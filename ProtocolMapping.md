# SkyLog paper-to-model traceability

TLC verifies a finite instance of a TLA+ model, not the paper directly.  This
document records which paper behavior belongs to each of the three current
models, the exact TLC configuration that checks it, and the abstractions that
connect the models.

## Model layout

| Case | TLA+ model | TLC configurations | Reader behavior covered |
| --- | --- | --- | --- |
| 1. Data path | `SkyLogDataPath.tla` | `DataPath.cfg`, `DataPathLiveness.cfg` | Concrete home and mirror readers: metadata ordering, fallback to home, and duplicate filtering. |
| 2. Home unchanged | `SkyLogHomeUnchanged.tla` | `HomeUnchanged.cfg` | A bounded fuzzy-reconfiguration state machine and progress check; it has no reader or cached mapping. |
| 3. Home changed | `SkyLogHomeChanged.tla` | `HomeChanged.cfg` | Dup-then-switch plus the appendix consumer: read O to the marker, refresh the mapping, scan N with duplicate suppression, and assign compact logical positions. |

## 1. Data path: payload, metadata, and readers

Model: `SkyLogDataPath.tla`.

| Paper behavior | TLA+ representation | TLC check |
| --- | --- | --- |
| §4.2.1: clients disseminate a payload to every log in their cached configuration | `producerView`, `recordView`, `PersistAtHome`, and `PersistAtMirror` | `DataPath.cfg` explores old and duped views with independent physical writes. |
| The home establishes logical order | `homePos` and `nextHome` | `MirrorFollowsHomeOrder`, `OldAndNewReadersAgree`. |
| The order-replicator writes home record IDs to a separate mirror meta-stream | `SendMetadata`, `repCursor`, and `metaLog` | `MetadataAfterHomeDurable`; `MetadataLiveness` in `DataPathLiveness.cfg`. |
| A mirror reader uses metadata rather than physical mirror order | `ReadFromMirror` | `MirrorFollowsHomeOrder` and `NoMirrorDuplicateDelivered`. |
| Metadata may arrive before the corresponding mirror payload | `ReadFromHomeFallback` | `MirrorReaderLiveness` in `DataPathLiveness.cfg`. |
| Producer failure can leave an orphaned mirror payload | `FailProducer` after `PersistAtMirror` | `NoMirrorOrphanDelivered`. |
| Replicator restart can resend metadata | `CheckpointReplicator`, `CrashReplicator`, `RestartReplicator`, and `FilterDuplicateMetadata` | no duplicate mirror delivery. |

## 2. Home unchanged: fuzzy reconfiguration

Model: `SkyLogHomeUnchanged.tla`, a dedicated §4.3.1 state machine.

| Paper behavior | TLA+ representation | TLC check |
| --- | --- | --- |
| §4.3.1: record a proposed configuration before a mapping update | `Begin` changes only `proposal` | exhaustive interleavings in `HomeUnchanged.cfg`. The persistent configuration-store mapping is not represented. |
| A client drains its old-view append before switching | `SwitchClient(c)` requires `NoOutstanding(c)` | checked only with one outstanding request slot per client; this is not the paper's arbitrary-pipeline drain rule. |
| Old and proposed client views coexist | `clientCfg`, `issueCfg`, and delayed `Deliver(c)` | all client switching and request-delivery orders are explored. |
| Controller waits for every acknowledgment or lease expiry | `AllClientsDone` guards `FinishFuzzy` | `Progress` and acknowledged-append state predicates. |
| Every configuration retains home `O` | `ConfigHomes("old")` and `ConfigHomes("duped")` include `O` | `FuzzyHomeSafety` and `MappingVisibility`. |
| Mapping changes at `p = tail(O)` and the new configuration starts at `p+1` | `FinishFuzzy` retains only `cutover = nextO - 1` | omitted as a configuration-store behavior. No consumer holds or refreshes a cached mapping, so this is not a falsifiable stale-reader invariant. |

## 3. Home changed: dup-then-switch

Model: `SkyLogHomeChanged.tla`, a dedicated §4.3.2 state machine.

| Paper behavior | TLA+ representation | TLC check |
| --- | --- | --- |
| §4.3.2 begins by adding new home `N` as a mirror | each live client enters `"duped"`, whose targets are `{O, N}` | `HomeMoveRequiresCompletedDup`. |
| Controller completes the staged fuzzy dup only after acknowledgment or expiry | `AllClientsDone` guards `FinishDup` | `HomeMoveRequiresCompletedDup`. |
| Insert an old-home marker and call its position `p` | `PlaceMarker` reserves `nextO` as `cutover`, before the final proposal | the marker is a control-plane boundary, not an application record. |
| Propose `<N>` only after the marker and use fresh client responses | `ProposeFinal` enters `"finalizing"` and resets every `clientAck`; `MoveClientToFinal` drains `<O,N>` requests before acknowledging | all second-round client-switch interleavings are explored. |
| Install `p+1... -> <N>` only after every fresh acknowledgment or lease expiry | `AllClientsDone` guards `InstallHomeMove` | `FinalInstallRequiresClientSwitch`. The persistent mapping value itself is abstracted by `installed` and `cutover`. |
| A client that drains old requests can no longer issue an old-only request after it joins the dup | `SwitchClient`, `issueCfg`, and `ConfigHomes` | `MappingVisibility`. |
| An expired client cannot make a delayed old-only append visible after the cutover | `DropLateCompletion` suppresses its completion | `NoOldOnlyAcknowledgmentAfterCutover` and `MappingVisibility`. |
| The consumer reads O until it observes the marker at `p`, then waits for the installed `p+1 -> N` mapping | `ReadFromOldHome`, `CrossHomeBoundary`, `readerOPos`, and `readerSource` | `ReaderCrossesOnlyAtInstalledBoundary`. |
| The consumer scans N from its beginning and discards records already returned from O | `readerNPos`, `readerSeen`, and `SkipSeenAtNewHome` | `ReaderNoDuplicateDelivery`. |
| Each unseen N record is returned at `q`, beginning at `p+1` | `readerQ`, `readerPos`, and `ReadUnseenFromNewHome` | `ReaderReturnsLogicalStream`. |
| An acknowledged record is eventually returned by the boundary consumer | the four reader actions under weak fairness | `ReaderLiveness`. |
| Logical order remains unique and every acknowledged append remains visible at the marker-implied home | `logicalPos`, `posO`, `posN`, and `cutover` | `UniqueLogicalOrder`, `MappingVisibility`, `AcknowledgedDurable`. |

## Cross-model contract

The models are intentionally not one product state machine.

- `SkyLogDataPath.tla` proves metadata-driven order for a single mirror reader
  before any home move: metadata follows O, mirror payload order is irrelevant,
  fallback is safe, and duplicate *metadata* is filtered.
- `SkyLogHomeUnchanged.tla` does not contain a reconfiguration-specific reader;
  because O remains home, its consumer remains the fixed-home data-path case.
- `SkyLogHomeChanged.tla` contains the appendix's boundary consumer and checks
  source switching, duplicate suppression, compact positions, and liveness.

`SkyLogHomeChanged.tla` models the marker as O-side control state rather than
as an application record, and `CrossHomeBoundary` represents observing that
marker and fetching the installed mapping. `SkyLogDataPath.tla`'s
`FilterDuplicateMetadata` is separate: it concerns a replicator restart that
repeats entries in one meta-stream, whereas `SkipSeenAtNewHome` implements the
appendix's duplicate-record filtering across O and N.

The independent writes in `SkyLogDataPath.tla` still allow O and a mirror to
assign different physical orders. The home-move model abstracts dissemination
to `{O,N}` as one atomic completion, so its boundary-consumer result is not yet
an end-to-end composition proof with metadata replication.

Therefore a future product model must still compose metadata replication and
its independent physical-write ordering with this boundary consumer before
making an end-to-end reader-safety claim.

## Deliberate abstractions

- The persistent configuration store and its mapping value are not modeled.
  `proposal` and `cutover` are control-state scaffolding, not a store model.
- Underlying cloud logs are append-only and do not offer a seal operation.
- Network delay is arbitrary, but delivery to all destinations in an
  issue-time configuration is one atomic completion in the reconfiguration
  models. Thus they do not model independent acknowledgements or the relative
  physical orders at O and N; synchronous acknowledgement in the paper must
  not be read as this atomic-step abstraction.
- Leases are abstract `live`/`expired` states. Expiry is absorbing: an expired
  client cannot refetch the mapping, rejoin, or obtain a new lease, although
  the paper permits those behaviours.
- There are no application records before `Begin`; the marker can therefore
  create a non-application slot at `p`, which the reader's output skips.
- Each client has exactly one outstanding request slot. Consequently, the
  drain guard is not tested against more than one pending request per client.
- The home-changed consumer refreshes its mapping at the marker; arbitrary
  stale mappings and the §4.3.1 stop case remain omitted.
- The order replicator's stop-at-O/start-at-N protocol, including its order
  relative to the marker, is omitted. The data-path replicator restart models
  only a restart in O's meta-stream and is not a substitute.
- The data path uses one mirror and permits one replicator crash/restart per
  bounded execution.  It does not model multiple mirrors.
- Controller recovery (§4.3.3), concurrent reconfigurations, and cloud
  outages remain out of scope.

## Review procedure

1. Check every row against the paper before changing its model.
2. Require any new action, guard, or invariant to add or update a row here.
3. Run the three safety configurations, plus `DataPathLiveness.cfg`.
4. Classify a counterexample as a protocol flaw, translation flaw, or omitted
   assumption before changing the model or its property.
