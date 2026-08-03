# SkyLog §4.3 TLA+ model

This repository model-checks selected SkyLog data-path and reconfiguration
state-machine properties from `nsdi27spring-paper499.pdf`. It does not model
the complete end-to-end reader protocol.

The three models share a clear boundary: `SkyLogDataPath.tla` owns payload,
metadata, and per-log reader behavior; the reconfiguration models own client
leases, staged configurations, and a marker boundary. This is a modelling boundary, not a composition
proof or a reader-source-selection result.

Read [ProtocolMapping.md](ProtocolMapping.md) first.  It maps every material
paper rule to a state transition or invariant, and names every deliberate
abstraction.

## Files

- `SkyLogDataPath.tla`: §4.2 payload dissemination, home-ordered metadata
  replication, mirror reading, fallback, and duplicate filtering.
- `SkyLogHomeUnchanged.tla`: §4.3.1 fuzzy-reconfiguration state machine. It
  checks bounded progress and staged-configuration bookkeeping; it has no consumer with
  a cached mapping, so it is not a reader-safety result.
- `SkyLogHomeChanged.tla`: §4.3.2 dup-then-switch state machine, including a
  marker boundary and acknowledged-append visibility. It does not model
  N-side deduplication, renumbering, or a consumer reading across that boundary.
- `DataPath.cfg`, `HomeUnchanged.cfg`, and `HomeChanged.cfg`: the exhaustive
  finite TLC configurations for those three models.
- `Mutation*.cfg`: intentionally broken variants that must produce TLC
  counterexamples in the home-changed model.
- `DataPathLiveness.cfg`: a one-record temporal check for metadata and
  mirror-reader progress under weak fairness.

## Run TLC

Install the official TLA+ tools and point `TLA_TOOLS_JAR` at `tla2tools.jar`.
Java 17 or later is required.

```sh
export TLA_TOOLS_JAR=/absolute/path/to/tla2tools.jar
./run-checks.sh
```

To run an individual check:

```sh
java -cp "$TLA_TOOLS_JAR" tlc2.TLC -workers auto -config HomeChanged.cfg SkyLogHomeChanged.tla
```

The good checks must pass.  Each `Mutation*.cfg` run must fail by violating
the named invariant; that demonstrates the properties are sensitive to the
rules that make the protocol safe.

The data-path safety configuration uses two producers and two records; its
liveness configuration uses one of each to keep temporal model checking
tractable. The reconfiguration checks use two clients and three records. Each
client has one outstanding request slot, so the drain discipline is checked
only at pipeline depth one; the paper's arbitrary-pending-request rule is not
covered.

## Meaning of a passing result

TLC exhaustively checks the finite instance in the configuration files: two
clients and three application records, with all allowed interleavings. It is
formal bounded model checking, not an unbounded proof. In particular, a
passing run does not establish the paper's post-cutover N-reader behavior:
discarding duplicate records and assigning their compact logical positions.
