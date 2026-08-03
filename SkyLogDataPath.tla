------------------------------ MODULE SkyLogDataPath -----------------------------
\* Data-path model for paper §4.2.1--§4.2.3.
\* Producers may concurrently use old {O} and duped {O,N} configurations.
\* Payload writes to O and N are independent; only the metadata stream orders
\* mirror reads.  A single crash/restart is sufficient to model duplicate
\* metadata caused by resuming from a checkpoint.

EXTENDS Naturals, Sequences, TLC

CONSTANTS Producers, Records

O == "O"
N == "N"
NoRecord == "None"

Targets(view) == IF view = "old" THEN {O} ELSE {O, N}

VARIABLES producerView, recordView, recordOwner, producerActive,
          payloadO, payloadN, homePos, mirrorPos, nextHome, nextMirror,
          metaLog, repAlive, repCursor, checkpoint, repCrashUsed,
          mirrorCursor, mirrorOutput, homeCursor, homeOutput

vars == << producerView, recordView, recordOwner, producerActive,
           payloadO, payloadN, homePos, mirrorPos, nextHome, nextMirror,
           metaLog, repAlive, repCursor, checkpoint, repCrashUsed,
           mirrorCursor, mirrorOutput, homeCursor, homeOutput >>

Issued == {r \in Records : recordView[r] # "none"}
MetaSet == {metaLog[i] : i \in 1..Len(metaLog)}
MirrorDelivered == {mirrorOutput[i] : i \in 1..Len(mirrorOutput)}
HomeDelivered == {homeOutput[i] : i \in 1..Len(homeOutput)}

HomeRecordAt(i) == CHOOSE r \in Records : homePos[r] = i
IndexOf(seq, r) == CHOOSE i \in 1..Len(seq) : seq[i] = r

Init ==
  /\ producerView = [p \in Producers |-> "old"]
  /\ recordView = [r \in Records |-> "none"]
  /\ recordOwner = [r \in Records |-> NoRecord]
  /\ producerActive = [r \in Records |-> FALSE]
  /\ payloadO = {}
  /\ payloadN = {}
  /\ homePos = [r \in Records |-> 0]
  /\ mirrorPos = [r \in Records |-> 0]
  /\ nextHome = 1
  /\ nextMirror = 1
  /\ metaLog = << >>
  /\ repAlive = TRUE
  /\ repCursor = 0
  /\ checkpoint = 0
  /\ repCrashUsed = FALSE
  /\ mirrorCursor = 0
  /\ mirrorOutput = << >>
  /\ homeCursor = 0
  /\ homeOutput = << >>

\* Fuzzy reconfiguration lets a producer independently change from the old
\* configuration to the duped configuration; both views coexist afterwards.
SwitchProducer(p) ==
  /\ p \in Producers
  /\ producerView[p] = "old"
  /\ producerView' = [producerView EXCEPT ![p] = "duped"]
  /\ UNCHANGED << recordView, recordOwner, producerActive,
                 payloadO, payloadN, homePos, mirrorPos, nextHome, nextMirror,
                 metaLog, repAlive, repCursor, checkpoint, repCrashUsed,
                 mirrorCursor, mirrorOutput, homeCursor, homeOutput >>

\* Each record id is unique.  recordView snapshots the configuration at issue.
Issue(p, r) ==
  /\ p \in Producers /\ r \in Records
  /\ recordView[r] = "none"
  /\ recordView' = [recordView EXCEPT ![r] = producerView[p]]
  /\ recordOwner' = [recordOwner EXCEPT ![r] = p]
  /\ producerActive' = [producerActive EXCEPT ![r] = TRUE]
  /\ UNCHANGED << producerView,
                 payloadO, payloadN, homePos, mirrorPos, nextHome, nextMirror,
                 metaLog, repAlive, repCursor, checkpoint, repCrashUsed,
                 mirrorCursor, mirrorOutput, homeCursor, homeOutput >>

\* These two actions deliberately have no ordering constraint.  Thus N can
\* physically store payloads in a different order from O, or only one write can
\* complete if the producer fails between them.
PersistAtHome(r) ==
  /\ r \in Records
  /\ producerActive[r]
  /\ O \in Targets(recordView[r])
  /\ r \notin payloadO
  /\ payloadO' = payloadO \cup {r}
  /\ homePos' = [homePos EXCEPT ![r] = nextHome]
  /\ nextHome' = nextHome + 1
  /\ UNCHANGED << producerView, recordView, recordOwner, producerActive,
                 payloadN, mirrorPos, nextMirror,
                 metaLog, repAlive, repCursor, checkpoint, repCrashUsed,
                 mirrorCursor, mirrorOutput, homeCursor, homeOutput >>

PersistAtMirror(r) ==
  /\ r \in Records
  /\ producerActive[r]
  /\ N \in Targets(recordView[r])
  /\ r \notin payloadN
  /\ payloadN' = payloadN \cup {r}
  /\ mirrorPos' = [mirrorPos EXCEPT ![r] = nextMirror]
  /\ nextMirror' = nextMirror + 1
  /\ UNCHANGED << producerView, recordView, recordOwner, producerActive,
                 payloadO, homePos, nextHome,
                 metaLog, repAlive, repCursor, checkpoint, repCrashUsed,
                 mirrorCursor, mirrorOutput, homeCursor, homeOutput >>

\* A producer may fail after writing nowhere, only O, only N, or both.
FailProducer(r) ==
  /\ r \in Records
  /\ producerActive[r]
  /\ producerActive' = [producerActive EXCEPT ![r] = FALSE]
  /\ UNCHANGED << producerView, recordView, recordOwner,
                 payloadO, payloadN, homePos, mirrorPos, nextHome, nextMirror,
                 metaLog, repAlive, repCursor, checkpoint, repCrashUsed,
                 mirrorCursor, mirrorOutput, homeCursor, homeOutput >>

\* §4.2.1: the replicator reads home records in home order and writes their
\* record ids to N's separate meta-stream.  Metadata is never generated before
\* the corresponding home payload has become durable.
SendMetadata ==
  /\ repAlive
  /\ repCursor < nextHome - 1
  /\ LET r == HomeRecordAt(repCursor + 1) IN
       /\ metaLog' = Append(metaLog, r)
       /\ repCursor' = repCursor + 1
  /\ UNCHANGED << producerView, recordView, recordOwner, producerActive,
                 payloadO, payloadN, homePos, mirrorPos, nextHome, nextMirror,
                 repAlive, checkpoint, repCrashUsed,
                 mirrorCursor, mirrorOutput, homeCursor, homeOutput >>

CheckpointReplicator ==
  /\ repAlive
  /\ checkpoint < repCursor
  /\ checkpoint' = repCursor
  /\ UNCHANGED << producerView, recordView, recordOwner, producerActive,
                 payloadO, payloadN, homePos, mirrorPos, nextHome, nextMirror,
                 metaLog, repAlive, repCursor, repCrashUsed,
                 mirrorCursor, mirrorOutput, homeCursor, homeOutput >>

\* §4.2.3: restart from the last checkpoint.  Any metadata sent after that
\* checkpoint is sent again, so duplicate meta-stream entries are intentional.
CrashReplicator ==
  /\ repAlive
  /\ ~repCrashUsed
  /\ repAlive' = FALSE
  /\ repCrashUsed' = TRUE
  /\ UNCHANGED << producerView, recordView, recordOwner, producerActive,
                 payloadO, payloadN, homePos, mirrorPos, nextHome, nextMirror,
                 metaLog, repCursor, checkpoint,
                 mirrorCursor, mirrorOutput, homeCursor, homeOutput >>

RestartReplicator ==
  /\ ~repAlive
  /\ repAlive' = TRUE
  /\ repCursor' = checkpoint
  /\ UNCHANGED << producerView, recordView, recordOwner, producerActive,
                 payloadO, payloadN, homePos, mirrorPos, nextHome, nextMirror,
                 metaLog, checkpoint, repCrashUsed,
                 mirrorCursor, mirrorOutput, homeCursor, homeOutput >>

\* Old-cloud reader: directly consume the home sequence in home order.
ReadAtHome ==
  /\ homeCursor < nextHome - 1
  /\ LET r == HomeRecordAt(homeCursor + 1) IN
       /\ homeOutput' = Append(homeOutput, r)
       /\ homeCursor' = homeCursor + 1
  /\ UNCHANGED << producerView, recordView, recordOwner, producerActive,
                 payloadO, payloadN, homePos, mirrorPos, nextHome, nextMirror,
                 metaLog, repAlive, repCursor, checkpoint, repCrashUsed,
                 mirrorCursor, mirrorOutput >>

\* New-cloud reader follows N's metadata, not N's physical payload order.
ReadFromMirror ==
  /\ mirrorCursor < Len(metaLog)
  /\ LET r == metaLog[mirrorCursor + 1] IN
       /\ r \in payloadN
       /\ r \notin MirrorDelivered
       /\ mirrorOutput' = Append(mirrorOutput, r)
       /\ mirrorCursor' = mirrorCursor + 1
  /\ UNCHANGED << producerView, recordView, recordOwner, producerActive,
                 payloadO, payloadN, homePos, mirrorPos, nextHome, nextMirror,
                 metaLog, repAlive, repCursor, checkpoint, repCrashUsed,
                 homeCursor, homeOutput >>

\* §4.2.3: if metadata arrives before N's data, model timeout + fetch from O.
ReadFromHomeFallback ==
  /\ mirrorCursor < Len(metaLog)
  /\ LET r == metaLog[mirrorCursor + 1] IN
       /\ r \notin payloadN
       /\ r \in payloadO
       /\ r \notin MirrorDelivered
       /\ mirrorOutput' = Append(mirrorOutput, r)
       /\ mirrorCursor' = mirrorCursor + 1
  /\ UNCHANGED << producerView, recordView, recordOwner, producerActive,
                 payloadO, payloadN, homePos, mirrorPos, nextHome, nextMirror,
                 metaLog, repAlive, repCursor, checkpoint, repCrashUsed,
                 homeCursor, homeOutput >>

\* Duplicate metadata is consumed but never delivered twice.
FilterDuplicateMetadata ==
  /\ mirrorCursor < Len(metaLog)
  /\ metaLog[mirrorCursor + 1] \in MirrorDelivered
  /\ mirrorCursor' = mirrorCursor + 1
  /\ UNCHANGED << producerView, recordView, recordOwner, producerActive,
                 payloadO, payloadN, homePos, mirrorPos, nextHome, nextMirror,
                 metaLog, repAlive, repCursor, checkpoint, repCrashUsed,
                 mirrorOutput, homeCursor, homeOutput >>

Next ==
  \/ \E p \in Producers : SwitchProducer(p)
  \/ \E p \in Producers, r \in Records : Issue(p, r)
  \/ \E r \in Records : PersistAtHome(r)
  \/ \E r \in Records : PersistAtMirror(r)
  \/ \E r \in Records : FailProducer(r)
  \/ SendMetadata
  \/ CheckpointReplicator
  \/ CrashReplicator
  \/ RestartReplicator
  \/ ReadAtHome
  \/ ReadFromMirror
  \/ ReadFromHomeFallback
  \/ FilterDuplicateMetadata

TypeOK ==
  /\ producerView \in [Producers -> {"old", "duped"}]
  /\ recordView \in [Records -> {"none", "old", "duped"}]
  /\ recordOwner \in [Records -> (Producers \cup {NoRecord})]
  /\ producerActive \in [Records -> BOOLEAN]
  /\ payloadO \subseteq Records
  /\ payloadN \subseteq Records
  /\ homePos \in [Records -> Nat]
  /\ mirrorPos \in [Records -> Nat]
  /\ nextHome \in Nat /\ nextMirror \in Nat
  /\ metaLog \in Seq(Records)
  /\ repAlive \in BOOLEAN
  /\ repCursor \in Nat /\ checkpoint \in Nat /\ repCrashUsed \in BOOLEAN
  /\ mirrorCursor \in Nat /\ mirrorOutput \in Seq(Records)
  /\ homeCursor \in Nat /\ homeOutput \in Seq(Records)

\* Metadata can name only a record durable in O.  A payload written only to N
\* therefore remains an orphan and cannot be read through the logical log.
MetadataAfterHomeDurable ==
  \A i \in 1..Len(metaLog) : metaLog[i] \in payloadO

NoMirrorOrphanDelivered == MirrorDelivered \subseteq payloadO

NoMirrorDuplicateDelivered ==
  \A i \in 1..Len(mirrorOutput) : \A j \in 1..Len(mirrorOutput) :
    i # j => mirrorOutput[i] # mirrorOutput[j]

NoHomeDuplicateDelivered ==
  \A i \in 1..Len(homeOutput) : \A j \in 1..Len(homeOutput) :
    i # j => homeOutput[i] # homeOutput[j]

\* This is the §4.2 same-order property: the N reader's output is ordered by
\* O's positions even when mirrorPos has an unrelated physical ordering.
MirrorFollowsHomeOrder ==
  \A i \in 1..Len(mirrorOutput) : \A j \in 1..Len(mirrorOutput) :
    i < j => homePos[mirrorOutput[i]] < homePos[mirrorOutput[j]]

OldAndNewReadersAgree ==
  \A r \in (MirrorDelivered \cap HomeDelivered) :
    \A s \in (MirrorDelivered \cap HomeDelivered) :
      r # s =>
        (IndexOf(mirrorOutput, r) < IndexOf(mirrorOutput, s)) =
        (IndexOf(homeOutput, r) < IndexOf(homeOutput, s))

\* With at most one crash, fairness makes the restarted replicator and the
\* metadata-driven reader drain all durable home records.
Fairness ==
  /\ WF_vars(RestartReplicator)
  /\ WF_vars(SendMetadata)
  /\ WF_vars(ReadAtHome)
  /\ WF_vars(ReadFromMirror)
  /\ WF_vars(ReadFromHomeFallback)
  /\ WF_vars(FilterDuplicateMetadata)

MetadataLiveness ==
  \A r \in Records : (r \in payloadO) ~> (r \in MetaSet)

MirrorReaderLiveness ==
  \A r \in Records : (r \in MetaSet) ~> (r \in MirrorDelivered)

Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================
