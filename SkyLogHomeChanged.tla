--------------------------- MODULE SkyLogHomeChanged -----------------------------
\* An abstraction of SkyLog paper §4.3.2 (dup-then-switch).
\* It models delayed completion of an already-issued append. A completion to a
\* duped configuration updates O and N atomically in this abstraction, so it
\* does not represent independent acknowledgements or their relative physical
\* order. The cloud logs themselves do not reject stale requests; stale
\* successful completions are suppressed by the client library after expiry.

EXTENDS Naturals, Sequences, TLC

CONSTANTS Clients, Records

O == "O"
N == "N"
NoRecord == "None"

\* The staged configuration writes to both homes; final writes only to N.
ConfigHomes(label) ==
  IF label = "old" THEN {O}
  ELSE IF label = "duped" THEN {O, N}
  ELSE {N}

VARIABLES phase, proposal, installed, cutover,
          clientCfg, clientAck, lease,
          pending, issueCfg, reqState, issued, appAcked, discarded,
          posO, posN, logicalPos, nextO, nextN, nextLogical,
          readerSource, readerOPos, readerNPos, readerQ,
          readerSeen, readerOutput, readerPos

vars == << phase, proposal, installed, cutover,
           clientCfg, clientAck, lease,
           pending, issueCfg, reqState, issued, appAcked, discarded,
           posO, posN, logicalPos, nextO, nextN, nextLogical,
           readerSource, readerOPos, readerNPos, readerQ,
           readerSeen, readerOutput, readerPos >>

systemVars == << phase, proposal, installed, cutover,
                clientCfg, clientAck, lease,
                pending, issueCfg, reqState, issued, appAcked, discarded,
                posO, posN, logicalPos, nextO, nextN, nextLogical >>

readerVars == << readerSource, readerOPos, readerNPos, readerQ,
                readerSeen, readerOutput, readerPos >>

NoOutstanding(c) == reqState[c] = "idle"
AllClientsDone == \A c \in Clients : clientAck[c] \/ lease[c] = "expired"
ReaderDelivered == {readerOutput[i] : i \in 1..Len(readerOutput)}
OldRecordAt(i) == CHOOSE r \in Records : posO[r] = i
NewRecordAt(i) == CHOOSE r \in Records : posN[r] = i

Init ==
  /\ phase = "idle"
  /\ proposal = "none"
  /\ installed = FALSE
  /\ cutover = 0
  /\ clientCfg = [c \in Clients |-> "old"]
  /\ clientAck = [c \in Clients |-> FALSE]
  /\ lease = [c \in Clients |-> "live"]
  /\ pending = [c \in Clients |-> NoRecord]
  /\ issueCfg = [c \in Clients |-> "old"]
  /\ reqState = [c \in Clients |-> "idle"]
  /\ issued = {}
  /\ appAcked = {}
  /\ discarded = {}
  /\ posO = [r \in Records |-> 0]
  /\ posN = [r \in Records |-> 0]
  /\ logicalPos = [r \in Records |-> 0]
  /\ nextO = 1
  /\ nextN = 1
  /\ nextLogical = 1
  /\ readerSource = "O"
  /\ readerOPos = 1
  /\ readerNPos = 1
  /\ readerQ = 1
  /\ readerSeen = {}
  /\ readerOutput = << >>
  /\ readerPos = [r \in Records |-> 0]

\* Recording the proposal does not change the marker state.
Begin ==
  /\ phase = "idle"
  /\ phase' = "fuzzy"
  /\ proposal' = "duped"
  /\ UNCHANGED << installed, cutover,
                 clientCfg, clientAck, lease,
                 pending, issueCfg, reqState, issued, appAcked, discarded,
                 posO, posN, logicalPos, nextO, nextN, nextLogical,
                 readerVars >>

\* A client may issue only under a live session and its cached configuration.
Issue(c, r) ==
  /\ c \in Clients /\ r \in Records
  /\ phase \in {"fuzzy", "duped", "marker", "finalizing", "done"}
  /\ lease[c] = "live"
  /\ reqState[c] = "idle"
  /\ r \notin issued
  /\ pending' = [pending EXCEPT ![c] = r]
  /\ issueCfg' = [issueCfg EXCEPT ![c] = clientCfg[c]]
  /\ reqState' = [reqState EXCEPT ![c] = "inFlight"]
  /\ issued' = issued \cup {r}
  /\ UNCHANGED << phase, proposal, installed, cutover,
                 clientCfg, clientAck, lease,
                 appAcked, discarded,
                 posO, posN, logicalPos, nextO, nextN, nextLogical,
                 readerVars >>

\* Delivery is delayed. A request keeps issueCfg (the destination configuration
\* it had when issued), which permits delayed old-view requests. For a duped
\* request, both physical writes occur in this one abstract step.
Deliver(c) ==
  /\ c \in Clients
  /\ reqState[c] = "inFlight"
  /\ posO' = [posO EXCEPT
        ![pending[c]] = IF O \in ConfigHomes(issueCfg[c]) THEN nextO ELSE @]
  /\ posN' = [posN EXCEPT
        ![pending[c]] = IF N \in ConfigHomes(issueCfg[c]) THEN nextN ELSE @]
  /\ logicalPos' = [logicalPos EXCEPT
        ![pending[c]] = IF phase \in {"marker", "finalizing", "done"}
                         THEN IF N \in ConfigHomes(issueCfg[c])
                              THEN nextLogical
                              ELSE 0
                         ELSE nextO]
  /\ nextO' = IF O \in ConfigHomes(issueCfg[c]) THEN nextO + 1 ELSE nextO
  /\ nextN' = IF N \in ConfigHomes(issueCfg[c]) THEN nextN + 1 ELSE nextN
  /\ nextLogical' = IF phase \in {"marker", "finalizing", "done"}
                         /\ N \in ConfigHomes(issueCfg[c])
                    THEN nextLogical + 1
                    ELSE nextLogical
  /\ reqState' = [reqState EXCEPT ![c] = "durable"]
  /\ UNCHANGED << phase, proposal, installed, cutover,
                 clientCfg, clientAck, lease,
                 pending, issueCfg, issued, appAcked, discarded,
                 readerVars >>

\* A successful completion is returned only while the client's session remains
\* live.  This represents the paper's client-side late-acknowledgment check.
ReportSuccess(c) ==
  /\ c \in Clients
  /\ reqState[c] = "durable"
  /\ lease[c] = "live"
  /\ appAcked' = appAcked \cup {pending[c]}
  /\ pending' = [pending EXCEPT ![c] = NoRecord]
  /\ reqState' = [reqState EXCEPT ![c] = "idle"]
  /\ UNCHANGED << phase, proposal, installed, cutover,
                 clientCfg, clientAck, lease, issueCfg, issued, discarded,
                 posO, posN, logicalPos, nextO, nextN, nextLogical,
                 readerVars >>

DropLateCompletion(c) ==
  /\ c \in Clients
  /\ reqState[c] = "durable"
  /\ lease[c] = "expired"
  /\ discarded' = discarded \cup {pending[c]}
  /\ pending' = [pending EXCEPT ![c] = NoRecord]
  /\ reqState' = [reqState EXCEPT ![c] = "idle"]
  /\ UNCHANGED << phase, proposal, installed, cutover,
                 clientCfg, clientAck, lease, issueCfg, issued, appAcked,
                 posO, posN, logicalPos, nextO, nextN, nextLogical,
                 readerVars >>

\* Paper §4.3.1: drain every append from the prior configuration before
\* acknowledging the new configuration.
SwitchClient(c) ==
  /\ c \in Clients
  /\ phase = "fuzzy"
  /\ proposal = "duped"
  /\ lease[c] = "live"
  /\ clientCfg[c] = "old"
  /\ NoOutstanding(c)
  /\ clientCfg' = [clientCfg EXCEPT ![c] = "duped"]
  /\ clientAck' = [clientAck EXCEPT ![c] = TRUE]
  /\ UNCHANGED << phase, proposal, installed, cutover,
                 lease, pending, issueCfg, reqState, issued, appAcked, discarded,
                 posO, posN, logicalPos, nextO, nextN, nextLogical,
                 readerVars >>

\* Expiry makes a disconnected client unable to issue more old-view requests.
Expire(c) ==
  /\ c \in Clients
  /\ phase # "idle"
  /\ lease[c] = "live"
  /\ lease' = [lease EXCEPT ![c] = "expired"]
  /\ UNCHANGED << phase, proposal, installed, cutover,
                 clientCfg, clientAck,
                 pending, issueCfg, reqState, issued, appAcked, discarded,
                 posO, posN, logicalPos, nextO, nextN, nextLogical,
                 readerVars >>

\* §4.3.2 stage 1: the fuzzy dup has completed, but O remains the home.
FinishDup ==
  /\ phase = "fuzzy"
  /\ AllClientsDone
  /\ phase' = "duped"
  /\ proposal' = "none"
  /\ UNCHANGED << installed, cutover,
                 clientCfg, clientAck, lease,
                 pending, issueCfg, reqState, issued, appAcked, discarded,
                 posO, posN, logicalPos, nextO, nextN, nextLogical,
                 readerVars >>

\* §4.3.2 stage 2: append the O marker and retain its position as p.  The
\* marker is not an application record.  The persistent mapping itself is
\* abstracted by installed and cutover.
PlaceMarker ==
  /\ phase = "duped"
  /\ phase' = "marker"
  /\ cutover' = nextO
  /\ nextO' = nextO + 1
  /\ nextLogical' = nextO + 1
  /\ UNCHANGED << proposal, installed, clientCfg, clientAck, lease,
                 pending, issueCfg, reqState, issued, appAcked, discarded,
                 posO, posN, logicalPos, nextN, readerVars >>

\* After placing the marker, record the final <N> proposal and begin a fresh
\* acknowledgment epoch.  Acknowledgments from the initial dup cannot satisfy
\* this second wait.
ProposeFinal ==
  /\ phase = "marker"
  /\ phase' = "finalizing"
  /\ proposal' = "final"
  /\ clientAck' = [c \in Clients |-> FALSE]
  /\ UNCHANGED << installed, cutover, clientCfg, lease,
                 pending, issueCfg, reqState, issued, appAcked, discarded,
                 posO, posN, logicalPos, nextO, nextN, nextLogical,
                 readerVars >>

\* Each live client drains requests issued under <O,N>, switches to <N>, and
\* acknowledges the final proposal.  Expired clients are covered by the lease
\* side of AllClientsDone.
MoveClientToFinal(c) ==
  /\ c \in Clients
  /\ phase = "finalizing"
  /\ proposal = "final"
  /\ lease[c] = "live"
  /\ clientCfg[c] = "duped"
  /\ NoOutstanding(c)
  /\ clientCfg' = [clientCfg EXCEPT ![c] = "final"]
  /\ clientAck' = [clientAck EXCEPT ![c] = TRUE]
  /\ UNCHANGED << phase, proposal, installed, cutover,
                 lease,
                 pending, issueCfg, reqState, issued, appAcked, discarded,
                 posO, posN, logicalPos, nextO, nextN, nextLogical,
                 readerVars >>

\* Install p+1 -> <N> only after every client has acknowledged the second
\* proposal or its lease has expired.
InstallHomeMove ==
  /\ phase = "finalizing"
  /\ AllClientsDone
  /\ phase' = "done"
  /\ proposal' = "none"
  /\ installed' = TRUE
  /\ UNCHANGED << cutover, clientCfg, clientAck, lease,
                 pending, issueCfg, reqState, issued, appAcked, discarded,
                 posO, posN, logicalPos, nextO, nextN, nextLogical,
                 readerVars >>

\* Appendix: consume O until the marker at p. Every application record before
\* the marker is delivered at its O position and remembered for N-side dedup.
ReadFromOldHome ==
  /\ readerSource = "O"
  /\ readerOPos < nextO
  /\ (cutover = 0 \/ readerOPos < cutover)
  /\ LET r == OldRecordAt(readerOPos) IN
       /\ readerOutput' = Append(readerOutput, r)
       /\ readerPos' = [readerPos EXCEPT ![r] = posO[r]]
       /\ readerSeen' = readerSeen \cup {r}
       /\ readerOPos' = readerOPos + 1
  /\ UNCHANGED << systemVars, readerSource, readerNPos, readerQ >>

\* Seeing the marker triggers a mapping refresh. The consumer may cross the
\* boundary only after p+1 -> N has been installed, then it starts N at 1.
CrossHomeBoundary ==
  /\ readerSource = "O"
  /\ cutover > 0
  /\ readerOPos = cutover
  /\ installed
  /\ readerSource' = "N"
  /\ readerQ' = cutover + 1
  /\ UNCHANGED << systemVars, readerOPos, readerNPos,
                 readerSeen, readerOutput, readerPos >>

\* N contains records copied during the dup phase. Records already returned
\* from O are consumed physically but suppressed from the application stream.
SkipSeenAtNewHome ==
  /\ readerSource = "N"
  /\ readerNPos < nextN
  /\ LET r == NewRecordAt(readerNPos) IN
       /\ r \in readerSeen
       /\ readerNPos' = readerNPos + 1
  /\ UNCHANGED << systemVars, readerSource, readerOPos, readerQ,
                 readerSeen, readerOutput, readerPos >>

\* The first unseen N record is the next logical record after p. Subsequent
\* unseen records receive consecutive logical positions q, q+1, ... .
ReadUnseenFromNewHome ==
  /\ readerSource = "N"
  /\ readerNPos < nextN
  /\ LET r == NewRecordAt(readerNPos) IN
       /\ r \notin readerSeen
       /\ readerOutput' = Append(readerOutput, r)
       /\ readerPos' = [readerPos EXCEPT ![r] = readerQ]
       /\ readerNPos' = readerNPos + 1
       /\ readerQ' = readerQ + 1
  /\ UNCHANGED << systemVars, readerSource, readerOPos, readerSeen >>

\* The model represents one reconfiguration request.  A completed request may
\* quiesce; explicit stuttering prevents TLC from treating that terminal state
\* as a deadlock.
Done ==
  /\ phase = "done"
  /\ UNCHANGED vars

Next ==
  \/ Begin
  \/ \E c \in Clients, r \in Records : Issue(c, r)
  \/ \E c \in Clients : Deliver(c)
  \/ \E c \in Clients : ReportSuccess(c)
  \/ \E c \in Clients : DropLateCompletion(c)
  \/ \E c \in Clients : SwitchClient(c)
  \/ \E c \in Clients : Expire(c)
  \/ FinishDup
  \/ PlaceMarker
  \/ ProposeFinal
  \/ \E c \in Clients : MoveClientToFinal(c)
  \/ InstallHomeMove
  \/ ReadFromOldHome
  \/ CrossHomeBoundary
  \/ SkipSeenAtNewHome
  \/ ReadUnseenFromNewHome
  \/ Done

TypeOK ==
  /\ phase \in {"idle", "fuzzy", "duped", "marker", "finalizing", "done"}
  /\ proposal \in {"none", "duped", "final"}
  /\ installed \in BOOLEAN
  /\ cutover \in Nat
  /\ clientCfg \in [Clients -> {"old", "duped", "final"}]
  /\ clientAck \in [Clients -> BOOLEAN]
  /\ lease \in [Clients -> {"live", "expired"}]
  /\ pending \in [Clients -> (Records \cup {NoRecord})]
  /\ issueCfg \in [Clients -> {"old", "duped", "final"}]
  /\ reqState \in [Clients -> {"idle", "inFlight", "durable"}]
  /\ issued \subseteq Records
  /\ appAcked \subseteq issued
  /\ discarded \subseteq issued
  /\ posO \in [Records -> Nat]
  /\ posN \in [Records -> Nat]
  /\ logicalPos \in [Records -> Nat]
  /\ nextO \in Nat /\ nextN \in Nat /\ nextLogical \in Nat
  /\ readerSource \in {"O", "N"}
  /\ readerOPos \in Nat /\ readerNPos \in Nat /\ readerQ \in Nat
  /\ readerSeen \subseteq Records
  /\ readerOutput \in Seq(Records)
  /\ readerPos \in [Records -> Nat]

\* Every result returned to the application has reached at least one cloud log.
AcknowledgedDurable ==
  \A r \in appAcked : posO[r] > 0 \/ posN[r] > 0

\* This scalar predicate checks that every acknowledged append has a payload at
\* the home implied by the marker boundary. It is not a reader simulation.
MappingVisibility ==
  \A r \in appAcked :
    /\ logicalPos[r] > 0
    /\ IF cutover > 0 /\ logicalPos[r] > cutover
       THEN posN[r] > 0
       ELSE posO[r] > 0

UniqueLogicalOrder ==
  \A r \in appAcked : \A s \in appAcked :
    r # s => logicalPos[r] # logicalPos[s]

\* No active client remains on the O-only view once the controller is allowed
\* to choose the home-move marker.
HomeMoveRequiresCompletedDup ==
  phase \in {"duped", "marker", "finalizing", "done"} =>
    \A c \in Clients : lease[c] = "expired" \/ clientCfg[c] # "old"

\* Installing the final mapping requires a fresh response to the final
\* proposal from every live client; initial-dup acknowledgments were reset.
FinalInstallRequiresClientSwitch ==
  installed =>
    /\ phase = "done"
    /\ AllClientsDone
    /\ \A c \in Clients : lease[c] = "live" => clientCfg[c] = "final"

\* This is the central late-request safety obligation in the paper's sketch.
NoOldOnlyAcknowledgmentAfterCutover ==
  \A r \in appAcked :
    ~(cutover > 0 /\ posO[r] > cutover /\ posN[r] = 0)

\* The application never sees the same record twice while the N scan passes
\* over the duplicated prefix.
ReaderNoDuplicateDelivery ==
  \A i \in 1..Len(readerOutput) : \A j \in 1..Len(readerOutput) :
    i # j => readerOutput[i] # readerOutput[j]

\* Each delivered record carries its model logical position, and application
\* delivery remains strictly ordered across the marker (whose slot is skipped).
ReaderReturnsLogicalStream ==
  /\ \A i \in 1..Len(readerOutput) :
       readerPos[readerOutput[i]] = logicalPos[readerOutput[i]]
  /\ \A i \in 1..Len(readerOutput) : \A j \in 1..Len(readerOutput) :
       i < j => logicalPos[readerOutput[i]] < logicalPos[readerOutput[j]]

ReaderCrossesOnlyAtInstalledBoundary ==
  readerSource = "N" =>
    /\ installed
    /\ cutover > 0
    /\ readerOPos = cutover
    /\ readerQ >= cutover + 1

\* Under weak fairness, a started reconfiguration cannot remain fuzzy forever:
\* active clients switch or expire, and the controller then completes it.
Fairness ==
  /\ \A c \in Clients : WF_vars(SwitchClient(c))
  /\ \A c \in Clients : WF_vars(Expire(c))
  /\ \A c \in Clients : WF_vars(Deliver(c))
  /\ \A c \in Clients : WF_vars(ReportSuccess(c))
  /\ \A c \in Clients : WF_vars(DropLateCompletion(c))
  /\ WF_vars(FinishDup)
  /\ WF_vars(PlaceMarker)
  /\ WF_vars(ProposeFinal)
  /\ \A c \in Clients : WF_vars(MoveClientToFinal(c))
  /\ WF_vars(InstallHomeMove)
  /\ WF_vars(ReadFromOldHome)
  /\ WF_vars(CrossHomeBoundary)
  /\ WF_vars(SkipSeenAtNewHome)
  /\ WF_vars(ReadUnseenFromNewHome)

Progress ==
  /\ (phase = "fuzzy") ~> (phase = "duped")
  /\ (phase = "duped") ~> (phase = "marker")
  /\ (phase = "marker") ~> (phase = "finalizing")
  /\ (phase = "finalizing") ~> (phase = "done")

ReaderLiveness ==
  \A r \in Records :
    (installed /\ r \in appAcked) ~> (r \in ReaderDelivered)

Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================
