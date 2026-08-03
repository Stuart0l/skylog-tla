-------------------------- MODULE SkyLogHomeUnchanged ----------------------------
\* An abstraction of SkyLog paper §4.3.1 (fuzzy reconfiguration).
\* It models delayed completion of an already-issued append. A completion to a
\* duped configuration updates O and N atomically in this abstraction, so it
\* does not represent independent acknowledgements or their relative physical
\* order. The cloud logs themselves do not reject stale requests; stale
\* successful completions are suppressed by the client library after expiry.

EXTENDS Naturals, TLC

CONSTANTS Clients, Records

O == "O"
N == "N"
NoRecord == "None"

\* The proposed configuration adds N as a mirror; O remains home throughout.
ConfigHomes(label) ==
  IF label = "old" THEN {O}
  ELSE {O, N}

VARIABLES phase, proposal, installed, cutover,
          clientCfg, clientAck, lease,
          pending, issueCfg, reqState, issued, appAcked, discarded,
          posO, posN, logicalPos, nextO, nextN

vars == << phase, proposal, installed, cutover,
           clientCfg, clientAck, lease,
           pending, issueCfg, reqState, issued, appAcked, discarded,
           posO, posN, logicalPos, nextO, nextN >>

NoOutstanding(c) == reqState[c] = "idle"
AllClientsDone == \A c \in Clients : clientAck[c] \/ lease[c] = "expired"

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

\* Recording the proposal does not change the marker state.
Begin ==
  /\ phase = "idle"
  /\ phase' = "fuzzy"
  /\ proposal' = "duped"
  /\ UNCHANGED << installed, cutover,
                 clientCfg, clientAck, lease,
                 pending, issueCfg, reqState, issued, appAcked, discarded,
                 posO, posN, logicalPos, nextO, nextN >>

\* A client may issue only under a live session and its cached configuration.
Issue(c, r) ==
  /\ c \in Clients /\ r \in Records
  /\ phase \in {"fuzzy", "done"}
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
                 posO, posN, logicalPos, nextO, nextN >>

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
        ![pending[c]] = nextO]
  /\ nextO' = IF O \in ConfigHomes(issueCfg[c]) THEN nextO + 1 ELSE nextO
  /\ nextN' = IF N \in ConfigHomes(issueCfg[c]) THEN nextN + 1 ELSE nextN
  /\ reqState' = [reqState EXCEPT ![c] = "durable"]
  /\ UNCHANGED << phase, proposal, installed, cutover,
                 clientCfg, clientAck, lease,
                 pending, issueCfg, issued, appAcked, discarded >>

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
                 posO, posN, logicalPos, nextO, nextN >>

DropLateCompletion(c) ==
  /\ c \in Clients
  /\ reqState[c] = "durable"
  /\ lease[c] = "expired"
  /\ discarded' = discarded \cup {pending[c]}
  /\ pending' = [pending EXCEPT ![c] = NoRecord]
  /\ reqState' = [reqState EXCEPT ![c] = "idle"]
  /\ UNCHANGED << phase, proposal, installed, cutover,
                 clientCfg, clientAck, lease, issueCfg, issued, appAcked,
                 posO, posN, logicalPos, nextO, nextN >>

\* Paper §4.3.1: drain every append from the prior configuration before
\* acknowledging the new configuration.
SwitchClient(c) ==
  /\ c \in Clients
  /\ phase = "fuzzy"
  /\ lease[c] = "live"
  /\ clientCfg[c] = "old"
  /\ NoOutstanding(c)
  /\ clientCfg' = [clientCfg EXCEPT ![c] = "duped"]
  /\ clientAck' = [clientAck EXCEPT ![c] = TRUE]
  /\ UNCHANGED << phase, proposal, installed, cutover,
                 lease, pending, issueCfg, reqState, issued, appAcked, discarded,
                 posO, posN, logicalPos, nextO, nextN >>

\* Expiry makes a disconnected client unable to issue more old-view requests.
Expire(c) ==
  /\ c \in Clients
  /\ phase # "idle"
  /\ lease[c] = "live"
  /\ lease' = [lease EXCEPT ![c] = "expired"]
  /\ UNCHANGED << phase, proposal, installed, cutover,
                 clientCfg, clientAck,
                 pending, issueCfg, reqState, issued, appAcked, discarded,
                 posO, posN, logicalPos, nextO, nextN >>

\* §4.3.1 completion: home O remains authoritative before and after p.
FinishFuzzy ==
  /\ phase = "fuzzy"
  /\ AllClientsDone
  /\ phase' = "done"
  /\ proposal' = "none"
  /\ installed' = TRUE
  /\ cutover' = nextO - 1
  /\ UNCHANGED << clientCfg, clientAck, lease,
                 pending, issueCfg, reqState, issued, appAcked, discarded,
                 posO, posN, logicalPos, nextO, nextN >>

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
  \/ FinishFuzzy
  \/ Done

TypeOK ==
  /\ phase \in {"idle", "fuzzy", "duped", "done"}
  /\ proposal \in {"none", "duped", "final"}
  /\ installed \in BOOLEAN
  /\ cutover \in Nat
  /\ clientCfg \in [Clients -> {"old", "duped"}]
  /\ clientAck \in [Clients -> BOOLEAN]
  /\ lease \in [Clients -> {"live", "expired"}]
  /\ pending \in [Clients -> (Records \cup {NoRecord})]
  /\ issueCfg \in [Clients -> {"old", "duped"}]
  /\ reqState \in [Clients -> {"idle", "inFlight", "durable"}]
  /\ issued \subseteq Records
  /\ appAcked \subseteq issued
  /\ discarded \subseteq issued
  /\ posO \in [Records -> Nat]
  /\ posN \in [Records -> Nat]
  /\ logicalPos \in [Records -> Nat]
  /\ nextO \in Nat /\ nextN \in Nat

\* Every result returned to the application has reached at least one cloud log.
AcknowledgedDurable ==
  \A r \in appAcked : posO[r] > 0 \/ posN[r] > 0

\* For §4.3.1, O is present in every configuration and is the source of truth.
FuzzyHomeSafety ==
  \A r \in appAcked : posO[r] > 0

\* During fuzzy reconfiguration O remains the home for every acknowledged
\* append. This is a state predicate, not a reader simulation.
MappingVisibility ==
  \A r \in appAcked :
    /\ logicalPos[r] > 0
    /\ posO[r] > 0

UniqueLogicalOrder ==
  \A r \in appAcked : \A s \in appAcked :
    r # s => logicalPos[r] # logicalPos[s]

\* Under weak fairness, a started reconfiguration cannot remain fuzzy forever:
\* active clients switch or expire, and the controller then completes it.
Fairness ==
  /\ \A c \in Clients : WF_vars(SwitchClient(c))
  /\ \A c \in Clients : WF_vars(Expire(c))
  /\ \A c \in Clients : WF_vars(Deliver(c))
  /\ \A c \in Clients : WF_vars(ReportSuccess(c))
  /\ \A c \in Clients : WF_vars(DropLateCompletion(c))
  /\ WF_vars(FinishFuzzy)

Progress == (phase = "fuzzy") ~> (phase = "done")

Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================
