------------------------------- MODULE benor -------------------------------
EXTENDS Integers, Sequences, FiniteSets
CONSTANT N, F, MAXROUND, INPUT
\* E.g., INPUT= <<0,1,1,1>> for N=4.
ASSUME F<N   \* F is upperbound on # of crash faults
Procs == 1..N
(*
--algorithm benor
{ variable p1Msg={}, p2Msg={};
  define{
    Phase1SentMessages(round) == {msg \in p1Msg:msg[2]=round}
    Phase2SentMessages(round) == {msg \in p2Msg:msg[2]=round}
    Phase1Value(round, val) == {msg \in p1Msg:msg[2]=round /\ msg[3]=val}
    Phase2Value(round, val) == {msg \in p2Msg:msg[2]=round /\ msg[3]=val}
    AnchoredValue(S) == {msg[3] : msg \in S}
  }

  fair process (p \in Procs)
  variable r=1, p1v=INPUT[self], p2v=-1, decided={};
  {
  S: while (r<= MAXROUND){
        p1Msg:=p1Msg \union {<<self, r, p1v>>};
        p2v:=-1;
  P1: await (Cardinality(Phase1SentMessages(r)) >= N - F);
      if (\E val \in {0,1}: 2*Cardinality(Phase1Value(r,val)) > N)
      p2v:= CHOOSE val \in AnchoredValue(Phase1SentMessages(r)): 2*Cardinality(Phase1Value(r,val)) > N;
      p2Msg:=p2Msg \union {<<self, r, p2v>>};
  P2: await (Cardinality(Phase2SentMessages(r)) >= N - F);
      if (\E val \in {0,1}: Cardinality(Phase2Value(r,val)) >= F+1){
        p1v:= CHOOSE val \in AnchoredValue(Phase2SentMessages(r)): val/=-1;
        decided:={p1v};}
      else if(\E val \in AnchoredValue(Phase2SentMessages(r)): val/=-1){
        p1v:= CHOOSE val \in AnchoredValue(Phase2SentMessages(r)): val/=-1;}
      else with (val \in {0,1})
        p1v:=val;
      r:=r+1;
     }
  }

} \* end algorithm
*)


\* BEGIN TRANSLATION - the hash of the PCal code: PCal-9155a06b820ac48cc65ace95a2beba6b
VARIABLES p1Msg, p2Msg, pc

(* define statement *)
Phase1SentMessages(round) == {msg \in p1Msg:msg[2]=round}
Phase2SentMessages(round) == {msg \in p2Msg:msg[2]=round}
Phase1Value(round, val) == {msg \in p1Msg:msg[2]=round /\ msg[3]=val}
Phase2Value(round, val) == {msg \in p2Msg:msg[2]=round /\ msg[3]=val}
AnchoredValue(S) == {msg[3] : msg \in S}

VARIABLES r, p1v, p2v, decided

vars == << p1Msg, p2Msg, pc, r, p1v, p2v, decided >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ p1Msg = {}
        /\ p2Msg = {}
        (* Process p *)
        /\ r = [self \in Procs |-> 1]
        /\ p1v = [self \in Procs |-> INPUT[self]]
        /\ p2v = [self \in Procs |-> -1]
        /\ decided = [self \in Procs |-> {}]
        /\ pc = [self \in ProcSet |-> "S"]

S(self) == /\ pc[self] = "S"
           /\ IF r[self]<= MAXROUND
                 THEN /\ p1Msg' = (p1Msg \union {<<self, r[self], p1v[self]>>})
                      /\ p2v' = [p2v EXCEPT ![self] = -1]
                      /\ pc' = [pc EXCEPT ![self] = "P1"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << p1Msg, p2v >>
           /\ UNCHANGED << p2Msg, r, p1v, decided >>

P1(self) == /\ pc[self] = "P1"
            /\ (Cardinality(Phase1SentMessages(r[self])) >= N - F)
            /\ IF \E val \in {0,1}: 2*Cardinality(Phase1Value(r[self],val)) > N
                  THEN /\ p2v' = [p2v EXCEPT ![self] = CHOOSE val \in AnchoredValue(Phase1SentMessages(r[self])): 2*Cardinality(Phase1Value(r[self],val)) > N]
                  ELSE /\ TRUE
                       /\ p2v' = p2v
            /\ p2Msg' = (p2Msg \union {<<self, r[self], p2v'[self]>>})
            /\ pc' = [pc EXCEPT ![self] = "P2"]
            /\ UNCHANGED << p1Msg, r, p1v, decided >>

P2(self) == /\ pc[self] = "P2"
            /\ (Cardinality(Phase2SentMessages(r[self])) >= N - F)
            /\ IF \E val \in {0,1}: Cardinality(Phase2Value(r[self],val)) >= F+1
                  THEN /\ p1v' = [p1v EXCEPT ![self] = CHOOSE val \in AnchoredValue(Phase2SentMessages(r[self])): val/=-1]
                       /\ decided' = [decided EXCEPT ![self] = {p1v'[self]}]
                  ELSE /\ IF \E val \in AnchoredValue(Phase2SentMessages(r[self])): val/=-1
                             THEN /\ p1v' = [p1v EXCEPT ![self] = CHOOSE val \in AnchoredValue(Phase2SentMessages(r[self])): val/=-1]
                             ELSE /\ \E val \in {0,1}:
                                       p1v' = [p1v EXCEPT ![self] = val]
                       /\ UNCHANGED decided
            /\ r' = [r EXCEPT ![self] = r[self]+1]
            /\ pc' = [pc EXCEPT ![self] = "S"]
            /\ UNCHANGED << p1Msg, p2Msg, p2v >>

p(self) == S(self) \/ P1(self) \/ P2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-181dfd3fb9f65b3750d1cf6773d5a8c6


Agreement == \A j,k \in Procs: Cardinality(decided[j])=1  /\ Cardinality(decided[k])=1 => decided[j]=decided[k]

MinorityReport == ~ \A j \in Procs: decided[j]={0}

Progress  == <> (\A j \in Procs: Cardinality(decided[j])>0)


\* Exclude failed processes

=========================================================
=============================================================================
\* Modification History
\* Last modified Thu Jul 02 17:35:32 EDT 2020 by DELL
\* Last modified Wed Jun 24 08:37:04 EDT 2020 by bekir
\* Created Wed Jun 24 07:53:22 EDT 2020 by bekir
