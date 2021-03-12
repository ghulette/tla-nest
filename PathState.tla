------ MODULE PathState -----------------------------------------------------

VARIABLES st, msg, ready, input

St == {"A0", "A1", "A2", "A_End", "B", "C"}
Msg == {"a", "b", "c"}

SimMap(x) ==
  CASE x \in {"A0", "A1", "A2", "A_End"} -> "A"
    [] x = "B" -> "B"
    [] x = "C" -> "C"

TypeInv ==
  /\ st \in St
  /\ msg \in Msg \union {"NULL"}
  /\ ready \in BOOLEAN
  /\ input \in Msg

Init ==
  /\ st = "A0"
  /\ msg = "NULL"
  /\ TypeInv

Next ==
  \/ st = "A0" /\ ready /\ st' = "A1" /\ UNCHANGED msg
  \/ st = "A0" /\ ~ready /\ st' = "A2" /\ UNCHANGED msg
  \/ st = "A1" /\ input = "b" /\ st' = "A_End" /\ msg' = "b"
  \/ st = "A1" /\ input = "c" /\ st' = "A_End" /\ msg' = "c"
  \/ st = "A1" /\ input \notin {"b", "c"} /\ st' = "A2" /\ UNCHANGED msg
  \/ st = "A2" /\ st' = "A_End" /\ msg' = "a"
  \/ st = "A_End" /\ msg = "a" /\ st' = "A0" /\ msg' = "NULL"
  \/ st = "A_End" /\ msg = "b" /\ st' = "B" /\ msg' = "NULL"
  \/ st = "A_End" /\ msg = "c" /\ st' = "C" /\ msg' = "NULL"
  \/ st = "B" /\ UNCHANGED <<st, msg>>
  \/ st = "C" /\ UNCHANGED <<st, msg>>

Env ==
    /\ ready' \in BOOLEAN
    /\ input' \in Msg

Spec == Init /\ [][Next /\ Env]_<<st, msg, ready, input>>

-----------------------------------------------------------------------------
(* Refinement *)

State == INSTANCE State WITH st <- SimMap(st)

Refines == State!Spec

BCMsgNull == st \in {"B", "C"} => msg = "NULL"

=============================================================================
