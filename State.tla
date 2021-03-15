------ MODULE State ---------------------------------------------------------

VARIABLES st, msg

St == {"A", "B", "C"}
Msg == {"NULL", "a", "b", "c"}

TypeInv ==
  /\ st \in St
  /\ msg \in Msg

Init ==
  /\ st = "A"
  /\ msg \in Msg

Next ==
  \/ st = "A" /\ msg = "a"    /\ st' = "A"
  \/ st = "A" /\ msg = "b"    /\ st' = "B"
  \/ st = "A" /\ msg = "c"    /\ st' = "C"
  \/ st = "A" /\ msg = "NULL" /\ UNCHANGED st
  \/ st = "B"                 /\ UNCHANGED st
  \/ st = "C"                 /\ UNCHANGED st

Env == msg' \in Msg

Spec == Init /\ [][Next /\ Env]_<<st, msg>>

-----------------------------------------------------------------------------

NullMsg == [][msg = "NULL" => UNCHANGED st]_<<st, msg>>
AtoB == [][st = "A" /\ msg = "b" => st' = "B"]_<<st, msg>>

=============================================================================
