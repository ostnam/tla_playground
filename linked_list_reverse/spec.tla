-------------------------------- MODULE spec --------------------------------
EXTENDS Naturals

CONSTANTS N
ASSUME N \in Nat

Len == 1..N
NIL == CHOOSE NIL : NIL \notin Len
Nodes == Len \union NIL
Succ == [ x \in Len |-> IF x + 1 \in Len THEN x+1 ELSE NIL ]

(*
--algorithm LinkedListReverse

variables
    prev = NIL;
    current = 1;
    next = NIL;
    NewSucc = Succ;
begin

loop:
    while current # NIL do
        next := NewSucc[current];
        NewSucc[current] := prev;
        prev := current;
        current := next;
    end while;

end algorithm
*)
\* BEGIN TRANSLATION (chksum(pcal) = "d53f0d2f" /\ chksum(tla) = "a8aa6dea")
VARIABLES prev, current, next, NewSucc, pc

vars == << prev, current, next, NewSucc, pc >>

Init == (* Global variables *)
        /\ prev = NIL
        /\ current = 1
        /\ next = NIL
        /\ NewSucc = Succ
        /\ pc = "loop"

loop == /\ pc = "loop"
        /\ IF current # NIL
              THEN /\ next' = NewSucc[current]
                   /\ NewSucc' = [NewSucc EXCEPT ![current] = prev]
                   /\ prev' = current
                   /\ current' = next'
                   /\ pc' = "loop"
              ELSE /\ pc' = "Done"
                   /\ UNCHANGED << prev, current, next, NewSucc >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == loop
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
IsReversed ==
  current = NIL => NewSucc = [ x \in Len |-> IF x-1 \in Len THEN x-1 ELSE NIL ]
=============================================================================
\* Modification History
\* Last modified Mon May 20 11:37:28 CEST 2024 by mansour
\* Created Mon May 20 10:40:28 CEST 2024 by ostnam
