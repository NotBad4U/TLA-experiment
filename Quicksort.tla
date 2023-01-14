----------------------------- MODULE Quicksort -----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

(* TODO: use N in the generation of sequence *)
CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

VARIABLES seq, stack

Sorted(s) == \A i, j \in 1..(Len(s)-1) : i <= j => s[i] <= s[j]

IsPermOf(s1,s2) == s1 \in Permutations(s2)

vars == <<seq, stack>> 

TypeOk == /\ seq \in Seq(Nat)  \ {<< >>}
          /\ stack \in SUBSET {1..Len(seq)}

          
(*
    Split the sequence through the pivot and sort left and right and sort them.
    (1) All the element lower than the pivot go to the left
    (2) All the element higher than the pivot go to the right
    (3) The pivot doesn't move.
    Return the union of this two sorted sequence end the pivot
 *)                  
Partitions(s, p) ==
    LET elementsLessThanPivot == SelectSeq(s, LAMBDA v: v < s[p]) (* (1) *)
        elementsGreatherThanPivot == SelectSeq(s, LAMBDA v: v > s[p]) (* (2) *)
    IN
        elementsLessThanPivot \o <<s[p]>> \o elementsGreatherThanPivot (* <<s[p]>> is because of (3) *)

Init == /\ seq = <<5, 4, 1, 3, 6, 2 >>
        /\ stack = {<<1, Len(seq)>>}

Next == /\ stack # {}
        /\
            (* pop an unsorted interval from the sack -- we have only index *) 
            \E <<li, hi >> \in stack:
            (* pick a random pivot that belongs to this interval *)
            \E pivot \in li..hi:
            LET
                newseq == Partitions(seq, pivot)
                newStack == IF li = hi THEN {} ELSE {<<li,(pivot-1)>>, <<pivot,hi>>}
            IN
                /\ seq' = newseq
                /\ stack' = (stack \ {<<li,hi>>}) \cup newStack

Liveness == WF_vars(Next)

Spec == Init /\ [][Next]_<<vars>> /\ Liveness

Correctness == Sorted(seq)

=============================================================================
\* Modification History
\* Last modified Sat Jan 14 17:12:00 CET 2023 by alessio
\* Created Wed Jan 11 11:39:24 CET 2023 by alessio
