------------------ MODULE helloworld -------------------------------
EXTENDS TLC
(* --algorithm HelloWorld
{
    { 
        etiq: print "Hello, world.";
            either print "ei"
            or print "ther";
        fin: assert TRUE
    }
}
*)
\* BEGIN TRANSLATION
VARIABLE pc

vars == << pc >>

Init == /\ pc = "etiq"

etiq == /\ pc = "etiq"
        /\ PrintT("Hello, world.")
        /\ \/ /\ PrintT("ei")
           \/ /\ PrintT("ther")
        /\ pc' = "fin"

fin == /\ pc = "fin"
       /\ Assert(TRUE, "Failure of assertion at line 9, column 14.")
       /\ pc' = "Done"

Next == etiq \/ fin
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
====================================================================
