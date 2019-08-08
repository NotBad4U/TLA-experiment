------------------ MODULE tp3_Q1 -------------------------------
EXTENDS Naturals, TLC, Reals
(* --algorithm tp3_Q1
{   
    variables buf1 = -1, buf2 = -1, err = 0, entree;
    
    macro send(buffer, value) {
        await buffer = -1; 
        buffer := value;
    }
    
    macro receive(buffer, value) {
        await buffer # -1;
        value := buffer;
        buffer := -1;
    }
    
    fair process(producteur = 0)
    {
        etiq1: while(TRUE) {
            etiq8: with (v \in 1..5) {
                entree := v;
                send(buf1, v);
            }
        }
    }
       
    fair process(traitement = 1)
        variables value;
    {
        etiq2: while(TRUE) {
            etiq6: with (t \in 0..1){
                err := t;
                if (t = 0){
                    receive(buf1, value);
                    send(buf2, value + 1);        
                } else {
                    send(buf2, 0);
                }
            }
            
        }  
    }    
    
    fair process (consommateur = 2)
        variables resultat;
    {
        etiq3: while(TRUE) {
            receive(buf2, resultat);
            print resultat;
        }
    }     
}
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES buf1, buf2, err, entree, pc, value, resultat

vars == << buf1, buf2, err, entree, pc, value, resultat >>

ProcSet == {0} \cup {1} \cup {2}

Init == (* Global variables *)
        /\ buf1 = -1
        /\ buf2 = -1
        /\ err = 0
        /\ entree = defaultInitValue
        (* Process traitement *)
        /\ value = defaultInitValue
        (* Process consommateur *)
        /\ resultat = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "etiq1"
                                        [] self = 1 -> "etiq2"
                                        [] self = 2 -> "etiq3"]

etiq1 == /\ pc[0] = "etiq1"
         /\ pc' = [pc EXCEPT ![0] = "etiq8"]
         /\ UNCHANGED << buf1, buf2, err, entree, value, resultat >>

etiq8 == /\ pc[0] = "etiq8"
         /\ \E v \in 1..5:
              /\ entree' = v
              /\ buf1 = -1
              /\ buf1' = v
         /\ pc' = [pc EXCEPT ![0] = "etiq1"]
         /\ UNCHANGED << buf2, err, value, resultat >>

producteur == etiq1 \/ etiq8

etiq2 == /\ pc[1] = "etiq2"
         /\ pc' = [pc EXCEPT ![1] = "etiq6"]
         /\ UNCHANGED << buf1, buf2, err, entree, value, resultat >>

etiq6 == /\ pc[1] = "etiq6"
         /\ \E t \in 0..1:
              /\ err' = t
              /\ IF t = 0
                    THEN /\ buf1 # -1
                         /\ value' = buf1
                         /\ buf1' = -1
                         /\ buf2 = -1
                         /\ buf2' = value' + 1
                    ELSE /\ buf2 = -1
                         /\ buf2' = 0
                         /\ UNCHANGED << buf1, value >>
         /\ pc' = [pc EXCEPT ![1] = "etiq2"]
         /\ UNCHANGED << entree, resultat >>

traitement == etiq2 \/ etiq6

etiq3 == /\ pc[2] = "etiq3"
         /\ buf2 # -1
         /\ resultat' = buf2
         /\ buf2' = -1
         /\ PrintT(resultat')
         /\ pc' = [pc EXCEPT ![2] = "etiq3"]
         /\ UNCHANGED << buf1, err, entree, value >>

consommateur == etiq3

Next == producteur \/ traitement \/ consommateur

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(producteur)
        /\ WF_vars(traitement)
        /\ WF_vars(consommateur)

\* END TRANSLATION
=====
