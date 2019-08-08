------------------ MODULE tp3_Q2 -------------------------------
EXTENDS Naturals, TLC, Reals
CONSTANT NB_TRAIT
(* --algorithm tp3_Q2
{   
    variables buffer_final = -1, in = [i \in 0..NB_TRAIT |-> -1], err = [j \in 0..NB_TRAIT |-> 0], out = [k \in 0..NB_TRAIT |-> -1], entree;
    
    macro send(buffer, value) {
        await buffer = -1; 
        buffer := value;
    }
    
    macro receive(buffer, value) {
        await buffer # -1;
        value := buffer;
        buffer := -1;
    }
    
    macro treat(err, in, out, value, t) {
        err := t;
        if (t = 0) {
            receive(in, value);
            send(out, value + 1);      
        }
    }
    
    fair process(producteur = 0)
        variables m, input = 0;
    {
        etiq1: while(TRUE) {
            etiq8: with (v \in 1..5) {
                entree := v;
                input := v;
            };
            m := 0;
            etiq10: while(m < NB_TRAIT) {
                send(in[m], input);
                m := m + 1
            }
        }
    }

    fair process(traitement \in 3..NB_TRAIT+3)
        variables value;
    {
        etiq2: while(TRUE) {
            etiq6: with (t \in 0..1) {
                treat(err[self-3], in[self-3], out[self-3], value, t);
            }
        }
    }    
    
    fair process (voteur = 1)
        variables p = 0, n, imajoritaire, majoritaire = 0, resultat = [l \in 0..NB_TRAIT |-> 0], majorite = [o \in 0..4 |-> 0], unique = 0;
    {
        etiq3: while(TRUE) {
            n := 0;
            etiq11: while(n < NB_TRAIT) {
                receive(out[n], resultat[n]);
                n := n + 1;
            };
            
            n := 0;
            etiq16: while(n < NB_TRAIT) {
                majorite[resultat[n]-2] := majorite[resultat[n]-2] + 1;
                n := n + 1;
            };
            
             \* On récupère le majoritaire
            n := 0;
            etiq12: while(n < 5) {
                etiq13: if (majorite[n] > majoritaire) {
                    majoritaire := n
                };
                n := n + 1
            };
            
            \* On vérifie que le majoritaire est unique
            n := 0;
            etiq15: while(n < 5) {
                if (majorite[n] = majoritaire) {
                    unique := unique + 1;
                };
                n := n + 1;
            };
            
            if (unique = 1) {
                \* On est sûr que le majoritaire est unique, on send au consommateur
                send(buffer_final, majoritaire + 2);
            };           

        }
    }
    
    
    fair process (consommateur = 2)
        variable resultat_final = 0;
    {
       etiq14: receive(buffer_final, resultat_final);
        print resultat_final;
    }     
}
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES buffer_final, in, err, out, entree, pc, m, input, value, p, n, 
          imajoritaire, majoritaire, resultat, majorite, unique, 
          resultat_final

vars == << buffer_final, in, err, out, entree, pc, m, input, value, p, n, 
           imajoritaire, majoritaire, resultat, majorite, unique, 
           resultat_final >>

ProcSet == {0} \cup (3..NB_TRAIT+3) \cup {1} \cup {2}

Init == (* Global variables *)
        /\ buffer_final = -1
        /\ in = [i \in 0..NB_TRAIT |-> -1]
        /\ err = [j \in 0..NB_TRAIT |-> 0]
        /\ out = [k \in 0..NB_TRAIT |-> -1]
        /\ entree = defaultInitValue
        (* Process producteur *)
        /\ m = defaultInitValue
        /\ input = 0
        (* Process traitement *)
        /\ value = [self \in 3..NB_TRAIT+3 |-> defaultInitValue]
        (* Process voteur *)
        /\ p = 0
        /\ n = defaultInitValue
        /\ imajoritaire = defaultInitValue
        /\ majoritaire = 0
        /\ resultat = [l \in 0..NB_TRAIT |-> 0]
        /\ majorite = [o \in 0..4 |-> 0]
        /\ unique = 0
        (* Process consommateur *)
        /\ resultat_final = 0
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "etiq1"
                                        [] self \in 3..NB_TRAIT+3 -> "etiq2"
                                        [] self = 1 -> "etiq3"
                                        [] self = 2 -> "etiq14"]

etiq1 == /\ pc[0] = "etiq1"
         /\ pc' = [pc EXCEPT ![0] = "etiq8"]
         /\ UNCHANGED << buffer_final, in, err, out, entree, m, input, value, 
                         p, n, imajoritaire, majoritaire, resultat, majorite, 
                         unique, resultat_final >>

etiq8 == /\ pc[0] = "etiq8"
         /\ \E v \in 1..5:
              /\ entree' = v
              /\ input' = v
         /\ m' = 0
         /\ pc' = [pc EXCEPT ![0] = "etiq10"]
         /\ UNCHANGED << buffer_final, in, err, out, value, p, n, imajoritaire, 
                         majoritaire, resultat, majorite, unique, 
                         resultat_final >>

etiq10 == /\ pc[0] = "etiq10"
          /\ IF m < NB_TRAIT
                THEN /\ (in[m]) = -1
                     /\ in' = [in EXCEPT ![m] = input]
                     /\ m' = m + 1
                     /\ pc' = [pc EXCEPT ![0] = "etiq10"]
                ELSE /\ pc' = [pc EXCEPT ![0] = "etiq1"]
                     /\ UNCHANGED << in, m >>
          /\ UNCHANGED << buffer_final, err, out, entree, input, value, p, n, 
                          imajoritaire, majoritaire, resultat, majorite, 
                          unique, resultat_final >>

producteur == etiq1 \/ etiq8 \/ etiq10

etiq2(self) == /\ pc[self] = "etiq2"
               /\ pc' = [pc EXCEPT ![self] = "etiq6"]
               /\ UNCHANGED << buffer_final, in, err, out, entree, m, input, 
                               value, p, n, imajoritaire, majoritaire, 
                               resultat, majorite, unique, resultat_final >>

etiq6(self) == /\ pc[self] = "etiq6"
               /\ \E t \in 0..1:
                    /\ err' = [err EXCEPT ![self-3] = t]
                    /\ IF t = 0
                          THEN /\ (in[self-3]) # -1
                               /\ value' = [value EXCEPT ![self] = in[self-3]]
                               /\ in' = [in EXCEPT ![self-3] = -1]
                               /\ (out[self-3]) = -1
                               /\ out' = [out EXCEPT ![self-3] = value'[self] + 1]
                          ELSE /\ TRUE
                               /\ UNCHANGED << in, out, value >>
               /\ pc' = [pc EXCEPT ![self] = "etiq2"]
               /\ UNCHANGED << buffer_final, entree, m, input, p, n, 
                               imajoritaire, majoritaire, resultat, majorite, 
                               unique, resultat_final >>

traitement(self) == etiq2(self) \/ etiq6(self)

etiq3 == /\ pc[1] = "etiq3"
         /\ n' = 0
         /\ pc' = [pc EXCEPT ![1] = "etiq11"]
         /\ UNCHANGED << buffer_final, in, err, out, entree, m, input, value, 
                         p, imajoritaire, majoritaire, resultat, majorite, 
                         unique, resultat_final >>

etiq11 == /\ pc[1] = "etiq11"
          /\ IF n < NB_TRAIT
                THEN /\ (out[n]) # -1
                     /\ resultat' = [resultat EXCEPT ![n] = out[n]]
                     /\ out' = [out EXCEPT ![n] = -1]
                     /\ n' = n + 1
                     /\ pc' = [pc EXCEPT ![1] = "etiq11"]
                ELSE /\ n' = 0
                     /\ pc' = [pc EXCEPT ![1] = "etiq16"]
                     /\ UNCHANGED << out, resultat >>
          /\ UNCHANGED << buffer_final, in, err, entree, m, input, value, p, 
                          imajoritaire, majoritaire, majorite, unique, 
                          resultat_final >>

etiq16 == /\ pc[1] = "etiq16"
          /\ IF n < NB_TRAIT
                THEN /\ majorite' = [majorite EXCEPT ![resultat[n]-2] = majorite[resultat[n]-2] + 1]
                     /\ n' = n + 1
                     /\ pc' = [pc EXCEPT ![1] = "etiq16"]
                ELSE /\ n' = 0
                     /\ pc' = [pc EXCEPT ![1] = "etiq12"]
                     /\ UNCHANGED majorite
          /\ UNCHANGED << buffer_final, in, err, out, entree, m, input, value, 
                          p, imajoritaire, majoritaire, resultat, unique, 
                          resultat_final >>

etiq12 == /\ pc[1] = "etiq12"
          /\ IF n < 5
                THEN /\ pc' = [pc EXCEPT ![1] = "etiq13"]
                     /\ n' = n
                ELSE /\ n' = 0
                     /\ pc' = [pc EXCEPT ![1] = "etiq15"]
          /\ UNCHANGED << buffer_final, in, err, out, entree, m, input, value, 
                          p, imajoritaire, majoritaire, resultat, majorite, 
                          unique, resultat_final >>

etiq13 == /\ pc[1] = "etiq13"
          /\ IF majorite[n] > majoritaire
                THEN /\ majoritaire' = n
                ELSE /\ TRUE
                     /\ UNCHANGED majoritaire
          /\ n' = n + 1
          /\ pc' = [pc EXCEPT ![1] = "etiq12"]
          /\ UNCHANGED << buffer_final, in, err, out, entree, m, input, value, 
                          p, imajoritaire, resultat, majorite, unique, 
                          resultat_final >>

etiq15 == /\ pc[1] = "etiq15"
          /\ IF n < 5
                THEN /\ IF majorite[n] = majoritaire
                           THEN /\ unique' = unique + 1
                           ELSE /\ TRUE
                                /\ UNCHANGED unique
                     /\ n' = n + 1
                     /\ pc' = [pc EXCEPT ![1] = "etiq15"]
                     /\ UNCHANGED buffer_final
                ELSE /\ IF unique = 1
                           THEN /\ buffer_final = -1
                                /\ buffer_final' = majoritaire + 2
                           ELSE /\ TRUE
                                /\ UNCHANGED buffer_final
                     /\ pc' = [pc EXCEPT ![1] = "etiq3"]
                     /\ UNCHANGED << n, unique >>
          /\ UNCHANGED << in, err, out, entree, m, input, value, p, 
                          imajoritaire, majoritaire, resultat, majorite, 
                          resultat_final >>

voteur == etiq3 \/ etiq11 \/ etiq16 \/ etiq12 \/ etiq13 \/ etiq15

etiq14 == /\ pc[2] = "etiq14"
          /\ buffer_final # -1
          /\ resultat_final' = buffer_final
          /\ buffer_final' = -1
          /\ PrintT(resultat_final')
          /\ pc' = [pc EXCEPT ![2] = "Done"]
          /\ UNCHANGED << in, err, out, entree, m, input, value, p, n, 
                          imajoritaire, majoritaire, resultat, majorite, 
                          unique >>

consommateur == etiq14

Next == producteur \/ voteur \/ consommateur
           \/ (\E self \in 3..NB_TRAIT+3: traitement(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(producteur)
        /\ \A self \in 3..NB_TRAIT+3 : WF_vars(traitement(self))
        /\ WF_vars(voteur)
        /\ WF_vars(consommateur)

\* END TRANSLATION
=====
