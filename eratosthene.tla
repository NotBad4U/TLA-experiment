---------------------------- MODULE Eratosthene ----------------------------


EXTENDS Naturals, TLC
Divides(i,f) == \E k \in 0..f: f = i * k
CONSTANT N

(* --algorithm ErathosteneAlgo
{
    variables mess=[a \in 0..N |-> 0];
    
    macro send(i,v) {
        await(mess[i] = 0);
        mess[i] := v;
    }
    
    macro recive(i,x) {
        await(mess[i] # 0);
        x := mess[i];
        mess[i] := 0;
    }
    
    process (Gen = 0)
    variables k = 2;
    {          
       A1: while(TRUE){
            A2:send(0, k);
            k := k + 1;
       }
    }
    process (Filtre \in 1..N)
    variables j = 0, prem = 0;
    { 
        B1:recive(self-1,prem);
        
        B2:while(TRUE){
            B3:recive(self-1, j); 
            
            B4:if(~Divides(prem,j)){
                B5:send(self, j);
            }
        }
    }    
}
*)
\* BEGIN TRANSLATION
VARIABLES mess, pc, k, j, prem

vars == << mess, pc, k, j, prem >>

ProcSet == {0} \cup (1..N)

Init == (* Global variables *)
        /\ mess = [a \in 0..N |-> 0]
        (* Process Gen *)
        /\ k = 2
        (* Process Filtre *)
        /\ j = [self \in 1..N |-> 0]
        /\ prem = [self \in 1..N |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "A1"
                                        [] self \in 1..N -> "B1"]

A1 == /\ pc[0] = "A1"
      /\ pc' = [pc EXCEPT ![0] = "A2"]
      /\ UNCHANGED << mess, k, j, prem >>

A2 == /\ pc[0] = "A2"
      /\ (mess[0] = 0)
      /\ mess' = [mess EXCEPT ![0] = k]
      /\ k' = k + 1
      /\ pc' = [pc EXCEPT ![0] = "A1"]
      /\ UNCHANGED << j, prem >>

Gen == A1 \/ A2

B1(self) == /\ pc[self] = "B1"
            /\ (mess[(self-1)] # 0)
            /\ prem' = [prem EXCEPT ![self] = mess[(self-1)]]
            /\ mess' = [mess EXCEPT ![(self-1)] = 0]
            /\ pc' = [pc EXCEPT ![self] = "B2"]
            /\ UNCHANGED << k, j >>

B2(self) == /\ pc[self] = "B2"
            /\ pc' = [pc EXCEPT ![self] = "B3"]
            /\ UNCHANGED << mess, k, j, prem >>

B3(self) == /\ pc[self] = "B3"
            /\ (mess[(self-1)] # 0)
            /\ j' = [j EXCEPT ![self] = mess[(self-1)]]
            /\ mess' = [mess EXCEPT ![(self-1)] = 0]
            /\ pc' = [pc EXCEPT ![self] = "B4"]
            /\ UNCHANGED << k, prem >>

B4(self) == /\ pc[self] = "B4"
            /\ IF ~Divides(prem[self],j[self])
                  THEN /\ pc' = [pc EXCEPT ![self] = "B5"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "B2"]
            /\ UNCHANGED << mess, k, j, prem >>

B5(self) == /\ pc[self] = "B5"
            /\ (mess[self] = 0)
            /\ mess' = [mess EXCEPT ![self] = j[self]]
            /\ pc' = [pc EXCEPT ![self] = "B2"]
            /\ UNCHANGED << k, j, prem >>

Filtre(self) == B1(self) \/ B2(self) \/ B3(self) \/ B4(self) \/ B5(self)

Next == Gen
           \/ (\E self \in 1..N: Filtre(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu Dec 14 18:02:04 CET 2017 by Marti_000
\* Created Thu Dec 14 09:46:58 CET 2017 by Marti_000


