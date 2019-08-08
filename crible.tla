------------------ MODULE Crible -------------------------------
EXTENDS Naturals, TLC
CONSTANT N
Divides(i,j) == \E k \in 0..j: j = i * k
IsGCD(i,j,k) ==
    Divides(i,j)
   /\ Divides(i,k)
   /\ \A r \in 0..j \cup 0..k :
     (Divides(r,j ) /\ Divides(r,k)) => Divides(r,i)
(* --algorithm Crible
{   
    variables mes= [i \in 0..N |-> 0];

    macro send(x, i) {
        await mes[i] = 0; 
        mes[i] := x;
    }
    
    macro receive(v, i) {
        await mes[i] # 0;
        v := mes[i];
        mes[i] := 0;
    }
    
    process (generator = 0) 
        variables x = 2;
    {
        etiq: while (TRUE) {    
            se1: send(x, 0);
            x := x +1;
        }
    }
       
    process(Filtre \in 1..N)
        variables myvar, v;
    {
        rec: receive(myvar, self -1);
        assert IsGCD(myvar,myvar,myvar);
        
        etiq2: while (TRUE) {
            rec2: receive(v, self -1);
            
            if (v % myvar # 0) {
                se2: send(v, self);
            }    
        }
    }         
}
*)	
\* BEGIN TRANSLATION
\* Label se of process generator at line 15 col 9 changed to se_
CONSTANT defaultInitValue
VARIABLES mes, pc, x, myvar, v

vars == << mes, pc, x, myvar, v >>

ProcSet == {0} \cup (1..N)

Init == (* Global variables *)
        /\ mes = [i \in 0..N |-> 0]
        (* Process generator *)
        /\ x = 2
        (* Process Filtre *)
        /\ myvar = [self \in 1..N |-> defaultInitValue]
        /\ v = [self \in 1..N |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "etiq"
                                        [] self \in 1..N -> "rec"]

etiq == /\ pc[0] = "etiq"
        /\ pc' = [pc EXCEPT ![0] = "se_"]
        /\ UNCHANGED << mes, x, myvar, v >>

se_ == /\ pc[0] = "se_"
       /\ mes[0] = 0
       /\ mes' = [mes EXCEPT ![0] = x]
       /\ x' = x +1
       /\ pc' = [pc EXCEPT ![0] = "etiq"]
       /\ UNCHANGED << myvar, v >>

generator == etiq \/ se_

rec(self) == /\ pc[self] = "rec"
             /\ mes[(self -1)] # 0
             /\ myvar' = [myvar EXCEPT ![self] = mes[(self -1)]]
             /\ mes' = [mes EXCEPT ![(self -1)] = 0]
             /\ Assert(IsGCD(myvar'[self],myvar'[self],myvar'[self]), 
                       "Failure of assertion at line 38, column 9.")
             /\ pc' = [pc EXCEPT ![self] = "etiq2"]
             /\ UNCHANGED << x, v >>

etiq2(self) == /\ pc[self] = "etiq2"
               /\ mes[self -1] # 0
               /\ v' = [v EXCEPT ![self] = mes[self -1]]
               /\ mes' = [mes EXCEPT ![self - 1] = 0]
               /\ IF v'[self] % myvar[self] # 0
                     THEN /\ pc' = [pc EXCEPT ![self] = "se"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "etiq2"]
               /\ UNCHANGED << x, myvar >>

se(self) == /\ pc[self] = "se"
            /\ mes[self] = 0
            /\ mes' = [mes EXCEPT ![self] = v[self]]
            /\ pc' = [pc EXCEPT ![self] = "etiq2"]
            /\ UNCHANGED << x, myvar, v >>

Filtre(self) == rec(self) \/ etiq2(self) \/ se(self)

Next == generator
           \/ (\E self \in 1..N: Filtre(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
=====
