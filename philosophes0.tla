---------------- MODULE philosophes0 ----------------
(* Philosophes. Version en utilisant l'état des voisins. *)

EXTENDS Naturals

CONSTANT N

Philos == 0..N-1

gauche(i) == (i+1)%N       \* philosophe à gauche du philo n°i
droite(i) == (i+N-1)%N     \* philosophe à droite du philo n°i

Hungry == "H"
Thinking == "T"
Eating == "E"

VARIABLES
    etat         \* i -> Hungry,Thinking,Eating

TypeInvariant == [](etat \in [ Philos -> { Hungry, Thinking, Eating }])

(* TODO : autres propri�t�s de philosophes0 (exclusion, vivacité) *)  

----------------------------------------------------------------

(* Au d�but les philosphes sont dans l'�tat "Thinking" *)
Init == 
    /\ etat = [ i \in 0..N-1 |-> "T" ]

demande(i) ==
    /\ etat[i] = "T"
    /\ etat' = [ etat EXCEPT ![i] = "H" ]

mange(i) ==
    /\ etat[i] = "H"
    /\ etat[gauche(i)] /= "E"
    /\ etat[droite(i)] /= "E"
    /\ etat' = [etat EXCEPT ![i] = "E"]

pense(i) ==
    /\ etat[i] = "E"
    /\ etat' = [etat EXCEPT ![i] = "T"]

Next ==
  \E i \in Philos : \/ demande(i)
                    \/ mange(i)
                    \/ pense(i)

(* Premi�re WF: le philosophe ne doit pas rester dans un mode attente ou "Hungry" *)
(* Deuxi�me WF: le philosophe ne doit 'prendre les ressources' ind�finiment et emp�cher les autres de manger*)
(* Pas de WF sur demande(i) car je n'ai pas de probl�me qu'un philosophe reste dans the mode "Thinking" *)
Fairness == \A i \in 0..N-1 :
    /\ WF_<<etat>> (mange(i))
    /\ WF_<<etat>> (pense(i))

Spec ==
  /\ Init
  /\ [] [ Next ]_<<etat>>
  /\ Fairness

================================
