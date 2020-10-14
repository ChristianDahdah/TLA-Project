---------------- MODULE philosophes0 ----------------
(* Philosophes. Version en utilisant l'Ã©tat des voisins. *)

EXTENDS Naturals

CONSTANT N

Philos == 0..N-1

gauche(i) == (i+1)%N       \* philosophe Ã  gauche du philo nÂ°i
droite(i) == (i+N-1)%N     \* philosophe Ã  droite du philo nÂ°i

Hungry == "H"
Thinking == "T"
Eating == "E"

VARIABLES
    etat         \* i -> Hungry,Thinking,Eating

TypeInvariant == [](etat \in [ Philos -> { Hungry, Thinking, Eating }])

(* TODO : autres propriétés de philosophes0 (exclusion, vivacitÃ©) *)  

----------------------------------------------------------------

(* Au début les philosphes sont dans l'état "Thinking" *)
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

(* Première WF: le philosophe ne doit pas rester dans un mode attente ou "Hungry" *)
(* Deuxième WF: le philosophe ne doit 'prendre les ressources' indéfiniment et empêcher les autres de manger*)
(* Pas de WF sur demande(i) car je n'ai pas de problème qu'un philosophe reste dans the mode "Thinking" *)
Fairness == \A i \in 0..N-1 :
    /\ WF_<<etat>> (mange(i))
    /\ WF_<<etat>> (pense(i))

Spec ==
  /\ Init
  /\ [] [ Next ]_<<etat>>
  /\ Fairness

================================
