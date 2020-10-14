---------------- MODULE philosophes0 ----------------
(* Philosophes. Version en utilisant l'état des voisins. *)

EXTENDS Naturals

CONSTANT N

Philos == 0..N-1

gauche(i) == (i+1)%N       \* philosophe � gauche du philo n�i
droite(i) == (i+N-1)%N     \* philosophe � droite du philo n�i

Hungry == "H"
Thinking == "T"
Eating == "E"

VARIABLES
    etat         \* i -> Hungry,Thinking,Eating

TypeInvariant == [](etat \in [ Philos -> { Hungry, Thinking, Eating }])

(* TODO : autres propriétés de philosophes0 (exclusion, vivacité) *)  

(* Si un philosophe mange, il faut s'assurer que le philosophe de droite et de gauche ne mange pas *)

ExclusionMutuelle == \A i \in Philos : etat[i] = Eating => etat[gauche(i)] /= Eating /\ etat[droite(i)] /= Eating 

PasDeFamine == \A i \in Philos : etat[i] = Hungry ~> etat[i] = Eating 

----------------------------------------------------------------

(* Au début les philosphes sont dans l'état "Thinking" *)
Init == 
    /\ etat = [ i \in Philos |-> Thinking ]

demande(i) ==
    /\ etat[i] = Thinking
    /\ etat' = [ etat EXCEPT ![i] = Hungry ]

mange(i) ==
    /\ etat[i] = Hungry
    /\ etat[gauche(i)] /= Eating
    /\ etat[droite(i)] /= Eating
    /\ etat' = [etat EXCEPT ![i] = Eating]

pense(i) ==
    /\ etat[i] = Eating
    /\ etat' = [etat EXCEPT ![i] = Thinking]

Next ==
  \E i \in Philos : \/ demande(i)
                    \/ mange(i)
                    \/ pense(i)

(* Premi�re WF: le philosophe ne doit pas rester dans un mode attente ou "Hungry" *)
(* Deuxi�me WF: le philosophe ne doit pas 'prendre les ressources' ind�finiment et emp�cher les autres de manger*)
(* Pas de WF sur demande(i) car je n'ai pas de probl�me qu'un philosophe reste dans l'état "Thinking" *)
Fairness == \A i \in Philos :
    /\ WF_<<etat>> (mange(i))
    /\ WF_<<etat>> (pense(i))

Spec ==
  /\ Init
  /\ [] [ Next ]_<<etat>>
  /\ Fairness

================================
