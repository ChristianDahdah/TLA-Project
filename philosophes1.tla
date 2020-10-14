---------------- MODULE philosophes1 ----------------
(* Philosophes. Version en utilisant l'état des voisins. *)

EXTENDS Naturals

CONSTANT N

Philos == 0..N-1

gauche(i) == (i+1)%N       \* philosophe à gauche du philo n°i
droite(i) == (i+N-1)%N     \* philosophe à droite du philo n°i

Hungry == "H"
Thinking == "T"
Eating == "E"

(* D�finition des �tats possibles des fourchettes *)
ForkStatus == {"Taken", "Available"}

VARIABLES
    etat,         \* i -> Hungry,Thinking,Eating
    forksStatus,
    forksTaken


TypeInvariant == 
    [](/\ etat \in [ Philos -> { Hungry, Thinking, Eating }]
       /\ forksStatus \in [ Philos -> ForkStatus ]
       /\ forksTaken \in [ Philos -> 0..2 ] )
       

(* TODO : autres propri�t�s de philosophes0 (exclusion, vivacit�) *)  

(* Si un philosophe mange, il faut s'assurer que le philosophe de droite et de gauche ne mange pas *)

ExclusionMutuelle == \A i \in Philos : etat[i] = Eating => etat[gauche(i)] /= Eating /\ etat[droite(i)] /= Eating 

PasDeFamine == \A i \in Philos : etat[i] = Hungry ~> etat[i] = Eating 

----------------------------------------------------------------

(* Au d�but les philosphes sont dans l'�tat "Thinking" et tous les fourchettes en �tat disponible *)
(* Sous-entendu aucun philosophe n'a une fourchette en main*)
Init == 
    /\ etat = [ i \in Philos |-> Thinking ]
    /\ forksStatus = [ i \in Philos |-> "Available" ]
    /\ forksTaken = [i \in Philos |-> 0 ]
    
demande(i) ==
    /\ etat[i] = Thinking
    /\ etat' = [ etat EXCEPT ![i] = Hungry ]
    /\ UNCHANGED <<forksStatus,forksTaken>>
    
(* Prendre la fourchette du c�t� gauche*)    
prendGauche(i) ==
    /\ etat[i] = Hungry
    /\ forksTaken[i] < 2
    /\ forksStatus[gauche(i)] = "Available"
    /\ forksStatus' = [forksStatus EXCEPT ![gauche(i)] = "Taken" ]
    /\ forksTaken' = [forksTaken EXCEPT ![i] = forksTaken[i] + 1]
    /\ UNCHANGED <<etat>>

(* Prendre la fourchette du c�t� droit*) 
prendDroite(i) ==
    /\ etat[i] = Hungry
    /\ forksTaken[i] < 2
    /\ forksStatus[droite(i)] = "Available"
    /\ forksStatus' = [forksStatus EXCEPT ![droite(i)] = "Taken" ]
    /\ forksTaken' = [forksTaken EXCEPT ![i] = forksTaken[i] + 1]
    /\ UNCHANGED <<etat>>
        
(* Les conditions:     /\ etat[gauche(i)] /= Eating
                       /\ etat[droite(i)] /= Eating 
   Ne sont plus n�cessaires puisque si un philosophe a 2 fourchettes, 
   �a implique que les philosophes � cot� ont au plus 1 seule fourchette donc ne mange pas*)        
     
mange(i) ==
    /\ etat[i] = Hungry
    /\ forksTaken[i] = 2
    /\ etat' = [etat EXCEPT ![i] = Eating]
    /\ UNCHANGED <<forksTaken,forksStatus>>
    
pense(i) ==
    /\ etat[i] = Eating
    /\ etat' = [etat EXCEPT ![i] = Thinking]
    /\ forksStatus' = [forksStatus EXCEPT ![gauche(i)] = "Available", ![droite(i)] = "Available" ]
    /\ forksTaken' = [forksTaken EXCEPT ![i] = 0]

Next ==
  \E i \in Philos : \/ demande(i)
                    \/ mange(i)
                    \/ pense(i)
                    \/ prendGauche(i)
                    \/ prendDroite(i)

(* Premi�re WF: le philosophe ne doit pas rester dans un mode attente ou "Hungry" *)
(* Deuxi�me WF: le philosophe ne doit pas 'prendre les ressources' ind�finiment et emp�cher les autres de manger*)
(* Pas de WF sur demande(i) car je n'ai pas de probl�me qu'un philosophe reste dans le mode "Thinking" *)
Fairness == \A i \in Philos :
    /\ WF_<<etat,forksStatus,forksTaken>> (mange(i))
    /\ WF_<<etat,forksStatus,forksTaken>> (pense(i))
    /\ WF_<<etat,forksStatus,forksTaken>> (prendGauche(i))
    /\ WF_<<etat,forksStatus,forksTaken>> (prendDroite(i))
    

Spec ==
  /\ Init
  /\ [] [ Next ]_<<etat,forksStatus,forksTaken>>
  /\ Fairness

================================
