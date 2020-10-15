---------------- MODULE philosophes2 ----------------
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
Status == {"Taken", "Available"}

VARIABLES
    etat,         \* i -> Hungry,Thinking,Eating
    forksStatus,
    forksTaken,
    waiterStatus,
    customer


TypeInvariant == 
    [](/\ etat \in [ Philos -> { Hungry, Thinking, Eating }]
       /\ forksStatus \in [ Philos -> Status ]
       /\ forksTaken \in [ Philos -> 0..2 ] 
       /\ waiterStatus \in Status
       /\ customer \in Philos)

(* TODO : autres propri�t�s de philosophes0 (exclusion, vivacit�) *)  

(* Si un philosophe mange, il faut s'assurer que le philosophe de droite et de gauche ne mange pas *)

ExclusionMutuelle == \A i \in Philos : etat[i] = Eating => etat[gauche(i)] /= Eating /\ etat[droite(i)] /= Eating 

PasDeFamine == \A i \in Philos : etat[i] = Hungry ~> etat[i] = Eating 

----------------------------------------------------------------

(* Au d�but les philosphes sont dans l'�tat "Thinking" et tous les fourchettes en �tat disponible *)
(* Sous-entendu aucun philosophe n'a une fourchette en main*)
(* le waiter (ou le scheduler en r�alit�) ne sert personne au d�but, et donc le num�ro du client peut importe *)
Init == 
    /\ etat = [ i \in Philos |-> Thinking ]
    /\ forksStatus = [ i \in Philos |-> "Available" ]
    /\ forksTaken = [i \in Philos |-> 0 ]
    /\ waiterStatus = "Available"
    /\ customer \in Philos
    
demande(i) ==
    /\ etat[i] = Thinking
    /\ etat' = [ etat EXCEPT ![i] = Hungry ]
    /\ UNCHANGED <<forksStatus, forksTaken, waiterStatus, customer>>
    
(* Le client ou philosophe doit attendre le waiter pour qu'il puisse lui donner la permission de prendre les fourchettes *)
commande(i) ==
    /\ etat[i] = Hungry
    /\ waiterStatus = "Available"
    /\ waiterStatus' = "Taken"
    /\ customer' = i
    /\ UNCHANGED <<etat, forksStatus, forksTaken>>
    
(* M�me si un philosophe "A" en train d'�tre servit n'a pas tous les fourchettes disponibles � un moment (t), 
le fait qu'on impose que chaque philosophe va finir de manger � un certain point 
implique que les fourchettes du philosophe "A" vont �tre toujours libres � un certain temps (t0 + t) et on n'aura pas de deadlock *)    
   
(* Prendre la fourchette du c�t� gauche si elle est disponible et si le waiter le permet *)

(* On ne peut pas enlever la condition: waiterStatus = "Taken" car en �tat initial,
 on peut avoir un philosophe qui n'a pas faim mais que le waiter est fix� sur lui. 
 Hors pour fixer ce probl�me, si le waiter est pris c'est que un philosophe, qui a faim, l'a appel�*)
     
prendGauche(i) ==
    /\ waiterStatus = "Taken"
    /\ i = customer
    /\ forksTaken[i] < 2
    /\ forksStatus[gauche(i)] = "Available"
    /\ forksStatus' = [forksStatus EXCEPT ![gauche(i)] = "Taken" ]
    /\ forksTaken' = [forksTaken EXCEPT ![i] = forksTaken[i] + 1]
    /\ UNCHANGED <<etat, customer, waiterStatus>>

(* Prendre la fourchette du c�t� droit si elle est disponible et si le waiter le permet *) 
prendDroite(i) ==
    /\ waiterStatus = "Taken"
    /\ i = customer
    /\ forksTaken[i] < 2
    /\ forksStatus[droite(i)] = "Available"
    /\ forksStatus' = [forksStatus EXCEPT ![droite(i)] = "Taken" ]
    /\ forksTaken' = [forksTaken EXCEPT ![i] = forksTaken[i] + 1]
    /\ UNCHANGED <<etat, customer, waiterStatus>>
        
(* Les conditions:     /\ etat[gauche(i)] /= Eating
                       /\ etat[droite(i)] /= Eating 
   Ne sont plus n�cessaires puisque si un philosophe a 2 fourchettes, 
   �a implique que les philosophes � cot� ont au plus 1 seule fourchette donc ne mange pas *)        
     
(* Quand un philosophe commence � manger, �a implique qu'il a eu les deux fourchettes et qu'il peut lib�rer le waiter *)     
mange(i) ==
    /\ etat[i] = Hungry
    /\ forksTaken[i] = 2
    /\ etat' = [etat EXCEPT ![i] = Eating]
    /\ waiterStatus' = "Available"
    /\ UNCHANGED <<forksTaken, forksStatus, customer>>
    
pense(i) ==
    /\ etat[i] = Eating
    /\ etat' = [etat EXCEPT ![i] = Thinking]
    /\ forksStatus' = [forksStatus EXCEPT ![gauche(i)] = "Available", ![droite(i)] = "Available" ]
    /\ forksTaken' = [forksTaken EXCEPT ![i] = 0]
    /\ UNCHANGED <<waiterStatus, customer>>

Next ==
  \E i \in Philos : \/ demande(i)
                    \/ mange(i)
                    \/ pense(i)
                    \/ prendGauche(i)
                    \/ prendDroite(i)
                    \/ commande(i)

(* Premi�re WF: le philosophe ne doit pas rester dans un mode attente ou "Hungry" *)
(* Deuxi�me WF: le philosophe ne doit pas 'prendre les ressources' ind�finiment et emp�cher les autres de manger*)
(* Pas de WF sur demande(i) car je n'ai pas de probl�me qu'un philosophe reste dans le mode "Thinking" *)
(* WF sur prendGauche et prendDroite car on veut prendre les fourchettes si elles sont disponibles pour ne pas b�gayer infiniment *)
(* SF sur commande(i) car je ne veut pas avoir de famine en laissant seulement par exemple deux philosophes commander tout le temps tout en ayant d'autes philosophes faim *)
Fairness == \A i \in Philos :
    /\ WF_<<etat, forksStatus, forksTaken, waiterStatus, customer>> (mange(i))
    /\ WF_<<etat, forksStatus, forksTaken, waiterStatus, customer>> (pense(i))
    /\ WF_<<etat, forksStatus, forksTaken, waiterStatus, customer>> (prendGauche(i))
    /\ WF_<<etat, forksStatus, forksTaken, waiterStatus, customer>> (prendDroite(i))
    /\ SF_<<etat, forksStatus, forksTaken, waiterStatus, customer>> (commande(i))
    

Spec ==
  /\ Init
  /\ [] [ Next ]_<<etat,forksStatus,forksTaken, waiterStatus, customer>>
  /\ Fairness

================================
