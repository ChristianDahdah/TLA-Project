---------------- MODULE philosophes2 ----------------
(* Philosophes. Version en utilisant l'Ã©tat des voisins. *)

EXTENDS Naturals

CONSTANT N

Philos == 0..N-1

gauche(i) == (i+1)%N       \* philosophe Ã  gauche du philo nÂ°i
droite(i) == (i+N-1)%N     \* philosophe Ã  droite du philo nÂ°i

Hungry == "H"
Thinking == "T"
Eating == "E"

(* Définition des états possibles des fourchettes *)
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

(* TODO : autres propriétés de philosophes0 (exclusion, vivacité) *)  

(* Si un philosophe mange, il faut s'assurer que le philosophe de droite et de gauche ne mange pas *)

ExclusionMutuelle == \A i \in Philos : etat[i] = Eating => etat[gauche(i)] /= Eating /\ etat[droite(i)] /= Eating 

PasDeFamine == \A i \in Philos : etat[i] = Hungry ~> etat[i] = Eating 

----------------------------------------------------------------

(* Au début les philosphes sont dans l'état "Thinking" et tous les fourchettes en état disponible *)
(* Sous-entendu aucun philosophe n'a une fourchette en main*)
(* le waiter (ou le scheduler en réalité) ne sert personne au début, et donc le numéro du client peut importe *)
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
    
(* Même si un philosophe "A" en train d'être servit n'a pas tous les fourchettes disponibles à un moment (t), 
le fait qu'on impose que chaque philosophe va finir de manger à un certain point 
implique que les fourchettes du philosophe "A" vont être toujours libres à un certain temps (t0 + t) et on n'aura pas de deadlock *)    
   
(* Prendre la fourchette du côté gauche si elle est disponible et si le waiter le permet *)

(* On ne peut pas enlever la condition: waiterStatus = "Taken" car en état initial,
 on peut avoir un philosophe qui n'a pas faim mais que le waiter est fixé sur lui. 
 Hors pour fixer ce problème, si le waiter est pris c'est que un philosophe, qui a faim, l'a appelé*)
     
prendGauche(i) ==
    /\ waiterStatus = "Taken"
    /\ i = customer
    /\ forksTaken[i] < 2
    /\ forksStatus[gauche(i)] = "Available"
    /\ forksStatus' = [forksStatus EXCEPT ![gauche(i)] = "Taken" ]
    /\ forksTaken' = [forksTaken EXCEPT ![i] = forksTaken[i] + 1]
    /\ UNCHANGED <<etat, customer, waiterStatus>>

(* Prendre la fourchette du côté droit si elle est disponible et si le waiter le permet *) 
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
   Ne sont plus nécessaires puisque si un philosophe a 2 fourchettes, 
   ça implique que les philosophes à coté ont au plus 1 seule fourchette donc ne mange pas *)        
     
(* Quand un philosophe commence à manger, ça implique qu'il a eu les deux fourchettes et qu'il peut libérer le waiter *)     
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

(* Première WF: le philosophe ne doit pas rester dans un mode attente ou "Hungry" *)
(* Deuxième WF: le philosophe ne doit pas 'prendre les ressources' indéfiniment et empêcher les autres de manger*)
(* Pas de WF sur demande(i) car je n'ai pas de problème qu'un philosophe reste dans le mode "Thinking" *)
(* WF sur prendGauche et prendDroite car on veut prendre les fourchettes si elles sont disponibles pour ne pas bégayer infiniment *)
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
