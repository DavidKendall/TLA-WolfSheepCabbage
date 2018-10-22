-------------------------- MODULE WolfSheepCabbage --------------------------
PARTICIPANT == {"farmer", "wolf", "sheep", "cabbage"}
BANK == {"left", "right"}

VARIABLE
  participants

TypeOk == 
  /\ participants \in [BANK -> SUBSET PARTICIPANT]
----

Opposite(b) == IF b = "left" THEN "right" ELSE "left"

EverythingSafe(p) ==
 /\ \A b \in BANK : ({"wolf", "sheep"} \subseteq p[b] \/ {"sheep", "cabbage"} \subseteq p[b]) => "farmer" \in p[b]
 
Init ==
  /\ participants = [left |-> {"farmer", "wolf", "sheep", "cabbage"}, right |-> {}]

CrossAlone == 
  /\ LET 
       fb == CHOOSE b \in BANK : "farmer" \in participants[b]
     IN    
       /\ participants' = [b \in BANK |-> IF b = fb THEN participants[b] \ {"farmer"} 
                                                    ELSE participants[b] \union {"farmer"}] 
       /\ EverythingSafe(participants')
  
CrossWith(p) ==
  /\ LET 
       fb == CHOOSE b \in BANK : "farmer" \in participants[b]
     IN  
       /\ p \in participants[fb]  
       /\ participants' = [b \in BANK |-> IF b = fb THEN participants[b] \ {"farmer", p}
                                                    ELSE participants[b] \union {"farmer", p}]
       /\ EverythingSafe(participants')
  
Next == 
  \/ CrossAlone
  \/ \E p \in PARTICIPANT \ {"farmer"} :
       \/ CrossWith(p)
          
Goal == participants.right = PARTICIPANT

(*
 * A solution to the problem can be found with the model above by
 * checking the invariant ~Goal and examining the error trace.
 * Alternatively, the behaviour of the model can be less constrained
 * by removing EverythingSafe(participants') from CrossAlone and CrossWith(p)
 * and checking the temporal property ([]EverythingSafe(participants)) => ([]~Goal)
 *)
 

=============================================================================
\* Modification History
\* Last modified Mon Oct 22 08:37:42 BST 2018 by cgdk2
\* Created Wed Oct 03 10:21:23 BST 2018 by cgdk2
