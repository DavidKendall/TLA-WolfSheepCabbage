-------------------------- MODULE WolfSheepCabbage --------------------------
EXTENDS TLC

PARTICIPANT == {"farmer", "wolf", "sheep", "cabbage"}
BANK == {"left", "right"}

VARIABLE
  participants

TypeOk == 
  /\ participants \in [BANK -> SUBSET PARTICIPANT]
----

Opposite(b) == IF b = "left" THEN "right" ELSE "left"

EverythingSafe(p) ==
 /\ (\E b \in BANK : {"wolf", "sheep"} \subseteq p[b]) => (\E b \in BANK : {"wolf", "sheep", "farmer"} \subseteq p[b])
 /\ (\E b \in BANK : {"sheep", "cabbage"} \subseteq p[b]) => (\E b \in BANK : {"sheep", "cabbage", "farmer"} \subseteq p[b])
 
Init ==
  /\ participants = [left |-> {"farmer", "wolf", "sheep", "cabbage"}, right |-> {}]

CrossAlone == 
  /\ LET 
       fb == CHOOSE bank \in BANK : "farmer" \in participants[bank]
       ob == Opposite(fb)
     IN    
       /\ participants' = (fb :> participants[fb] \ {"farmer"} @@ ob :> participants[ob] \union {"farmer"}) 
       /\ EverythingSafe(participants')
  
CrossWith(p) ==
  /\ LET 
       fb == CHOOSE bank \in BANK : "farmer" \in participants[bank]
       ob == Opposite(fb)
     IN    
       /\ participants' = (fb :> participants[fb] \ {"farmer", p} @@ ob :> participants[ob] \union {"farmer", p})
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
 * by removing EverythingSafe(location') from CrossAlone and CrossWith(p)
 * and checking the temporal property ([]EverythingSafe(location)) => ([]~Goal)
 *)
 

=============================================================================
\* Modification History
\* Last modified Sat Oct 20 22:55:26 BST 2018 by cgdk2
\* Created Wed Oct 03 10:21:23 BST 2018 by cgdk2
