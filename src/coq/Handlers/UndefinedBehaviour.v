From Vellvm Require Import
     UndefinedBehaviour.

From ITree Require Import
     ITree.

Definition UB_handler: forall {X}, UndefinedBehaviourE X -> (itree void1 X -> Prop) := fun _ _ _ => True.

