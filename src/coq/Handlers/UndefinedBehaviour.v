From Vellvm Require Import
     LLVMEvents.

From ITree Require Import
     ITree.

Definition UB_handler: forall {X}, UBE X -> (itree void1 X -> Prop) := fun _ _ _ => True.

