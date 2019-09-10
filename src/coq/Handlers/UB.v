From ITree Require Import 
     ITree.

From Vellvm Require Import
     UndefinedBehaviour
     LLVMEvents.

Definition ub_handler E : UndefinedBehaviourE ~> (fun T => itree E T -> Prop)
  := fun T e => match e with
             | ThrowUB x =>
               fun t => True
             end.
