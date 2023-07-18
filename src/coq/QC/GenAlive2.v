From Vellvm Require Import
  Utilities
  AstLib
  Semantics.Memory.Sizeof
  LLVMEvents
  LLVMAst
  QC.Utils
  QC.Generators
  Handlers.
(* Maybe also import InterpretationStack *)

From ExtLib.Structures Require Export
  Functor Applicative Monad Monoid.

Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.EitherMonad.
Require Export ExtLib.Structures.Functor.

Require Import List.

Import ListNotations.
Import MonadNotation.
Import ApplicativeNotation.

From Coq Require Import
  ZArith Bool.Bool String.

Require Import QuickChick.GenLow.
Require Import QuickChick.GenHigh.
Import GenHigh.
Import GenLow.
(* Import QcDefaultNotation. *)
Open Scope qc_scope.
Open Scope Z_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".
(* (* Definition nat_gen_example : G nat := *) *)
(* (*   choose (0, 10)%nat. *) *)

(* Some code that may be useful*)
(* Module GEN_ALIVE2'. *)
(*   Module DV := InterpreterStackBigIntptr.LP.Events.DV. *)
(*   Fixpoint gen_uvalue `{MonadExc string G} (t : typ) : G DV.uvalue := *)
(*     match t with *)
(*     | TYPE_I i => *)
(*         match i with *)
(*         | 1%N => *)
(*             returnGen DV.UVALUE_I1 <*> (returnGen DV.repr <*> (choose (0, 1))) *)
(*             (* x <- choose (0,1);; *) *)
(*             (* returnGen (UVALUE_I1 (repr x))  *) *)
(*         | 8%N => *)
(*             returnGen DV.UVALUE_I8 <*> (returnGen DV.repr <*> (choose (0, 2^8))) *)
(*             (* x <- choose (0,2 ^ 8);; *) *)
(*             (* returnGen (UVALUE_I8 (repr x)) *) *)
(*         | 32%N => *)
(*             returnGen DV.UVALUE_I32 <*> (returnGen DV.repr <*> (choose (0, 2^32))) *)
(*             (* x <- choose (0, 2 ^ 32);; *) *)
(*             (* returnGen (UVALUE_I32 (repr x)) *) *)
(*         | 64%N => *)
(*             returnGen DV.UVALUE_I64 <*> (returnGen DV.repr <*> (choose (0, 2^64))) *)
(*             (* x <- choose (0, 2 ^ 63);; *) *)
(*             (* returnGen (UVALUE_I64 (repr x)) *) *)
(*         | _ => failwith "Invalid size" *)
(*         end *)
(*     | TYPE_Float => *)
(*         returnGen DV.UVALUE_Float <*> fing32 *)
(*     | TYPE_Double => *)
(*         returnGen DV.UVALUE_None (* FailGen *) *)
(*     | TYPE_Void => returnGen DV.UVALUE_None *)
(*     | TYPE_Vector sz subtyp => *)
(*         returnGen DV.UVALUE_Vector <*> vectorOf (N.to_nat sz) (gen_uvalue subtyp) *)
(*     | TYPE_Array sz subtyp => *)
(*         returnGen DV.UVALUE_Array <*> vectorOf (N.to_nat sz) (gen_uvalue subtyp) *)
(*     | _ => failwith "Unimplemented uvalue generators" *)
(*     end. *)
(* End GEN_ALIVE2'. *)

(* Module GEN_ALIVE2 (ADDR : MemoryAddress.ADDRESS) (IP:MemoryAddress.INTPTR) (SIZEOF : Sizeof) (LLVMEvents:LLVM_INTERACTIONS(ADDR)(IP)(SIZEOF)). *)
(*   Import LLVMEvents. *)
(*   Import DV. *)

(*   Record GenState := { *)
(*     num_void : nat}. *)

(*   Definition init_GenState : GenState *)
(*     := *)
(*     {| *)
(*       num_void := 0 *)
(*     |}. *)
(*   (* {}. *) *)
    
(*   Definition GenALIVE2 := (eitherT string (stateT GenState G)). *)

(*   #[global] Instance monad_stateT {s m} `{Monad m} : Monad (stateT s m). *)
(*   Proof. *)
(*     apply Monad_stateT. typeclasses eauto. *)
(*   Defined. *)

(*   #[global] Instance STGST : Monad (stateT GenState G). *)
(*   Proof. *)
(*     apply Monad_stateT. typeclasses eauto. *)
(*   Defined. *)
  
(*   #[global] Instance MGEN : Monad GenALIVE2. *)
(*   Proof. *)
(*     apply Monad_eitherT. typeclasses eauto. *)
(*   Defined. *)

(*   Definition lift_GenALIVE2 {A} (g : G A) : GenALIVE2 A. *)
(*     unfold GenALIVE2. *)
(*     apply mkEitherT. *)
(*     apply mkStateT. *)
(*     refine (fun stack => _). *)
(*     refine (a <- g;; _). *)
(*     refine (ret (inr a, stack)). *)
(*   Defined. *)

(*   #[global] Instance MGENT: MonadT GenALIVE2 G. *)
(*   unfold GenALIVE2. *)
(*   constructor. *)
(*   exact @lift_GenALIVE2. *)
(*   Defined. *)
  
(*   Definition failGen {A : Type} (s : string) : GenALIVE2 A. *)
(*     apply mkEitherT. *)
(*     apply mkStateT. *)
(*     refine (fun stack => _ ). *)
(*     exact (ret (inl (s), stack)). *)
(*   Defined. *)

(*   Definition vectorOf_ALIVE2 {A : Type} (k : nat) (g : GenALIVE2 A) : GenALIVE2 (list A). *)
(*     refine (fold_left _ _ _). *)
(*     refine (fun l g => _). *)
(*     refine (a <- g ;; _). *)
(*     refine (a' <- l ;; _). *)
(*     exact (ret (a :: a')). *)
(*     exact (repeat g k). *)
(*     exact (ret []). *)
(*   Defined. *)

(*   Definition run_GenALIVE2 {A : Type} (g : GenALIVE2 A) : G (string + A) *)
(*     := *)
(*     let ran := runStateT (unEitherT g) init_GenState in *)
(*     '(errA, _) <- ran;; *)
(*     ret errA *)
(*   . *)
  
(*   Fixpoint gen_uvalue (t : typ) : GenALIVE2 uvalue := *)
(*     match t with *)
(*     | TYPE_I i => *)
(*         match i with *)
(*         | 1%N => *)
(*             ret UVALUE_I1 <*> (ret repr <*> lift_GenALIVE2 (choose (0, 1))) *)
(*         | 8%N => *)
(*             ret UVALUE_I8 <*> (ret repr <*> lift_GenALIVE2 (choose (0, 2^8 - 1))) *)
(*         | 32%N => *)
(*             ret UVALUE_I32 <*> (ret repr <*> lift_GenALIVE2 (choose (0, 2^32 - 1))) *)
(*         | 64%N => *)
(*             ret UVALUE_I64 <*> (ret repr <*> lift_GenALIVE2 (choose (0, 2^64 - 1))) *)
(*         | _ => *)
(*             failGen "Invalid size" *)
(*         end *)
(*     | TYPE_Float => *)
(*         ret UVALUE_Float <*> lift_GenALIVE2 fing32 *)
(*     | TYPE_Double => *)
(*         failGen "Generating UValue Double - Not supported" *)
(*     | TYPE_Void => ret UVALUE_None *)
(*     | TYPE_Vector sz subtyp => *)
(*         ret UVALUE_Vector <*> (vectorOf_ALIVE2 (N.to_nat sz) (gen_uvalue subtyp)) *)
(*     | TYPE_Array sz subtyp => *)
(*         ret UVALUE_Array <*> (vectorOf_ALIVE2 (N.to_nat sz) (gen_uvalue subtyp)) *)
(*     | _ => failGen "Invalid" *)
(*     end. *)
(* End GEN_ALIVE2. *)

Module GEN_ALIVE2 (ADDR : MemoryAddress.ADDRESS) (IP:MemoryAddress.INTPTR) (SIZEOF : Sizeof).
  Module DV := DynamicValues.DVALUE(ADDR)(IP)(SIZEOF).
  Import DV.
  Record GenState := {
    num_void : nat}.

  Definition init_GenState : GenState
    :=
    {|
      num_void := 0
    |}.
  (* {}. *)
    
  Definition GenALIVE2 := (eitherT string (stateT GenState G)).

  #[global] Instance monad_stateT {s m} `{Monad m} : Monad (stateT s m).
  Proof.
    apply Monad_stateT. typeclasses eauto.
  Defined.

  #[global] Instance STGST : Monad (stateT GenState G).
  Proof.
    apply Monad_stateT. typeclasses eauto.
  Defined.
  
  #[global] Instance MGEN : Monad GenALIVE2.
  Proof.
    apply Monad_eitherT. typeclasses eauto.
  Defined.

  Definition lift_GenALIVE2 {A} (g : G A) : GenALIVE2 A.
    unfold GenALIVE2.
    apply mkEitherT.
    apply mkStateT.
    refine (fun stack => _).
    refine (a <- g;; _).
    refine (ret (inr a, stack)).
  Defined.

  #[global] Instance MGENT: MonadT GenALIVE2 G.
  unfold GenALIVE2.
  constructor.
  exact @lift_GenALIVE2.
  Defined.
  
  Definition failGen {A : Type} (s : string) : GenALIVE2 A.
    apply mkEitherT.
    apply mkStateT.
    refine (fun stack => _ ).
    exact (ret (inl (s), stack)).
  Defined.

  Definition vectorOf_ALIVE2 {A : Type} (k : nat) (g : GenALIVE2 A) : GenALIVE2 (list A).
    refine (fold_left _ _ _).
    refine (fun l g => _).
    refine (a <- g ;; _).
    refine (a' <- l ;; _).
    exact (ret (a :: a')).
    exact (repeat g k).
    exact (ret []).
  Defined.

  Definition run_GenALIVE2 {A : Type} (g : GenALIVE2 A) : G (string + A)
    :=
    let ran := runStateT (unEitherT g) init_GenState in
    '(errA, _) <- ran;;
    ret errA
  .
  
  Fixpoint gen_uvalue (t : typ) : GenALIVE2 uvalue :=
    match t with
    | TYPE_I i =>
        match i with
        | 1%N =>
            ret UVALUE_I1 <*> (ret repr <*> lift_GenALIVE2 (choose (0, 1)))
        | 8%N =>
            ret UVALUE_I8 <*> (ret repr <*> lift_GenALIVE2 (choose (0, 2^8 - 1)))
        | 32%N =>
            ret UVALUE_I32 <*> (ret repr <*> lift_GenALIVE2 (choose (0, 2^32 - 1)))
        | 64%N =>
            ret UVALUE_I64 <*> (ret repr <*> lift_GenALIVE2 (choose (0, 2^64 - 1)))
        | _ =>
            failGen "Invalid size"
        end
    | TYPE_Float =>
        ret UVALUE_Float <*> lift_GenALIVE2 fing32
    | TYPE_Double =>
        failGen "Generating UValue Double - Not supported"
    | TYPE_Void => ret UVALUE_None
    | TYPE_Vector sz subtyp =>
        ret UVALUE_Vector <*> (vectorOf_ALIVE2 (N.to_nat sz) (gen_uvalue subtyp))
    | TYPE_Array sz subtyp =>
        ret UVALUE_Array <*> (vectorOf_ALIVE2 (N.to_nat sz) (gen_uvalue subtyp))
    | _ => failGen "Invalid"
    end.
                                            

  
  (* Fixpoint gen_uvalue (t : typ): GenALIVE2 uvalue := *)
  (*   match t with *)
  (*   | TYPE_I i => *)
  (*       match i with *)
  (*       | 1%N => *)
  (*           ret UVALUE_I1 <*> (returnGen repr <*> (choose (0, 1))) *)
  (*           (* x <- choose (0,1);; *) *)
  (*           (* returnGen (UVALUE_I1 (repr x))  *) *)
  (*       | 8%N => *)
  (*           ret UVALUE_I8 <*> (returnGen repr <*> (choose (0, 2^8))) *)
  (*           (* x <- choose (0,2 ^ 8);; *) *)
  (*           (* returnGen (UVALUE_I8 (repr x)) *) *)
  (*       | 32%N => *)
  (*           ret UVALUE_I32 <*> (returnGen repr <*> (choose (0, 2^32))) *)
  (*           (* x <- choose (0, 2 ^ 32);; *) *)
  (*           (* returnGen (UVALUE_I32 (repr x)) *) *)
  (*       | 64%N => *)
  (*           ret UVALUE_I64 <*> (returnGen repr <*> (choose (0, 2^64))) *)
  (*           (* x <- choose (0, 2 ^ 63);; *) *)
  (*           (* returnGen (UVALUE_I64 (repr x)) *) *)
  (*       | _ => failGen "Invalid size" *)
  (*       end *)
  (*   | TYPE_Float => *)
  (*       ret UVALUE_Float <*> fing32 *)
  (*   | TYPE_Double => *)
  (*       ret UVALUE_None (* FailGen *) *)
  (*   | TYPE_Void => ret UVALUE_None *)
  (*   | TYPE_Vector sz subtyp => *)
  (*       ret UVALUE_Vector <*> vectorOf (N.to_nat sz) (gen_uvalue subtyp) *)
  (*   | TYPE_Array sz subtyp => *)
  (*       ret UVALUE_Array <*> vectorOf (N.to_nat sz) (gen_uvalue subtyp) *)
  (*   | _ => failGen "Unimplemented uvalue generators" *)
  (*   end. *)
  
End GEN_ALIVE2.

(* Module G := GEN_ALIVE2 MemoryModelImplementation.FinAddr MemoryModelImplementation.IP64Bit MemoryModelImplementation.FinSizeof  . (* LLVMEvents64. *) *)
 
(* (* Extract Inlined Constant fst => "fst". *) *)
(* (* Extract Inlined Constant app => "append". *) *)
(* (* Extract Inlined Constant rev => "rev". *) *)
(* (* Extract Inlined Constant map => "map". *) *)
(* (* Extract Inlined Constant combine => "combine". *) *)
(* (* (* Extract Inlined Constant eqn => "( == )". *) *) *)

(* (* Recursive Extraction nat_gen_example. *) *)
