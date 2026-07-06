From ITree Require Import ITree Eq Rutt HeterogeneousRelations.

From Vellvm Require Import
  Utilities
  Syntax
  Integers
  DynamicValues
  LLVMEvents
  Interfaces.IPtr
  Interfaces.Params
  Implementations.Address
  Implementations.Provenance
  Implementations.IPtrInfinite
  Implementations.IPtrFinite
  Implementations.Memory
  Implementations.ParamsV
  Denotation.

Section Refinement.
  
  Definition PInf : Params := @ParamsV IPZ IPZTheory.
  Definition PFin : Params := @ParamsV IP64Bit IP64BitTheory.
  (* Notation fin x := (@x PFin) *)

  Set Printing Implicit.

  Definition I2F_Iptr : @iptr IPZ -> @iptr IP64Bit -> Prop :=
    fun z i => z = unsigned i.

  Definition I2F_Addr : @addr ProvenanceV (@AddressV IPZ) -> @addr ProvenanceV (@AddressV IP64Bit) -> Prop :=
    fun '(z,p) '(i,p') => I2F_Iptr z i /\ p = p'.
  
  Inductive I2F_dvalue : @dvalue PInf -> @dvalue PFin -> Prop :=
  | I2F_dvalue_Addr a a' :
    I2F_Addr a a' ->
    I2F_dvalue (@DVALUE_Addr PInf a) (@DVALUE_Addr PFin a')
  | I2F_dvalue_Int sz i :
    I2F_dvalue (DVALUE_I sz i) (DVALUE_I sz i)
  | I2F_dvalue_Ptr p p' :
    I2F_Iptr p p' ->
    I2F_dvalue (@DVALUE_Iptr PInf p) (@DVALUE_Iptr PFin p')
  | I2F_dvalue_Double d :
    I2F_dvalue (DVALUE_Double d) (DVALUE_Double d)
  | I2F_dvalue_Float f :
    I2F_dvalue (DVALUE_Float f) (DVALUE_Float f)
  | I2F_dvalue_Poison τ :
    I2F_dvalue (DVALUE_Poison τ) (DVALUE_Poison τ)
  | I2F_dvalue_None :
    I2F_dvalue DVALUE_None DVALUE_None
  | I2F_dvalue_Struct s1 s2 :
    Forall2 I2F_dvalue s1 s2 ->
    I2F_dvalue (DVALUE_Struct s1) (DVALUE_Struct s2)
  | I2F_dvalue_Packed_struct s1 s2 :
    Forall2 I2F_dvalue s1 s2 ->
    I2F_dvalue (DVALUE_Packed_struct s1) (DVALUE_Packed_struct s2)
  | I2F_dvalue_Array τ s1 s2 :
    Forall2 I2F_dvalue s1 s2 ->
    I2F_dvalue (DVALUE_Array τ s1) (DVALUE_Array τ s2)
  | I2F_dvalue_Vector τ s1 s2 :
    Forall2 I2F_dvalue s1 s2 ->
    I2F_dvalue (DVALUE_Vector τ s1) (DVALUE_Vector τ s2)
  .

  Variant I2FE : forall A B, @CFGEtop PInf A -> @CFGEtop PFin B -> Prop :=
    | I2FE_call τ dv1 args1 dv2 args2 :
      I2F_dvalue dv1 dv2 ->
      Forall2 I2F_dvalue args1 args2 ->
      I2FE (subevent _ (@Call PInf τ dv1 args1)) (subevent _ (@Call PFin τ dv2 args2))
    | I2FE_extcall τ dv1 args1 dv2 args2 :
      I2F_dvalue dv1 dv2 ->
      Forall2 I2F_dvalue args1 args2 ->
      I2FE (subevent _ (@ExternalCall PInf τ dv1 args1)) (subevent _ (@ExternalCall PFin τ dv2 args2))
    | I2FE_stdout args :
      I2FE (subevent _ (@IO_stdout PInf args)) (subevent _ (@IO_stdout PFin args))
    | I2FE_stderr args :
      I2FE (subevent _ (@IO_stderr PInf args)) (subevent _ (@IO_stderr PFin args))
    | I2FE_intrinsic τ msg args1 oa1 args2 oa2 :
      option_rel I2F_Addr oa1 oa2 ->
      Forall2 I2F_dvalue args1 args2 ->
      I2FE (subevent _ (@Intrinsic PInf τ msg args1 oa1)) (subevent _ (@Intrinsic PFin τ msg args2 oa2))
    | I2FE_gwrite x dv1 dv2 :
      I2F_dvalue dv1 dv2 ->
      I2FE (subevent _ (@GlobalWrite PInf x dv1)) (subevent _ (@GlobalWrite PFin x dv2))
    | I2FE_gread x :
      I2FE (subevent _ (@GlobalRead PInf x)) (subevent _ (@GlobalRead PFin x))
    | I2FE_lwrite x dv1 dv2 :
      I2F_dvalue dv1 dv2 ->
      I2FE (subevent _ (@LocalWrite PInf x dv1)) (subevent _ (@LocalWrite PFin x dv2))
    | I2FE_lread x :
      I2FE (subevent _ (@LocalRead PInf x)) (subevent _ (@LocalRead PFin x))
    | I2FE_spush args1 args2 :
      Forall2 (prod_rel Logic.eq I2F_dvalue) args1 args2 ->
      I2FE (subevent _ (@StackPush PInf args1)) (subevent _ (@StackPush PFin args2))
    | I2FE_spop :
      I2FE (subevent _ (@StackPop PInf)) (subevent _ (@StackPop PFin))
    | I2FE_ssethandler ob :
      I2FE (subevent _ (@StackSetHandler PInf ob)) (subevent _ (@StackSetHandler PFin ob))
    | I2FE_shandler :
      I2FE (subevent _ (@StackHandler PInf)) (subevent _ (@StackHandler PFin))
    | I2FE_sraise exc1 exc2 :
      I2F_dvalue exc1 exc2 ->
      I2FE (subevent _ (@StackRaise PInf exc1)) (subevent _ (@StackRaise PFin exc2))
    | I2FE_sgetexc :
      I2FE (subevent _ (@StackGetExc PInf)) (subevent _ (@StackGetExc PFin))
   .
     

  Lemma denote_ok : Prop.
    refine (forall i oa oa', rutt I2FE _ _ (@denote_instr PInf i oa) (@denote_instr PFin i (_ oa))).
    3: refine (fmap _).
    3: refine (fun '(a,p) => _).
   3:{ cbn.
    
  
  Lemma handle_memory_refine : Prop.
    refine (forall {X} (e : @MemoryE PInf X), _ : Prop).
      @handle_memoryM PIn


 
