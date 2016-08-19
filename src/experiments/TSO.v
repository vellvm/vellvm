Add LoadPath "C:\Users\William\My Documents\cpdt/src".
Add LoadPath "C:\Users\William\My Documents\Coq\sf".
Require Import LibTactics.
Require Import CpdtTactics.
Require Import List.
Require Import ZArith.
Require Import String.
Require Import SetsAndMaps.
Require Import minillvm.
Require Import Morphisms.
Require Import EqNat.
Import ListNotations.

Set Implicit Arguments.

Section TSO.
  Inductive buffered_op :=
  | BWrite : nat -> const -> buffered_op
  | BAlloc : nat -> buffered_op
  | BFree : nat -> buffered_op.
  Scheme Equality for buffered_op.

  (* Memory representation and equality *)
  Definition TSO_mem := (nat_map const * nat_set * string_map (list buffered_op))%type.

  Lemma nat_const_map_eq_dec: forall (m m' : nat_map const), {NatMap.Equal m m'} + {~NatMap.Equal m m'}.
  Proof.
    apply NatMap.map_eq_dec; apply const_eq_dec.
  Qed.

  Lemma string_buffer_map_eq_dec: forall (m m' : string_map (list buffered_op)),
    {StringMap.Equal m m'} + {~StringMap.Equal m m'}.
  Proof.
    apply StringMap.map_eq_dec; repeat (decide equality).
  Qed.

  Definition sm (m : TSO_mem) := match m with (a, _, _) => a end.
  Definition fs (m : TSO_mem) := match m with (_, a, _) => a end.
  Definition wb (m : TSO_mem) := match m with (_, _, a) => a end.
  Hint Transparent sm fs wb.

  Definition TSO_mem_beq m m' := if nat_const_map_eq_dec (sm m) (sm m') then 
    if NatSet.eq_dec (fs m) (fs m') then 
    if string_buffer_map_eq_dec (wb m) (wb m') then true else false else false else false.
  Definition TSO_mem_eq := (fun m m' => TSO_mem_beq m m' = true).
  
  Lemma TSO_mem_eq_dec: forall m m', {TSO_mem_eq m m'} + {~TSO_mem_eq m m'}.
  Proof.
    intros; unfold TSO_mem_eq; destruct (TSO_mem_beq m m'); crush.
  Qed.

  Instance TSO_mem_eq_equiv: Equivalence TSO_mem_eq.
  Proof.
    intuition; unfold Reflexive; unfold Symmetric; unfold Transitive; unfold TSO_mem_eq; unfold TSO_mem_beq; crush.
      repeat crush_if.
      destruct y; destruct p; repeat crush_if.
      destruct z; destruct p; repeat crush_if.
        false; apply n1; etransitivity; eauto.
        false; apply n1; etransitivity; eauto.
        false; apply n1; etransitivity; eauto.
  Qed.

  Import Bool.
  Definition init_mem_TSO (m : TSO_mem) := NatMap.is_empty (sm m) && StringMap.is_empty (wb m).

  Definition get_locb e :=
    match e with
    | BWrite l _ => l
    | BAlloc l => l
    | BFree l => l
    end.

  Definition read_TSO (m : TSO_mem) (t : string) l := let buf_v := 
    match StringMap.find t (wb m) with
    | Some buf => match find (fun e => beq_nat (get_locb e) l) buf with
                  | Some (BWrite l v) => Some v
                  | _ => None
                  end
    | None => None
    end in
    match buf_v with Some v => Some v | None => NatMap.find l (sm m) end.

  Hint Rewrite andb_true_iff.

  Instance read_proper: Proper (TSO_mem_eq ==> eq ==> eq ==> eq) read_TSO.
  Proof.
    unfolds; unfolds; intros; subst.
      destruct x as ((a, b), c); destruct y as ((a', b'), c'); unfold TSO_mem_eq in H;
        unfold TSO_mem_beq in H; clarify.
      unfold read_TSO; simpl; rewrite e; rewrite e1; auto.
  Qed.

  Definition get_buf m t := match StringMap.find t (wb m) with Some buf => buf | None => [] end.
  

  Definition run_op_TSO m (a : LLVM_access) := 
    match a with
    | Read t l v => if is_free m t l then None else 
        match read_TSO m t l with
        | Some v' => if const_eq_dec v v' then Some m else None
        | None => None
        end
    | Write t l v => if is_free m t l then None else 
        Some (sm m, fs m, StringMap.add t (BWrite l v :: get_buf m t) (wb m))
    | ARW t l v v' => if buffers_clear m then if is_free m t l then None else 
      match read_TSO m t l with
      | Some v0 => if const_eq_dec v v0 then Some (NatMap.add l v' (fst m), snd m) else None
      | None => None
      end else None
    | Alloc t l => if is_free m t l then Some (sm m, fs m, StringMap.add t (BAlloc l :: get_buf m t) (wb m)) else None
    | Free t l => if is_free m t l then None else Some (sm m, fs m, StringMap.add t (BFree l :: get_buf m t) (wb m))
    | Cast t l p => if Z.eqb p (Z.of_nat l) then Some m else None
    end.

  Inductive update_mem_TSO m (ops : list LLVM_access) m' : Prop :=
  | atomic_TSO: forall t (l : nat) v v', ~ NatSet.In l (fs m) -> ops = [ARW t l v v'] ->
      (forall t buf, StringMap.find t (wb m) = Some buf -> buf = []) -> TSO_mem_eq (NatMap.add l v' (sm m), fs m, wb m) m' -> 
      update_mem_TSO m ops m'
  | buffers_TSO: forall t l v buf, StringMap.find t (wb m) = Some (buf ++ [(l, v)]) ->
      update_mem_TSO (NatMap.add l v (sm m), fs m, StringMap.add t buf (wb m)) ops m' -> 
      update_mem_TSO m ops m'.

          Hint Opaque NatSet.Equal NatMap.remove NatSet.remove NatSet.equal NatSet.eq_dec.

  Lemma run_op_TSO_eq: forall m a m' m2, run_op_TSO m a = Some m2 -> TSO_mem_eq m m' ->
    exists m2', run_op_TSO m' a = Some m2' /\ TSO_mem_eq m2 m2'.
  Proof.
    intros ? ? ? ? run mem_eq; destruct a; unfold run_op_TSO in run; intuition; try discriminate; crush_if.      
      rewrite must_be_Some in run; crush; crush_if.
        assert (read_TSO m' s n = read_TSO m2 s n) as eq; [rewrite mem_eq; auto | rewrite eq; rewrite H0; crush].
        eexists; auto.
      destruct m as ((a, b), d); destruct m' as ((a', b'), d'); unfold TSO_mem_eq in mem_eq; unfold TSO_mem_beq in mem_eq; repeat crush_if; simpl in *.
        rewrite e0 in *; crush.
        eexists; split; auto; unfold TSO_mem_eq; unfold TSO_mem_beq; crush.
        repeat crush_if; false; apply n0; rewrite e1; reflexivity.
      destruct m as ((a, b), d); destruct m' as ((a', b'), d'); unfold TSO_mem_eq in mem_eq; unfold TSO_mem_beq in mem_eq; repeat crush_if.
        rewrite e0 in *; crush.
        eexists; split; auto; unfold TSO_mem_eq; unfold TSO_mem_beq; unfold sm; unfold fs; unfold wb.
        generalize (NatMap.F.F.remove_m eq_refl(x := n) e); intro;
          destruct (nat_const_map_eq_dec (NatMap.remove n a) (NatMap.remove n a')) eqn: eq1; auto.
        destruct (NatSet.eq_dec (NatSet.remove n b) (NatSet.remove n b')); crush.
        rewrite e0 in n0; false; apply n0; reflexivity.
      destruct m as ((a, b), d); destruct m' as ((a', b'), d'); unfold TSO_mem_eq in mem_eq; unfold TSO_mem_beq in mem_eq; repeat crush_if.
        rewrite e0 in *; crush.
        eexists; split; auto; unfold TSO_mem_eq; unfold TSO_mem_beq; unfold sm; unfold fs; unfold wb.
        rewrite c0; auto.
        destruct (NatSet.eq_dec (NatSet.add n b) (NatSet.add n b')); crush.
        rewrite e0 in n0; false; apply n0; reflexivity.
      destruct (z =? Z.of_nat n)%Z eqn: try_cast; try discriminate; eexists; crush.
  Qed.

  Instance run_op_TSO_proper: Proper (TSO_mem_eq ==> eq ==> fun a b => match (a, b) with (Some m, Some m') => TSO_mem_eq m m' 
    | (None, None) => True | _ => False end) run_op_TSO.
  Proof.
    unfolds; unfolds; intros; subst.
      destruct (run_op_TSO x y0) eqn: run1.
        specialize (run_op_TSO_eq _ run1 H); crush.
        destruct (run_op_TSO y y0) eqn: run2; crush.
          symmetry in H; specialize (run_op_TSO_eq _ run2 H); crush.
  Qed.

  Lemma update_mem_TSO_eq: forall m1 ops m2, update_mem_TSO m1 ops m2 -> forall m1' m2', TSO_mem_eq m1 m1' -> TSO_mem_eq m2 m2' ->
    update_mem_TSO m1' ops m2'.
  Proof.
    intros m1 ops m2 H; induction H; intros.
      apply no_ops_TSO; auto.
        transitivity m; [symmetry | transitivity m']; assumption.
      specialize (run_op_TSO_eq _ H1 H3); crush.
        eapply no_atomic_TSO; eauto.
      eapply atomic_TSO; eauto; crush.
        unfold TSO_mem_eq in H3; unfold TSO_mem_beq in H3; repeat crush_if.
          rewrite e0 in H; auto.
        unfold TSO_mem_eq in H3; unfold TSO_mem_beq in H3; repeat crush_if.
          setoid_rewrite e1 in H1; eapply H1; eauto.
        unfold TSO_mem_eq in *; unfold TSO_mem_beq in *; repeat crush_if.
          false; apply n; etransitivity; eauto; etransitivity; eauto; symmetry; auto.
          false; apply n; etransitivity; eauto; etransitivity; eauto; symmetry; auto.
          false; apply n; etransitivity; eauto; etransitivity; eauto; apply NatMap.F.F.add_m; symmetry; auto.
      unfold TSO_mem_eq in H1; unfold TSO_mem_beq in H1; repeat crush_if; eapply buffers_TSO.
        rewrite <- e1; eauto.
        apply IHupdate_mem_TSO; auto.
          unfold TSO_mem_eq; unfold TSO_mem_beq; repeat crush_if.
            false; apply n; rewrite e1; reflexivity.
            false; apply n; rewrite e; reflexivity.
  Qed.        
   
  Instance update_mem_TSO_proper: Proper (TSO_mem_eq ==> eq ==> TSO_mem_eq ==> iff) update_mem_TSO.
  Proof.
    unfolds; unfolds; intros; split; intro; subst. 
      eapply update_mem_TSO_eq; eauto.
      symmetry in H; symmetry in H1; eapply update_mem_TSO_eq; eauto.
  Qed.

Instance TSO : Memory_Model TSO_mem string nat const Z := 
  { update_mem := update_mem_TSO; initial_mem := init_mem_TSO }.

End TSO.

Module TSO_Mem_Dec <: Equalities.DecidableType.
  Definition t := TSO_mem.
  Definition eq := TSO_mem_eq.
  Definition eq_dec := TSO_mem_eq_dec.
  Definition eq_equiv := TSO_mem_eq_equiv.
End TSO_Mem_Dec.
Module TSO_MemSet := MSet' TSO_Mem_Dec.
Definition TSO_mem_set := TSO_MemSet.t.

Definition is_nil {A : Set} (l : list A) := if eq_nat_dec (List.length l) 0 then true else false.
Lemma is_nil_spec: forall (A : Set) (l : list A), is_nil l = true <-> l = [].
Proof.
  unfold is_nil; crush; crush_if.
  destruct l; simpl in e; auto; discriminate.
Qed.
Hint Rewrite is_nil_spec.

Section TSO_impl.
(* Executable implementation of TSO *)
  
  Lemma update_TSO_self: forall m, update_mem_TSO m [] m.
  Proof.
    intros; apply no_ops_TSO; auto; reflexivity.
  Qed.
  Hint Resolve update_TSO_self.

  Fixpoint clear_buffer (mmap : nat_map const) buf :=
    match buf with
    | [] => mmap
    | (l, v)::rest => clear_buffer (NatMap.add l v mmap) rest
    end.

  Definition clear_buffers m := StringMap.fold
    (fun t buf m => (clear_buffer (sm m) (rev buf), fs m,
            StringMap.add t [] (wb m))) (wb m) m.
  
  Lemma update_trans: forall m ops m' ops' m'', (forall t l v v', ~ In (ARW t l v v') ops) -> 
    (forall t l v v', ~ In (ARW t l v v') ops') -> update_mem_TSO m ops m' ->
    update_mem_TSO m' ops' m'' -> update_mem_TSO m (ops ++ ops') m''.
  Proof.
    intros ? ? ? ? ? ops1 ops2 H; induction H; crush.
      eapply update_mem_TSO_eq; eauto; crush.
      eapply no_atomic_TSO; crush.
        rewrite in_app_iff in H0; crush.
          eapply H; rewrite in_app_iff; left; eauto.
          rewrite in_app_iff in H0; crush.
            eapply H; rewrite in_app_iff; right; crush; right; eauto.
            eapply ops2; eauto.
        apply IHupdate_mem_TSO; auto.
          intros; eapply H; rewrite in_app_iff in *; crush.
            left; eauto.
            right; right; eauto.
      false; eapply ops1; left; eauto.
      eapply buffers_TSO; eauto.
  Qed.

  Lemma add_twice: forall (A : Set) k (v v' : A) m, StringMap.Equal (StringMap.add k v (StringMap.add k v' m))
    (StringMap.add k v m).
  Proof.
    unfold StringMap.Equal; intros; rewrite StringMap.F.F.add_o; crush_if.
      rewrite StringMap.F.F.add_eq_o; auto.
      repeat (rewrite StringMap.F.F.add_neq_o; auto).
  Qed.
  Hint Rewrite add_twice.

  Import List.

  Lemma update_buffer: forall t buf' m buf, StringMap.find t (wb m) = Some (buf ++ rev buf') -> 
    update_mem_TSO m [] (clear_buffer (sm m) buf', fs m, StringMap.add t buf (wb m)).
  Proof.
    induction buf'; crush.
      rewrite app_nil_r in H; apply no_ops_TSO; auto.
        unfold TSO_mem_eq; unfold TSO_mem_beq; repeat crush_if.
        false; apply n; unfold StringMap.Equal; intro.
        rewrite StringMap.F.F.add_o.
        destruct (StringMap.MSet.F.eq_dec t y); crush.
      eapply buffers_TSO.
        instantiate (3 := buf ++ rev buf'); crush; eauto.
        specialize (IHbuf' (NatMap.add a0 b (sm m), fs m, StringMap.add t (buf ++ rev buf') (wb m)));
          simpl in IHbuf'.
          specialize (IHbuf' buf).
          generalize (add_twice t buf (buf ++ rev buf') (wb m)); intro.
          eapply (update_mem_TSO_eq(m1 := (NatMap.add a0 b (sm m), fs m, StringMap.add t (buf ++ rev buf') (wb m)))).
            apply IHbuf'; rewrite StringMap.F.F.add_eq_o; auto.
            reflexivity.
            unfold TSO_mem_eq; unfold TSO_mem_beq; simpl.
              destruct (nat_const_map_eq_dec (clear_buffer (NatMap.add a0 b (sm m)) buf')
                (clear_buffer (NatMap.add a0 b (sm m)) buf')).
                destruct (NatSet.eq_dec (fs m) (fs m)).
                  crush_if.
                false; apply n; reflexivity.
              false; apply n; reflexivity.
  Qed.

  Lemma update_buffer_all: forall t buf m, StringMap.find t (wb m) = Some buf -> 
    update_mem_TSO m [] (clear_buffer (sm m) (rev buf), fs m, StringMap.add t [] (wb m)).
  Proof.
    intros; apply update_buffer; simpl.
      rewrite rev_involutive; auto.
  Qed.

  Definition find_buf t m := StringMap.find t (wb m).

  Lemma update_buffers: StringMap.fold
    (fun t buf m => (clear_buffer (sm m) (rev buf), fs m,
            StringMap.add t [] (wb m))) bufs m.
StringMap.find t m = Some buf -> StringMap.find bufs t m = Some buf \/ 
  StringMap.find (wb (fold)) t = Some [].

  Lemma update_buffers: forall m, update_mem_TSO m [] (clear_buffers m) /\
    forall t buf, find_buf t m = Some buf -> StringMap.find t (wb (clear_buffers m)) = Some buf 
      \/ StringMap.find t (wb (clear_buffers m)) = Some [].
  Proof.
    unfold clear_buffers; intros; apply StringMap.F.fold_rec; crush.
      eapply (update_trans(m := m)(ops := [])(m' := a)); auto.
        apply update_buffer_all.
        apply StringMap.Map.find_1; auto.
        unfold find_buf in H4; rewrite StringMap.F.F.find_mapsto_iff in *.
        specialize (H4 
  Qed.
    
  Fixpoint update_mem_TSO_fun m (ops : list LLVM_access) : option TSO_mem :=
  match ops with
  | [] => Some m
  | [ARW t l v v'] => if NatSet.mem l (fs m) then None else
    let m' = clear_buffers m in Some (NatMap.add l v' (sm m'), fs m', wb m')    
  | a::ops' => if forallb not_atomic ops
    then match run_op_TSO m a with
                       | Some m'' => update_mem_TSO_fun m'' ops'
                       | None => None
                       end
    else None
  end.

  Lemma update_TSO_fun_sound: forall ops m m', update_mem_TSO_fun m ops = Some m' ->
    update_mem_TSO m ops m'.
  Proof.
    induction ops; crush.
      destruct a; repeat crush_if.
        eapply no_atomic_TSO.
          rewrite forallb_forall in c0; crush.
            specialize (c0 _ H2); simpl in *; discriminate.
          instantiate (3 := []); simpl; auto.
          simpl; rewrite H0; crush_if.
          simpl; auto.
        eapply no_atomic_TSO.
          rewrite forallb_forall in c0; crush.
            specialize (c0 _ H0); simpl in *; discriminate.
          instantiate (3 := []); simpl; auto.
          simpl; crush_if.
          simpl; auto.
        (*crush_if; eapply atomic_TSO; eauto.
          rewrite NatSet.F.not_mem_iff; eauto.
          reflexivity.*)skip.
        eapply no_atomic_TSO.
          rewrite forallb_forall in c; crush.
            specialize (c _ H0); simpl in *; discriminate.
          instantiate (3 := []); simpl; auto.
          simpl; crush_if.
          simpl; auto.
        eapply no_atomic_TSO.
          rewrite forallb_forall in c; crush.
            specialize (c _ H0); simpl in *; discriminate.
          instantiate (3 := []); simpl; auto.
          simpl; crush_if.
          simpl; auto.
        eapply no_atomic_TSO.
          rewrite forallb_forall in c; crush.
            specialize (c _ H0); simpl in *; discriminate.
          instantiate (3 := []); simpl; auto.
          simpl; crush_if.
          simpl; auto.
  Qed.

  Definition get_free_TSO (m : TSO_mem) (_ : string) := NatSet.choose (snd m).
  Definition cast_TSO (m : TSO_mem) (_ : string) l := Some (Z.of_nat l).

  Instance TSO_impl : MM_impl TSO := 
  { update_mem_fun := update_mem_TSO_fun; read := read_TSO; get_free := get_free_TSO;
    cast := cast_TSO }.
  Proof.
    unfold read_TSO; crush; exists m; eapply no_atomic_TSO; crush.
      instantiate (1 := []); instantiate (2 := []); simpl; auto.
      simpl; setoid_rewrite H; crush_if.
      simpl; auto.
    unfold get_free_TSO; crush; eexists; eapply no_atomic_TSO; crush.
      instantiate (1 := []); instantiate (2 := []); simpl; auto.
      generalize (NatSet.choose_spec1 H); rewrite <- NatSet.mem_spec; intro; simpl.
        setoid_rewrite H0; auto.
      simpl; auto.
    unfold cast_TSO; crush; exists m; eapply no_atomic_TSO; crush.
      instantiate (1 := []); instantiate (2 := []); simpl; auto.
      simpl; crush_if.
        generalize (Z.eqb_refl (Z.of_nat l)); intro; contr.
      simpl; auto.
    intros; apply update_TSO_fun_sound; auto.
  Defined.

End TSO_impl.
        
Recursive Extraction update_mem_TSO_fun step_fun.

(* No fairness, scheduling determined by the implementation of FMap.elements. *)
Definition conc_step_fun_TSO tG gt C m :=
  match StringMap.elements C with
  | nil => None
  | (t, c)::rest => 
    match StringMap.find t tG with
    | None => None
    | Some G => 
      match step_fun G TSO_impl t m gt c with
      | None => None
      | Some (ops, c') => 
        match update_mem_TSO_fun m ops with
        | None => None
        | Some m' => Some (StringMap.add t c' C, m')
        end
      end
    end
  end.
    
Recursive Extraction conc_step_fun_TSO.

Lemma conc_step_fun_TSO_sound: forall tG gt C m C' m', conc_step_fun_TSO tG gt C m = Some (C', m') ->
  conc_step TSO tG gt (C, m) (C', m').
Proof.
  unfold conc_step_fun_TSO; intros.
    destruct (StringMap.elements C) eqn: Cs; try discriminate.
    repeat (destruct p).
    repeat (rewrite must_be_Some in *; crush).
    destruct x0.
    rewrite must_be_Some in *; crush.
    eapply step_thread.
      eapply StringMap.find_2; eauto.
      eapply StringMap.elements_2; setoid_rewrite Cs; constructor; reflexivity.
      eapply step_fun_sound; eauto.
      unfold update_mem; unfold TSO; apply update_TSO_fun_sound; auto.
      unfold StringMap.F.Add; auto.
Qed.

Recursive Extraction conc_step_fun_TSO.