Require Import CpdtTactics.
Require Import List.
Require Import Util.
Require Import CoqEqDec.
Import ListNotations.
Import Bool.
Import Equalities.
Require Import Coqlib.
Import CoqEqDec.

Set Implicit Arguments.

(*Section Memory_Model.
  Variables (thread loc val concrete_ptr : Type).
  Context {Loc : EqDec_eq loc} (Val : EqDec_eq val).
  
  (* preliminaries *)
  Inductive access : Type :=
  | Read : thread -> loc -> val -> access
  | Write : thread -> loc -> val -> access
  | ARW : thread -> loc -> val -> val -> access
  | Alloc : thread -> loc -> access
  | Free : thread -> loc -> access
  | Cast : thread -> loc -> concrete_ptr -> access.

  Definition not_atomic a := match a with
  | ARW _ _ _ _ => false
  | _ => true
  end.

  Definition get_thread a := match a with
  | Read t _ _ => t
  | Write t _ _ => t
  | ARW t _ _ _ => t
  | Alloc t _ => t
  | Free t _ => t
  | Cast t _ _ => t
  end.

  Definition get_loc a := match a with
  | Read _ l _ => l
  | Write _ l _ => l
  | ARW _ l _ _ => l
  | Alloc _ l => l
  | Free _ l => l
  | Cast _ l _ => l
  end.

  Definition reads a l := match a with
  | Read _ l' _ => if eq_dec l l' then true else false
  | ARW _ l' _ _ => if eq_dec l l' then true else false
  | _ => false
  end.

  Definition reads_val a l v := match a with
  | Read _ l' v' => if eq_dec l l' then if eq_dec v v' then true else false else false
  | ARW _ l' v' _ => if eq_dec l l' then if eq_dec v v' then true else false else false
  | _ => false
  end.

  Definition writes a l := match a with
  | Write _ l' _ => if eq_dec l l' then true else false
  | ARW _ l' _ _ => if eq_dec l l' then true else false
  | _ => false
  end.

  Definition writes_val a l v := match a with
  | Write _ l' v' => if eq_dec l l' then if eq_dec v v' then true else false else false
  | ARW _ l' _ v' => if eq_dec l l' then if eq_dec v v' then true else false else false
  | _ => false
  end.

  Definition modifies a l := match a with
  | Write _ l' _ => if eq_dec l l' then true else false
  | ARW _ l' _ _ => if eq_dec l l' then true else false
  | Alloc _ l' => if eq_dec l l' then true else false
  | Free _ l' => if eq_dec l l' then true else false
  | _ => false
  end.

  Definition is_cast a := match a with Cast _ _ _ => true | _ => false end.

(*Module MM_Prelim (Thread : Typ) (Loc : UsualDecidableType) (Val : UsualDecidableType) (CPtr : Typ).
  Definition thread := Thread.t.
  Definition loc := Loc.t.
  Definition val := Val.t.
  Definition concrete_ptr := CPtr.t.

  ...

End MM_Prelim.*)

  Variable mem : Type.

  Class Memory_Model_Base := { apply_access : mem -> access -> mem -> Prop;
    initial_mem : mem -> bool }.

  (* record-keeping for cast *)
  Record mem_state := 
    { mrep : mem; acs : list (loc * concrete_ptr); fcs : list (loc * concrete_ptr) }.
  Coercion mrep : mem_state >-> mem.

  Definition apply_cast acs fcs a :=
    match a with
    | Cast t l p => if existsb (fun e => if eq_dec (fst e) l then true else false) acs then (acs, fcs) else ((l, p)::acs, fcs)
    | Free t l => let (a, b) := partition (fun e => if eq_dec (fst e) l then true else false) acs in
        (b, a ++ fcs)
    | _ => (acs, fcs)
    end.

  (* Derived functions used to state memory model axioms *)
  Context {MM_base : Memory_Model_Base}.

  Inductive apply_access' (m : mem_state) (a : access) (m' : mem_state) : Prop :=
  | apply' : forall (Happly : apply_access m a m') (Hcast : apply_cast (acs m) (fcs m) a = (acs m', fcs m')),
      apply_access' m a m'.
  Hint Constructors apply_access'.

  Inductive update_mem m : list access -> mem_state -> Prop :=
  | update_nil : update_mem m [] m
  | update_one : forall a m' ops1 ops2 m'' (Happly : apply_access' m a m') (Htrans : update_mem m' (ops1 ++ ops2) m''),
      update_mem m (ops1 ++ a :: ops2) m''.
  Hint Immediate update_nil.

  Lemma update_single_iff : forall m a m', update_mem m [a] m' <->
    apply_access' m a m'.
  Proof.
    intros; split; intro.
    - inversion H; clarify.
      destruct ops1; clarify.
      inversion Htrans; clarify.
      destruct ops1; clarify.
      destruct ops1; clarify.
    - apply (update_one [] [] H); clarify.
  Qed.

  Lemma update_trans : forall m ops m' (Hupdate1 : update_mem m ops m')
    ops' m'' (Hupdate2 : update_mem m' ops' m''), update_mem m (ops ++ ops') m''.
  Proof.
    intros ? ? ? ?; induction Hupdate1; intros; simpl; auto.
    rewrite <- app_assoc; eapply update_one; eauto.
    rewrite app_assoc; auto.
  Qed.

  Definition can_do m a := exists m', apply_access' m a m'.

  Lemma can_do_a : forall m a m', apply_access' m a m' -> can_do m a.
  Proof. unfold can_do; eauto. Qed.

  Lemma can_do_apply : forall (m : mem_state) a m', apply_access m a m' -> can_do m a.
  Proof.
    intros; destruct (apply_cast (acs m) (fcs m) a) eqn: cast.
    unfold can_do; eexists {| mrep := m' |}; constructor; eauto.
  Qed.

  Lemma can_do_apply_iff : forall (m : mem_state) a, can_do m a <->
    exists m', apply_access m a m'.
  Proof.
    split; clarify.
    - destruct H; inversion H; eauto.
    - eapply can_do_apply; eauto.
  Qed.

  Definition private m t l := exists m0, initial_mem m0 = true /\ 
    exists ops, Forall (fun a => get_loc a = l -> get_thread a = t) ops /\ update_mem {| mrep := m0; acs := []; fcs := [] |} ops m.
  Definition private_a m a := private m (get_thread a) (get_loc a).

(*Module Type Memory_Model_Base (Mem : Typ) (Thread : Typ) (Loc : UsualDecidableType) (Val : UsualDecidableType) (CPtr : Typ).
  Include MM_Prelim Thread Loc Val CPtr.
  Definition mem := Mem.t.

  ...

End Memory_Model_Base.*)

  (* Memory model typeclass *)
  Class Memory_Model := { 
    private_diff_loc : forall m a a' m' (Hprivate : private_a m a) (Hdiff_loc : get_loc a' <> get_loc a)
      (Happly : apply_access' m a' m') (Hnot_cast : is_cast a = false), can_do m a <-> can_do m' a;
    cast_active : forall m l p t (Hin_acs : In (l, p) (acs m)) p', can_do m (Cast t l p') <-> p' = p;
    cast_inactive : forall m l p t (Hin_fcs : In (l, p) (fcs m)) p', can_do m (Cast t l p') -> p' = p;
    private_read_noop : forall m t l v m' a (Hprivate : private_a m a) (Hread : apply_access' m (Read t l v) m'),
      can_do m a <-> can_do m' a;
    private_cast_noop : forall m t l p m' a (Hprivate : private_a m a) (Hcast : apply_access' m (Cast t l p) m')
      (Hnot_cast : is_cast a = false), can_do m a <-> can_do m' a;
    private_read_written : forall m t l v a m' a' (Hprivate : private m t l) (Hthread : get_thread a = t) 
      (Hwrites : writes_val a l v = true) (Happly : apply_access' m a m') (Hthread' : get_thread a' = t)
      (Hread : reads a' l = true), can_do m' a' <-> reads_val a' l v = true;
    private_not_mod_write : forall m t l v a m' (Hprivate : private m t l) (Hnot_mod : modifies a l = false) 
      (Happly : apply_access' m a m'), can_do m (Write t l v) <-> can_do m' (Write t l v);
    private_alloc_write : forall m t l v m' (Hprivate : private m t l) (Halloc : apply_access' m (Alloc t l) m'),
      can_do m' (Write t l v);
    private_free_rw : forall m t l a m' (Hprivate : private m t l) (Hfree : apply_access' m (Free t l) m')
      (Hthread : get_thread a = t) (Hrw : reads a l = true \/ writes a l = true), ~can_do m' a;
    private_alloc_free : forall m t l m' (Hprivate : private m t l) (Halloc : apply_access' m (Alloc t l) m'),
      can_do m' (Free t l);
    private_alloc_alloc : forall m t l m' (Hprivate : private m t l) (Halloc : apply_access' m (Alloc t l) m'),
      ~can_do m' (Alloc t l);
    private_free_free : forall m t l m' (Hprivate : private m t l) (Hfree : apply_access' m (Free t l) m'),
      ~can_do m' (Free t l);
    private_free_alloc : forall m t l m' (Hprivate : private m t l) (Hfree : apply_access' m (Free t l) m'),
      can_do m' (Alloc t l);
    private_write_not_read : forall m t l v m' a (Hprivate : private_a m a) (Hwrite : apply_access' m (Write t l v) m')
      (Hnot_read : reads a l = false), can_do m a <-> can_do m' a;
    private_ARW_not_read : forall m t l v v' m' a (Hprivate : private_a m a) (HARW : apply_access' m (ARW t l v v') m')
      (Hnot_read : reads a l = false), can_do m a <-> can_do m' a;
    private_alloc_cast : forall m t l m' p (Hprivate : private m t l) (Halloc : apply_access' m (Alloc t l) m'),
      can_do m (Cast t l p) <-> can_do m' (Cast t l p);
    (* Why should alloc not enable casting? *)
    private_free_cast : forall m t l m' p (Hprivate : private m t l) (Hfree : apply_access' m (Free t l) m')
      (Hno_addr : ~In (l, p) (acs m ++ fcs m)), can_do m (Cast t l p) <-> can_do m' (Cast t l p);
    ARW_reads : forall m t l v v', can_do m (ARW t l v v') -> can_do m (Read t l v) }.
  (* Is the cast in the other direction also a memory operation? *)

  Context (MM : Memory_Model).
  Lemma cast_activate: forall m t l p m', apply_access' m (Cast t l p) m' -> In (l, p) (acs m').
  Proof.
    intros; inversion H; clarify.
    assert (exists p', In (l, p') (acs m)) as l_in.
    { rewrite existsb_exists in *; clarify; destruct x; eexists; eauto. }
    generalize (cast_active m); intro active; clarify.
    specialize (active _ _ t l_in p).
    assert (p = x); subst; auto.
    rewrite <- active.
    exists m'; constructor; clarify.
  Qed.
  
(*Module Type Memory_Model (Mem : Typ) (Thread : Typ) (Loc : UsualDecidableType) (Val : UsualDecidableType) (CPtr : Typ).
  Include Memory_Model_Base Mem Thread Loc Val CPtr.
  
  ...

End Memory_Model.*)

  (* determinize guessed arguments *)
  Class MM_impl := { 
    read : mem_state -> thread -> loc -> option val;
    get_free : mem_state -> thread -> option loc;
    cast : mem_state -> thread -> loc -> option concrete_ptr;
    apply_access_fun : mem -> access -> option mem;
    read_correct : forall m t l v (Hread : read m t l = Some v), can_do m (Read t l v);
    get_free_correct : forall m t l (Hfree : get_free m t = Some l), can_do m (Alloc t l);
    cast_correct : forall m t l p (Hcast : cast m t l = Some p), can_do m (Cast t l p);
    apply_correct : forall m a m' (Happly : apply_access_fun m a = Some m'), apply_access m a m' }.

  Context (MM_exec : MM_impl).

  Fixpoint update_mem_fun (m : mem_state) ops := match ops with
  | [] => Some m
  | a :: rest => match apply_access_fun (mrep m) a with
               | Some m' => let (acs', fcs') := apply_cast (acs m) (fcs m) a in 
                   update_mem_fun {| mrep := m'; acs := acs'; fcs := fcs'|} rest
               | None => None
               end
  end.

  Lemma update_mem_correct : forall ops m m', 
    update_mem_fun m ops = Some m' -> update_mem m ops m'.
  Proof.
    induction ops; clarify.
    destruct (apply_access_fun (mrep m) a) eqn: apply; try discriminate;
      generalize (apply_correct _ _ apply); clarify.
    destruct (apply_cast (acs m) (fcs m) a) eqn: cast; exploit IHops; eauto;
      intro.
    eapply (update_one(m' := {| mrep := x |}) [] _); clarify; eauto.
  Qed.

End Memory_Model.
Arguments Read [thread] [loc] [val] [concrete_ptr] _ _ _.
Arguments Write [thread] [loc] [val] [concrete_ptr] _ _ _.
Arguments ARW [thread] [loc] [val] [concrete_ptr] _ _ _ _.
Arguments Alloc [thread] [loc] [val] [concrete_ptr] _ _.
Arguments Free [thread] [loc] [val] [concrete_ptr] _ _.
Arguments Cast [thread] [loc] [val] [concrete_ptr] _ _ _.
Arguments not_atomic {thread} {loc} {val} {concrete_ptr} _.
Hint Constructors apply_access'.
Hint Immediate update_nil.

Section MM_Similar.
  Variables (mem mem' thread loc val concrete_ptr : Type).
  Context (Loc : EqDec_eq loc) (Val : EqDec_eq val) 
          (CPtr : EqDec_eq concrete_ptr).
  Context (MM_base : Memory_Model_Base thread loc val concrete_ptr mem)
          (MM_base' : Memory_Model_Base thread loc val concrete_ptr mem').
  Context (MM : Memory_Model(mem := mem) Val) 
          (MM' : Memory_Model(mem := mem') Val).

  Definition in_cs_dec: forall (l : loc) (p : concrete_ptr) fs, {In (l, p) fs} + {~In (l, p) fs}.
  Proof. intros; apply in_dec; decide equality. Defined.

  Inductive similar_interface (m : mem_state loc concrete_ptr mem) (m' : mem_state loc concrete_ptr mem') t l : Prop := 
  | same_ops : (forall a (Hthread : get_thread a = t) (Hloc : get_loc a = l),
    ((forall p, In (l, p) (acs m) <-> In (l, p) (acs m')) /\
    (forall p, In (l, p) (fcs m) <-> In (l, p) (fcs m'))) /\
    (can_do m a <-> can_do m' a)) -> similar_interface m m' t l.

  (* What does it mean for two memory models to "have the same non-concurrent behavior"?
     Can we separate into concurrent and non-concurrent aspects? How? *)
  (* These hypotheses might be a starting point. *)
  Hypothesis same_alloc_read : forall (m m2 : mem_state loc concrete_ptr mem) 
    (m' m2' : mem_state loc concrete_ptr mem') (t t' : thread) (l l' : loc) (v : val)
    (Halloc : apply_access' m (Alloc t l) m2) (Halloc' : apply_access' m' (Alloc t' l') m2'),
    can_do m2 (Read t l v) <-> can_do m2' (Read t' l' v).
  Hypothesis same_alloc_ARW : forall (m m2 : mem_state loc concrete_ptr mem) 
    (m' m2' : mem_state loc concrete_ptr mem') (t t' : thread) (l l' : loc) (v v' : val)
    (Halloc : apply_access' m (Alloc t l) m2) (Halloc' : apply_access' m' (Alloc t' l') m2'),
    can_do m2 (ARW t l v v') <-> can_do m2' (ARW t' l' v v').
  Hypothesis same_cast_inactive : forall (m : mem_state loc concrete_ptr mem) 
    (m' : mem_state loc concrete_ptr mem') (t : thread) (l : loc) (p : concrete_ptr)
    (Hin_fcs : In (l, p) (fcs m)) (Hin_fcs' : In (l, p) (fcs m')), can_do m (Cast t l p) <-> can_do m' (Cast t l p).

  Lemma similar_apply: forall m m' t l a m2 (Hsim : similar_interface m m' t l)
    (Hprivate : private m t l) (Hprivate' : private m' t l)
    (Hthread : get_thread a = t) (Hloc : get_loc a = l) (Happly : apply_access' m a m2),
    exists m2', apply_access' m' a m2' /\ similar_interface m2 m2' t l.
  Proof.
    intros; inversion Hsim.
    generalize (H _ Hthread Hloc); intro X; destruct X as [[Hacs Hfcs] [Hm' _]].
    specialize (Hm' (can_do_a Happly)); unfold can_do in Hm'; crush.
    eexists; split; eauto; constructor; intros.
    destruct a; simpl in *.
    - (* Read *)
      rewrite <- private_read_noop; eauto; try (unfold private_a; clarify; fail).
      rewrite <- (private_read_noop(m := m')); eauto; unfold private_a; clarify.
      inversion Happly; inversion H0; clarify.
    - (* Write *)
      destruct (reads a0 l) eqn: reads.
      + rewrite (private_read_written(a := Write t l v) v _ Hprivate); eauto; try (clarify; fail).
        rewrite (private_read_written(a := Write t l v) v _ Hprivate'); eauto; clarify.
        inversion Happly; inversion H0; clarify; crush.
      + rewrite <- private_write_not_read; eauto; try (unfold private_a; clarify; fail).
        rewrite <- (private_write_not_read(m := m')); eauto; unfold private_a; clarify.
        inversion Happly; inversion H0; clarify; crush.
    - (* ARW *)
      destruct (reads a0 l) eqn: reads.
      + rewrite (private_read_written(a := ARW t l v v0) v0 _ Hprivate); eauto; try (clarify; fail).
        rewrite (private_read_written(a := ARW t l v v0) v0 _ Hprivate'); eauto; clarify.
        inversion Happly; inversion H0; clarify; crush.
      + rewrite <- private_ARW_not_read; eauto; try (unfold private_a; clarify; fail).
        rewrite <- (private_ARW_not_read(m := m')); unfold private_a; clarify; eauto.
        inversion Happly; inversion H0; clarify; crush.
    - (* Alloc *)
      inversion Happly; inversion H0; clarify.
      destruct a0; simpl in *; subst.
      + eapply same_alloc_read; eauto.
      + split; intro; eapply private_alloc_write; eauto.
      + split; eapply same_alloc_ARW; eauto.
      + generalize (private_alloc_alloc(m' := x) Hprivate'); generalize (private_alloc_alloc(m' := m2) Hprivate);
          crush.
      + split; intro; eapply private_alloc_free; eauto.
      + rewrite <- private_alloc_cast; eauto.
        rewrite <- (private_alloc_cast c Hprivate'); eauto.
    - (* Free *)
      inversion Happly; inversion H0; clarify.
      destruct (partition (fun e => if eq_dec (fst e) (get_loc a0) then true else false) (acs m)) eqn: part;
        destruct (partition (fun e => if eq_dec (fst e) (get_loc a0) then true else false) (acs m')) eqn: part'; clarify.
      split; [split; intro |].
      + generalize (partition_In2 (get_loc a0, p) (fun e => if eq_dec (fst e) (get_loc a0) then true else false) (acs m)); rewrite part; simpl.
        generalize (partition_In2 (get_loc a0, p) (fun e => if eq_dec (fst e) (get_loc a0) then true else false) (acs m')); rewrite part'; simpl;
          intros Hin1 Hin2.
        rewrite Hin1; rewrite <- Hacs; rewrite <- Hin2; reflexivity.
      + generalize (partition_In1 (get_loc a0, p) (fun e => if eq_dec (fst e) (get_loc a0) then true else false) (acs m)); rewrite part; simpl. 
        generalize (partition_In1 (get_loc a0, p) (fun e => if eq_dec (fst e) (get_loc a0) then true else false) (acs m')); rewrite part'; simpl;
          intros Hin1 Hin2.
        repeat (rewrite in_app_iff); rewrite Hin1; rewrite Hfcs; rewrite Hin2; rewrite Hacs; reflexivity.
      + destruct (reads a0 (get_loc a0) || writes a0 (get_loc a0)) eqn: rw; [rewrite orb_true_iff in * | rewrite orb_false_iff in *].
        generalize (private_free_rw(a := a0)(m' := m2) Hprivate); 
        generalize (private_free_rw(a := a0)(m' := x) Hprivate'); clarify.
        { split; intro; contradiction. }
        destruct a0; clarify; try (crush; fail).
        { generalize (private_free_alloc(m' := m2) Hprivate); generalize (private_free_alloc(m' := x) Hprivate'); clarify.
          split; auto. }
        { generalize (private_free_free(m' := m2) Hprivate); generalize (private_free_free(m' := x) Hprivate'); clarify.
          split; intro; contradiction. }
        destruct (find (fun e => if eq_dec (fst e) l0 then true else false) (l ++ fcs m)) eqn: inactive.
        * generalize (find_success _ _ _ inactive); clarify.
          destruct p; clarify.
          assert (In (l0, c0) (l1 ++ fcs m')).
          rewrite in_app_iff in *; destruct H1; [left | right]; crush.
          generalize (partition_In1 (l0, c0) (fun e => if eq_dec (fst e) l0 then true else false) (acs m)); setoid_rewrite part; simpl.
          generalize (partition_In1 (l0, c0) (fun e => if eq_dec (fst e) l0 then true else false) (acs m')); setoid_rewrite part'; simpl;
            intros Hin1 Hin2.
          clarify.
          rewrite Hin1; rewrite Hin2 in H; crush.
          rewrite <- Hacs; auto.
          rewrite <- Hfcs; auto.
          generalize (cast_inactive(m := m2)(l := l0) c0);
            generalize (cast_inactive(m := x)(l := l0) c0); intros cast1 cast2; clarify.
          
          rewrite H3 in *; rewrite H5 in *.
          exploit same_cast_inactive; eauto; intro same_cast.
          split; intro Hp.
          exploit cast2; eauto; clarify; rewrite <- same_cast; auto.
          exploit cast1; eauto; clarify; rewrite same_cast; auto.
        * (* never before cast *)
          autorewrite with core in *; clarify.
          assert (~ In (l0, c) (acs m ++ fcs m)).
          { unfold not; rewrite in_app_iff; intro in_cs; destruct in_cs as [Hin | Hin].
            generalize (partition_In1 (l0, c) (fun e => if eq_dec (fst e) l0 then true else false) (acs m)); rewrite part; intros [_ Ha].
            generalize (find_succeeds (fun e => if eq_dec (fst e) l0 then true else false) _ _ Hin); clarify.
            generalize (find_succeeds (fun e => if eq_dec (fst e) l0 then true else false) _ _ Ha); clarsimp.
            generalize (find_succeeds (fun e => if eq_dec (fst e) l0 then true else false) _ _ Hin); clarsimp. }
          rewrite <- private_free_cast; eauto.
          rewrite <- (private_free_cast c Hprivate'); eauto.
          clarify; rewrite in_app_iff; intros [? | ?].
          rewrite in_app_iff in *; rewrite <- Hacs in *; auto.
          rewrite in_app_iff in *; rewrite <- Hfcs in *; auto.
    - (* Cast *)
      split.
      + inversion Happly; inversion H0; clarify.
        destruct (existsb (fun e => if eq_dec (fst e) (get_loc a0) then true 
          else false) (acs m)) eqn: ex; 
        [|destruct (existsb (fun e => if eq_dec (fst e) (get_loc a0) then true 
          else false) (acs m')) eqn: ex']; try (rewrite existsb_exists in * ); 
          clarify.
        * destruct x0; clarify.
          rewrite Hacs in *.
          generalize (existsb_exists (fun e => if eq_dec (fst e) (get_loc a0) 
            then true else false) (acs m')); intros [_ ex']; use ex';
          [rewrite ex' in cond; discriminate |].
          eexists; split; eauto 2; clarify.
        * destruct x0; clarify.
          rewrite <- Hacs in *.
          generalize (existsb_exists (fun e => if eq_dec (fst e) (get_loc a0) 
            then true else false) (acs m)); intros [_ ex2]; use ex2;
            [rewrite ex2 in ex; discriminate |].
          eexists; split; eauto 2; clarify.
        * setoid_rewrite Hacs; reflexivity.
      + destruct (is_cast a0) eqn: cast.
        * generalize (cast_activate _ Happly); generalize (cast_activate _ H0);
            intros.
          destruct a0; clarify.
          generalize (cast_active m2 l c t); 
            generalize (cast_active x l c t); intros cast1 cast2; clarify.
          specialize (cast1 c0); specialize (cast2 c0); crush.
        * rewrite <- private_cast_noop; eauto; try (unfold private_a; clarify; fail).
          rewrite <- (private_cast_noop(m := m')); eauto; unfold private_a; clarify.
  Qed.
  (* We really need errors. *)

  (* Angle 1: general simulation *)
(*  Hypothesis similar1: forall p q p', R p q -> p -ops-> p' -> exists q', q -ops-> q' /\ R p' q'.*)


End MM_Similar.

(*Module MM_Similar (Mem : Typ) (Mem' : Typ) (Thread : Typ) (Loc : UsualDecidableType) (Val : UsualDecidableType) (CPtr : UsualDecidableType).
  Module MM_pre := MM_Prelim Thread Loc Val CPtr.
  Import MM_pre.
  Declare Module MM : Memory_Model Mem Thread Loc Val CPtr.
  Declare Module MM' : Memory_Model Mem' Thread Loc Val CPtr.
  (* sharing *)

  ...

End MM_Similar.*)
*)

Lemma in_break: forall A (a : A) l1 l2 x, In a (l1 ++ l2) -> In a (l1 ++ x :: l2).
Proof.
  intros; apply in_or_app; generalize (in_app_or _ _ _ H); crush.
Qed.
Hint Immediate in_break.

(* We have an idea that "memory representation" and "concurrency" should be separate aspects.
   This is an attempt to parameterize by memory layout. *)
Section Layout.
  Variables (mem thread loc val (*concrete_ptr*) : Type).
  Context (loc_eq : EqDec_eq loc).

  (* Reduced accesses sent to memory layout *)
  Inductive mem_op :=
  | MRead : loc -> val -> mem_op
  | MWrite : loc -> val -> mem_op
  | MAlloc : loc -> mem_op
  | MFree : loc -> mem_op.
(*  | MCast : loc -> concrete_ptr -> mem_op.*)

  Definition loc_of op := match op with
  | MRead l _ => l
  | MWrite l _ => l
  | MAlloc l => l
  | MFree l => l
(*  | MCast l _ => l*)
  end.

(*  Definition is_mcast op := match op with
  | MCast _ _ => true
  | _ => false
  end.*)

  Definition op_modifies a l := match a with
  | MWrite l' _ => if eq_dec l l' then true else false
  | MAlloc l' => if eq_dec l l' then true else false
  | MFree l' => if eq_dec l l' then true else false
  | _ => false
  end.

  (* Is there a more fundamental notion of independence hidden here? *)
  Class Memory_Layout := { 
    consistent : list mem_op -> Prop;
    consistent_nil : consistent [];
    consistent_prefix : forall m1 m2, consistent (m1 ++ m2) -> consistent m1;
    loc_comm : forall m1 m2 op1 op2 (Hdiff_loc : loc_of op1 <> loc_of op2),
      consistent (m1 ++ op1 :: op2 :: m2) <-> 
      consistent (m1 ++ op2 :: op1 :: m2);
    loc_valid : forall m op1 op2 (Hdiff_loc : loc_of op1 <> loc_of op2),
      consistent (m ++ [op1; op2]) <-> 
      consistent (m ++ [op1]) /\ consistent (m ++ [op2]);
    read_noop : forall m l v m2 (Hcon : consistent (m ++ [MRead l v])),
      consistent (m ++ MRead l v :: m2) <-> consistent (m ++ m2);
(*    cast_noop : forall m l p op (Hnot_cast : is_mcast op = false)
      (Hcan : can_do_op m (MCast l p) = true), 
      can_do_op (MCast l p :: m) op = can_do_op m op;*)
    read_written : forall m l v v' (Hcon : consistent (m ++ [MWrite l v])),
      consistent (m ++ [MWrite l v; MRead l v']) <-> v' = v;
    (* This one's phrased a bit awkwardly. *)
    write_not_read : forall m l v ops
      (Hnot_read : Forall (fun op => forall v', op <> MRead l v') ops),
      consistent (m ++ MWrite l v :: ops) <-> 
      consistent (m ++ [MWrite l v]) /\ consistent (m ++ ops);
    not_mod_write : forall m l v op (Hnot_mod : op_modifies op l = false)
      (Hcon : consistent (m ++ [op])),
      consistent (m ++ [op; MWrite l v]) <-> consistent (m ++ [MWrite l v]);
    alloc_allows : forall m l (Hcon : consistent (m ++ [MAlloc l])),
      (forall v, consistent (m ++ [MAlloc l; MWrite l v])) /\
      consistent (m ++ [MAlloc l; MFree l]) /\
      ~consistent (m ++ [MAlloc l; MAlloc l]);
    free_allows : forall m l (Hcon : consistent (m ++ [MFree l])),
      (forall v, ~consistent (m ++ [MFree l; MRead l v])) /\
      consistent (m ++ [MFree l; MAlloc l]) /\
      ~consistent (m ++ [MFree l; MFree l]);
    (* is this okay? *)
    base_allows : forall l, (forall v, ~consistent [MRead l v]) /\
      consistent [MAlloc l] /\ ~consistent [MFree l](*;
    alloc_cast : forall m l p (Hcan : can_do_op m (MAlloc l) = true),
      can_do_op (MAlloc l :: m) (MCast l p) = can_do_op m (MCast l p)*)(*;
    free_cast : forall m l m' p (Hfree : do_op m (Free t l) m')
      (Hno_addr : ~In (l, p) (acs m ++ fcs m)), do_op m (Cast t l p) <-> do_op m' (Cast t l p) 
    How do the acs and fcs interact with the layout/concurrent division? 
    They probably belong to the layout. *);
    write_any_value : forall m l v v',
      consistent (m ++ [MWrite l v]) <-> consistent (m ++ [MWrite l v']) }.

  Context {ML : Memory_Layout}.

  Definition can_do_op m op := consistent (m ++ [op]).

  Definition can_do_ops m ops := consistent (m ++ ops).

  Lemma do_one_op : forall m a, can_do_op m a = can_do_ops m [a].
  Proof. unfold can_do_op, can_do_ops; clarify. Qed.

  Lemma loc_comm_ops1 : forall op ops m1 m2 
    (Hdiff_loc : ~In (loc_of op) (map loc_of ops)),
    consistent (m1 ++ op :: ops ++ m2) <-> 
    consistent (m1 ++ ops ++ op :: m2).
  Proof.
    induction ops; clarify; try reflexivity.
    rewrite loc_comm; clarify.
    transitivity (consistent ((m1 ++ [a]) ++ op :: ops ++ m2)).
    - rewrite <- app_assoc; simpl; reflexivity.
    - rewrite IHops; clarify.
      rewrite <- app_assoc; simpl; reflexivity.
  Qed.

  Lemma loc_comm_ops : forall ops ops' m1 m2
    (Hdiff_locs : Forall (fun l => ~In l (map loc_of ops)) (map loc_of ops')),
    consistent (m1 ++ ops ++ ops' ++ m2) <-> 
    consistent (m1 ++ ops' ++ ops ++ m2).
  Proof.
    induction ops; clarify; try reflexivity.
    rewrite <- loc_comm_ops1; clarify.
    transitivity (consistent ((m1 ++ [a]) ++ ops ++ ops' ++ m2)).
    - rewrite <- app_assoc; simpl; reflexivity.
    - rewrite IHops; clarify.
      rewrite <- app_assoc; simpl; reflexivity.
      { rewrite Forall_forall in *; clarify.
        specialize (Hdiff_locs _ H); clarify. }
    - rewrite Forall_forall in *; repeat intro.
      specialize (Hdiff_locs _ H); clarify.
  Qed.

  Lemma loc_valid_ops1 : forall op ops m
    (Hdiff_loc : ~In (loc_of op) (map loc_of ops)),
    consistent (m ++ ops ++ [op]) <->
    consistent (m ++ ops) /\ consistent (m ++ [op]).
  Proof.
    induction ops using rev_ind; clarsimp.
    - split; clarify; eapply consistent_prefix; eauto.
    - rewrite app_assoc, loc_valid.
      repeat rewrite <- app_assoc; rewrite IHops.
      split; clarify; eapply consistent_prefix; rewrite <- app_assoc; eauto.
      { rewrite in_map_iff in *; intro; clarify; apply Hdiff_loc; eexists;
          split; eauto.
        rewrite in_app; clarify. }
      { rewrite in_map_iff in *; intro; apply Hdiff_loc; eexists; split; eauto.
        rewrite in_app; clarify. }
  Qed.

  Lemma loc_valid_ops : forall ops ops' m
    (Hdiff_locs : Forall (fun l => ~In l (map loc_of ops)) (map loc_of ops')),
    consistent (m ++ ops ++ ops') <->
    consistent (m ++ ops) /\ consistent (m ++ ops').
  Proof.
    induction ops; clarsimp.
    - split; clarify; eapply consistent_prefix; eauto.
    - specialize (IHops ops' (m ++ [a])); clarsimp; rewrite IHops.
      assert (~In (loc_of a) (map loc_of ops')) as Hin.
      { rewrite Forall_forall in *; intro; specialize (Hdiff_locs _ H); clarify.
      }
      generalize (loc_comm_ops1 a ops' m []); clarsimp; rewrite H.
      rewrite loc_valid_ops1; auto.
      split; clarify.
      eapply consistent_prefix; rewrite <- app_assoc; simpl; eauto.
      { rewrite Forall_forall in *; intros; rewrite in_map_iff in *; intro; 
          clarify.
        exploit (Hdiff_locs (loc_of x0)); clarify; rewrite in_map_iff; eauto. }
  Qed.

  Lemma reads_noops :forall ops m m2 (Hcon : consistent (m ++ ops))
    (Hreads : Forall (fun x => match x with MRead _ _ => True | _ => False end)
                      ops),
    consistent (m ++ ops ++ m2) <-> consistent (m ++ m2).
  Proof.
    induction ops; clarify; [reflexivity|].
    inversion Hreads; destruct a; clarify.
    generalize (consistent_prefix (m ++ [MRead l0 v]) ops); 
      rewrite <- app_assoc; clarify.
    rewrite read_noop; auto.
    rewrite read_noop in Hcon; auto.
  Qed.

  Lemma not_mod_ops_write : forall ops m l v
    (Hnot_mod : Forall (fun op => op_modifies op l = false) ops)
    (Hcon : consistent (m ++ ops)),
    consistent (m ++ ops ++ [MWrite l v]) <-> consistent (m ++ [MWrite l v]).
  Proof.
    induction ops using rev_ind; clarify; [reflexivity|].
    rewrite <- app_assoc; simpl; rewrite app_assoc; rewrite not_mod_write.
    rewrite <- app_assoc; apply IHops.
    { rewrite Forall_forall in *; intros; apply Hnot_mod; rewrite in_app; auto.
    }
    { eapply consistent_prefix; rewrite <- app_assoc; eauto. }
    { rewrite Forall_forall in *; intros; apply Hnot_mod; rewrite in_app; 
        clarify. }
    { rewrite <- app_assoc; auto. }
  Qed.

(* From layout to model? *)
End Layout.

Arguments MRead [loc] [val] (*[concrete_ptr]*) _ _.
Arguments MWrite [loc] [val] (*[concrete_ptr]*) _ _.
Arguments MAlloc [loc] [val] (*[concrete_ptr]*) _.
Arguments MFree [loc] [val] (*[concrete_ptr]*) _.
(*Arguments MCast [loc] [val] [concrete_ptr] _ _.*)

Section MM_Seq.
  (* There are only two sources of nondeterminism in programs in which every
     location is private: reads of unwritten locations, and casts. *)

  Context `{ML : Memory_Layout} {val_eq : EqDec_eq val}.

  Inductive mem_cell := Freed | Uninit | Stored (v : val).
  Instance mem_cell_eq : @EquivDec.EqDec mem_cell eq eq_equivalence.
  Proof. eq_dec_inst. Qed.

  Definition simple_mem := loc -> mem_cell.
  Definition simple_update m (l : loc) c l' : mem_cell := if eq_dec l' l then c else m l'.

  Definition simple_access (m : simple_mem) (a : mem_op loc val) := match a with
  | MRead l v => match m l with 
                  | Stored v' => if eq_dec v' v then Some m else None 
                  | _ => None 
                  end
  | MWrite l v => Some (simple_update m l (Stored v))
  | MAlloc l => match m l with
                 | Freed => Some (simple_update m l Uninit)
                 | _ => None
                 end
  | MFree l => match m l with
                | Freed => None
                | _ => Some (simple_update m l Freed)
                end
(*  | _ => None*)
  end.

  Fixpoint simple_accesses m ops := match ops with
  | [] => Some m
  | op :: rest => match simple_access m op with
                  | Some m' => simple_accesses m' rest
                  | None => None
                  end
  end.

  Lemma simple_diff_loc : forall sm a sm' l, simple_access sm a = Some sm' ->
    l <> loc_of a -> sm' l = sm l.
  Proof.
    destruct a; clarify; destruct (sm l); clarify; unfold simple_update;
      destruct (eq_dec l0 l); clarify.
  Qed.

(*  Definition all_private m := forall l, private m t l.*)

  Definition make_simple m := simple_accesses (fun _ => Freed) m.

  Lemma simple_accesses_snoc : forall m sm op sm', 
    simple_accesses sm (m ++ [op]) = Some sm' <->
    exists sm'', simple_accesses sm m = Some sm'' /\ 
                 simple_access sm'' op = Some sm'.
  Proof.
    induction m; clarify.
    - destruct (simple_access sm op) eqn: Hop; split; clarsimp.
      eexists; split; eauto.
    - destruct (simple_access sm a) eqn: Ha; [|split]; clarsimp.
  Qed.

  Corollary make_simple_snoc : forall m op sm, 
    make_simple (m ++ [op]) = Some sm <->
    exists sm', make_simple m = Some sm' /\ simple_access sm' op = Some sm.
  Proof.
    intros; unfold make_simple; rewrite simple_accesses_snoc; reflexivity.
  Qed.    

  Lemma simple_freed : forall m l sm (Hsimple : make_simple m = Some sm) 
    (Hfree : sm l = Freed) (Hcon : consistent m),
    (forall v, ~can_do_op m (MRead l v)) /\ 
    can_do_op m (MAlloc l) /\ ~can_do_op m (MFree l).
  Proof.
    unfold can_do_op; induction m using rev_ind; clarify.
    - apply base_allows.
    - rewrite make_simple_snoc in Hsimple; clarsimp.
      setoid_rewrite <- app_assoc; simpl.
      destruct (eq_dec l (loc_of x)).      
      + destruct x; clarify; destruct (x0 l0) eqn: cell; clarify; 
          try (unfold simple_update in *; clarify);
          try (rewrite cell in Hfree; clarify).
        * apply free_allows; auto.
        * apply free_allows; auto.
      + erewrite simple_diff_loc in Hfree; eauto.
        specialize (IHm _ _ eq_refl Hfree (consistent_prefix _ _ Hcon)).
        repeat split; intros; rewrite loc_valid; try intro; clarify.
        specialize (IHm1 v); clarify.
  Qed.

  Lemma simple_uninit : forall m l sm (Hsimple : make_simple m = Some sm) 
    (Hfree : sm l = Uninit) (Hcon : consistent m),
    (forall v, can_do_op m (MWrite l v)) /\
    ~can_do_op m (MAlloc l) /\ can_do_op m (MFree l).
  Proof.
    unfold can_do_op; induction m using rev_ind; clarify.
    - unfold make_simple in Hsimple; clarify.
    - rewrite make_simple_snoc in Hsimple; clarsimp.
      setoid_rewrite <- app_assoc; simpl.
      destruct (eq_dec l (loc_of x)).
      + destruct x; clarify; destruct (x0 l0) eqn: cell; clarify; 
          try (unfold simple_update in *; clarify);
          try (rewrite cell in Hfree; clarify).
        generalize (alloc_allows m l0); clarify.
      + erewrite simple_diff_loc in Hfree; eauto.
        specialize (IHm _ _ eq_refl Hfree (consistent_prefix _ _ Hcon)).
        repeat split; intros; rewrite loc_valid; try intro; clarify.
  Qed.

  Definition write_alloc m := forall m1 l v m2, m = m1 ++ MWrite l v :: m2 ->
    forall sm, make_simple m1 = Some sm -> sm l <> Freed.

  Lemma write_alloc_nil : write_alloc [].
  Proof.
    repeat intro.
    destruct m1; clarify.
  Qed.

  Lemma write_alloc_prefix : forall m m', write_alloc (m ++ m') ->
    write_alloc m.
  Proof.
    unfold write_alloc; intros; eapply H; eauto; clarsimp.
  Qed.

  Lemma simple_stored : forall m l sm (Hsimple : make_simple m = Some sm) 
    v (Hfree : sm l = Stored v) (Hcon : consistent m)
    (Hwrite_alloc : write_alloc m),
    (forall v', can_do_op m (MRead l v') <-> v' = v) /\
    (forall v, can_do_op m (MWrite l v)) /\
    ~can_do_op m (MAlloc l) /\ can_do_op m (MFree l).
  Proof.
    unfold can_do_op; induction m using rev_ind; clarify.
    - unfold make_simple in Hsimple; clarify.
    - rewrite make_simple_snoc in Hsimple; clarsimp.
      setoid_rewrite <- app_assoc; simpl.
      generalize (consistent_prefix _ _ Hcon); intro Hcon'.
      generalize (write_alloc_prefix _ Hwrite_alloc); intro Hwrite_alloc'.
      destruct (eq_dec l (loc_of x)).
      + destruct x; clarify; destruct (x0 l0) eqn: cell; clarify;
        try (unfold simple_update in *; clarify);
        try (rewrite cell in Hfree); try (inversion Hfree); clarify.
        * exploit IHm; eauto; intro Hops.
          repeat split; intros; try (rewrite read_noop; clarify).
          rewrite read_noop in H; clarify.
          rewrite Hops1 in H; auto.
        * exploit Hwrite_alloc; eauto; clarify.
        * exploit simple_uninit; eauto; unfold can_do_op; intro.
          split; [| split]; intros.
          apply read_written; auto.
          rewrite write_not_read; clarify; constructor; clarify.
          rewrite write_not_read, (write_not_read(ops := [MFree l0]) _ _); 
            clarify; try (constructor; clarify).
          intro; clarify.
        * exploit IHm; eauto; intro.
          split; [| split]; intros.
          apply read_written; auto.
          rewrite write_not_read; clarify; constructor; clarify.
          rewrite write_not_read, (write_not_read(ops := [MFree l0]) _ _); 
            clarify; try (constructor; clarify).
          intro; clarify.
      + erewrite simple_diff_loc in Hfree; eauto.
        exploit IHm; eauto; intro.
        repeat split; intros; try (rewrite loc_valid in *); try intro; clarify.
        * rewrite <- H1; auto.
        * rewrite H1; auto.
  Qed.

  Definition read_init m := forall m1 l v m2, m = m1 ++ MRead l v :: m2 ->
    forall sm, make_simple m1 = Some sm -> sm l <> Uninit.

  Lemma read_init_nil : read_init [].
  Proof.
    repeat intro.
    destruct m1; clarify.
  Qed.
  Hint Resolve read_init_nil write_alloc_nil.

  Lemma read_init_prefix : forall m m', read_init (m ++ m') ->
    read_init m.
  Proof.
    unfold read_init; intros; eapply H; eauto; clarsimp.
  Qed.

  Lemma exists_reorder : forall {A B} (P : A -> B -> Prop), 
    (exists x y, P x y) -> exists y x, P x y.
  Proof. clarify; eauto. Qed.

  Lemma exists_scope : forall {A B} P (Q : A -> B -> Prop), 
    (exists x, P x /\ exists y, Q x y) -> exists x y, P x /\ Q x y.
  Proof. clarify; eauto. Qed.

  Lemma consistent_simple : forall m (Hcon : consistent m)
    (Hread_init : read_init m) (Hwrite_alloc : write_alloc m),
    exists sm, make_simple m = Some sm.
  Proof.
    induction m using rev_ind; clarify; eauto.
    { unfold make_simple; clarify; eauto. }
    generalize (consistent_prefix _ _ Hcon);
      generalize (write_alloc_prefix _ Hwrite_alloc);
      generalize (read_init_prefix _ Hread_init); clarify.
    setoid_rewrite make_simple_snoc.
    apply exists_reorder; apply exists_scope; eexists; split; eauto.
    destruct (x0 (loc_of x)) eqn: cell.
    - exploit simple_freed; eauto; intros [Hread [Halloc Hfree]];
        destruct x; clarify; try (rewrite cell); eauto.
      specialize (Hread v); clarify.
    - exploit simple_uninit; eauto; intros [Hwrite [Halloc Hfree]];
        destruct x; clarify; try (rewrite cell); eauto.
      exploit Hread_init; eauto; clarify.
    - exploit simple_stored; eauto; intros [Hread [Hwrite [Halloc Hfree]]];
        destruct x; clarify; try (rewrite cell); eauto.
      unfold can_do_op in *; rewrite Hread in Hcon; clarify; eauto.
  Qed.

  Lemma simple_op : forall m (Hcon : consistent m) op
    (Hread_init : read_init (m ++ [op]))
    (Hwrite_alloc : write_alloc (m ++ [op])),
    exists sm, make_simple m = Some sm /\ 
               (can_do_op m op <-> simple_access sm op <> None).
  Proof.
    intros; generalize (write_alloc_prefix _ Hwrite_alloc);
      generalize (read_init_prefix _ Hread_init); intros.
    exploit consistent_simple; eauto; intros [sm Hmake]; rewrite Hmake;
      eexists; split; eauto.
    destruct (sm (loc_of op)) eqn: cell.
    - exploit simple_freed; eauto; intros [Hread [Halloc Hfree]];
        destruct op; clarsimp; split; clarify.
      + specialize (Hread v); clarify.
      + exploit Hwrite_alloc; eauto; clarify.
    - exploit simple_uninit; eauto; intros [Hwrite [Halloc Hfree]];
        destruct op; clarsimp; split; clarify.
      exploit Hread_init; eauto; clarify.
    - exploit simple_stored; eauto; intros [Hread [Hwrite [Halloc Hfree]]];
        destruct op; clarsimp; split; clarify.
      + unfold can_do_op in *; rewrite Hread in H1; clarify.
      + rewrite Hread; auto.
  Qed.

  Lemma simple_ops : forall ops m (Hcon : consistent m)
    (Hread_init : read_init (m ++ ops))
    (Hwrite_alloc : write_alloc (m ++ ops)),
    exists sm, make_simple m = Some sm /\ 
               (can_do_ops m ops <-> simple_accesses sm ops <> None).
  Proof.
    unfold can_do_ops; induction ops; clarify.
    - exploit consistent_simple; eauto; clarsimp.
      repeat eexists; eauto; clarify.
    - generalize (read_init_prefix _ Hread_init); intro Hinit1.
      generalize (write_alloc_prefix _ Hwrite_alloc); intro Halloc1.
      exploit consistent_simple; eauto; intros [sm Hmake]; rewrite Hmake.
      eexists; split; eauto.
      generalize (read_init_prefix(m := (m ++ [a])) ops);
        generalize (write_alloc_prefix(m := (m ++ [a])) ops);
        rewrite <- app_assoc; clarify.
      exploit simple_op; eauto 2; intro Hop; clarify.
      specialize (IHops (m ++ [a])); clarsimp; rewrite Hop2 in IHops.
      unfold can_do_op in *; destruct (simple_access x a) eqn: Hsm'; clarify.
      + use IHops; clarify.
        rewrite make_simple_snoc in *; clarsimp.
      + split; clarify.
        generalize (consistent_prefix (m ++ [a]) ops); rewrite <- app_assoc;
          intro Hcon1; clarify.
        rewrite Hop2 in Hcon1; clarify.
  Qed.

  Corollary simple_ops_iff : forall ops m (Hcon : consistent m)
    (Hread_init : read_init (m ++ ops))
    (Hwrite_alloc : write_alloc (m ++ ops))
    sm (Hsm : make_simple m = Some sm),
  can_do_ops m ops <-> simple_accesses sm ops <> None.
  Proof. intros; exploit simple_ops; eauto 2; clarsimp. Qed.

(*  Hint Unfold private_a.

  Lemma all_private_extend : forall m a m' (Hprivate : all_private m)
    (Happly : apply_access' m a m') (Hthread : get_thread a = t),
    all_private m'.
  Proof.
    intros; unfold all_private in *; unfold private in *; clarify.
    specialize (Hprivate l); destruct Hprivate as 
      [m0 [Hinit [ops [Hon Hupdate]]]]; exists m0; clarify.
    exists (ops ++ [a]); split.
    + apply Forall_snoc; auto.
    + eapply update_trans; eauto.
      rewrite update_single_iff; auto.
  Qed.*)

  (* At the memory level *)
  (* MOVE UP *)
(*  Lemma simple_write : forall (m1 m2 : mem ptr loc) l v sm1 sm2
    (Hsm1 : make_simple(Val := const_eq Ptr) (m1 ++ MWrite l v :: m2) = Some sm1)
    (Hsm2 : make_simple(Val := const_eq Ptr) (m1 ++ m2) = Some sm2),
    (forall l', l' <> l -> sm1 l' = sm2 l') /\ (sm1 l = sm2 l \/
      sm1 l = Stored v /\ sm2 l <> Freed).
  Proof.
    induction m1; clarsimp.
    - assert (sm1 = simple_update sm2 l (Stored v)); [destruct (sm2 l)|]; 
        clarify.
      unfold simple_update; split; clarify.
      right; destruct (sm2 l); split; clarify.
    - exploit IHm1; eauto; clarify.
      destruct a; clarify; try (destruct (x l0); destruct (x0 l0); clarify;
        unfold simple_update; split; clarify; destruct (eq_dec l l0); clarify).
  Qed.
    
  Lemma consistent_add_write : forall m1 m2 l v
    (Hcon1 : consistent(ML := ML) (m1 ++ MWrite l v :: m2) = true)
    (Hcon2 : consistent(ML := ML) (m1 ++ m2) = true)
    sm2 (Hsm1 : make_simple(Val := const_eq Ptr) (m1 ++ m2) = Some sm2),
    exists sm1, make_simple(Val := const_eq Ptr) (m1 ++ MWrite l v :: m2) = 
      Some sm1.
  Proof.
    induction m1; clarify.
    - destruct (sm2 l) eqn: state; eauto.
      exploit (simple_freed ML); eauto; intros [_ [no_write _]].
      rewrite no_write in *; discriminate.
    - clarsimp; exploit IHm1; eauto 2; clarify; clear IHm1.
      exploit simple_write; eauto 2; intros [Hdiff Hsame].
      destruct (eq_dec(EqDec_eq := EqDec_eq_of_EqDec (@mem_cell_eq _ (const_eq Ptr))) (x0 (loc_of a)) (x (loc_of a))).
      + destruct a; clarify; rewrite e in *; destruct (x l0); clarify; eauto.
      + specialize (Hdiff (loc_of a)); destruct (eq_dec (loc_of a) l); 
        [| rewrite Hdiff in *]; clarify.
        destruct a; clarify; rewrite Hsame1 in *; clarify; eauto.
        * destruct (x l) eqn: state2; clarify.
          exploit (simple_stored ML (m1 ++ MWrite l v :: m2)); eauto;
            intros [read _]; rewrite read in *; clarify.
        * destruct (x l); clarify.
  Qed.
  
  Lemma read_init_write : forall (m1 m2 : mem ptr loc) l v
    (Hcon1 : consistent(ML := ML) (m1 ++ MWrite l v :: m2) = true)
    (Hcon2 : consistent(ML := ML) (m1 ++ m2) = true)
    (Hread_init : read_init(Val := const_eq Ptr) (m1 ++ m2) = true),
    read_init(Val := const_eq Ptr) (m1 ++ MWrite l v :: m2) = true.
  Proof.
    induction m1; clarify.
    destruct a; clarsimp.
    destruct (make_simple (m1 ++ m2)) eqn: Hm; clarify.
    - exploit consistent_add_write; eauto 2; intros [m' Hm']; 
        setoid_rewrite Hm'.
      exploit simple_write; eauto 2; intros [Hdiff Hsame].
      destruct (eq_dec(EqDec_eq := EqDec_eq_of_EqDec (@mem_cell_eq _ (const_eq Ptr))) (m' l0) (m l0)).
      + rewrite e in *; destruct (m l0); clarify.
      + specialize (Hdiff l0); destruct (eq_dec l0 l); [| rewrite Hdiff in *];
          clarify.
        rewrite Hsame1.
        destruct (m l); clarify.
    - destruct (make_simple (m1 ++ MWrite l v :: m2)) eqn: Hm'; clarify.
      generalize (simple_no_cast _ Hm'); intro.
      exploit (consistent_simple ML); eauto 2; clarify.
      rewrite Forall_forall in *; clarify.
  Qed.      

  Lemma remove_dead_write : forall (m1 m2 : mem ptr loc) l v op 
    (Hnot_read : forall v', op <> MRead l v') 
    (Hnot_cast : is_mcast op = false)
    (Hcon1 : consistent(ML := ML) (m1 ++ MWrite l v :: m2) = true)
    (Hcon2 : consistent(ML := ML) (m1 ++ m2) = true)
    (Hno_cast : Forall (fun x => is_mcast x = false) (m1 ++ m2))
    (Hread_init : read_init(Val := const_eq Ptr) (op :: m1 ++ m2) = true),
    can_do_op(Memory_Layout := ML) (m1 ++ MWrite l v :: m2) op = 
    can_do_op(Memory_Layout := ML) (m1 ++ m2) op.
  Proof.
    intros; generalize (read_init_suffix [op] _ Hread_init); intro Hinit0.
    exploit (simple_op(Val := const_eq Ptr)(concrete_ptr := Z)); eauto 2;
      clarify.
    { rewrite H0 in Hread_init; intro X; rewrite X in Hread_init; clarify. }
    destruct (make_simple (m1 ++ m2)) eqn: Hm2; clarify.
    generalize (simple_op(Val := const_eq Ptr)(concrete_ptr := Z) _ Hcon1);
      intro X; repeat use X.
    specialize (X _ Hnot_cast).
    use X.
    destruct (make_simple (m1 ++ MWrite l v :: m2)) eqn: Hm1; clarify.
    rewrite H; rewrite X.
    exploit simple_write; eauto 2; intros [Hdiff Hsame].
    destruct (eq_dec(EqDec_eq := EqDec_eq_of_EqDec (@mem_cell_eq _ (const_eq Ptr))) (m0 (loc_of op)) (m (loc_of op))).
    - destruct op; clarify; rewrite e in *; destruct (m l0); clarify.
    - specialize (Hdiff (loc_of op)); destruct (eq_dec (loc_of op) l); 
        [| clarify].
      destruct op; simpl in *; subst; try (specialize (Hnot_read c));
        try (destruct Hsame as [? | [Hm0 Hm]]; 
             [| rewrite Hm0 in *; destruct (m l)]); clarify.
    - clarify.
      exploit simple_write; eauto; intros [Hdiff Hsame].
      specialize (Hdiff l0); intro X; rewrite X in Hdiff.
      specialize (Hnot_read v0); destruct (eq_dec l0 l); clarify.
      rewrite <- Hdiff in *; auto.
    - apply read_init_write; auto.
    - rewrite Forall_forall in *; intros x Hin; specialize (Hno_cast x).
      rewrite in_app in Hin; clarify; destruct Hin as [? | [? | ?]]; clarify;
        use Hno_cast; auto; rewrite in_app; auto.
  Qed.

  Lemma remove_dead_write_ops : forall (m2 : mem ptr loc) l v ops m1
    (Hnot_read : Forall (fun op => forall v', op <> MRead l v') ops)
    (Hnot_cast : Forall (fun op => is_mcast op = false) ops)
    (Hcon1 : consistent(ML := ML) (m1 ++ MWrite l v :: m2) = true)
    (Hcon2 : consistent(ML := ML) (m1 ++ m2) = true)
    (Hno_cast : Forall (fun x => is_mcast x = false) (m1 ++ m2))
    (Hread_init : read_init(Val := const_eq Ptr) (rev ops ++ m1 ++ m2) = true),
    can_do_ops(ML := ML) (m1 ++ MWrite l v :: m2) ops = 
    can_do_ops(ML := ML) (m1 ++ m2) ops.
  Proof.
    induction ops; clarify.
    inversion Hnot_read; inversion Hnot_cast; clarify.
    exploit remove_dead_write; eauto 2.
    { apply (read_init_suffix (rev ops)); clarsimp. }
    intro Hrem.
    specialize (IHops (a :: m1)); clarify.
    destruct (can_do_op (m1 ++ m2) a) eqn: Hcan_do; 
      setoid_rewrite Hcan_do in Hrem; clarsimp.
    destruct (can_do_ops (a :: m1 ++ m2) ops); clarsimp.
  Qed.*)

End MM_Seq.