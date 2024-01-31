(* begin hide *)
From Coq Require Import
     Program
     Lists.List.

 From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
(* end hide *)

(** * A trace-based axiomatic memory model? 
  This is currently a very naive experiment, nothing well thought out.
*)

Module Simple.

  Section WithDom.

    Variable (var value : Type).
    Variable (eqb : var -> var -> bool).
    Infix "=?" := eqb (at level 50).

    (* We assume computations interacting through simple read and writes with a memory *)
    Variant StateE : Type -> Type :=
    | GetVar (x : var) : StateE value
    | SetVar (x : var) (v : value) : StateE unit.

    (* [action]s are read and writes to the memory, they map one to one to events *)
    Variant action : Type := Wr (x: var) (v : value) | Rd (x : var) (v : value). 
    (* A history is a finite list of actions that has occurred. We add to the left, never remove *)
    Definition history : Type := list action.

    (* The semantics of a read is deterministic if at least one write to the same cell has taken place before *)
    Fixpoint read (t : history) (x : var) : option value :=
      match t with
      | nil => None
      | Wr y v :: t => if x =? y then Some v else read t x
      | Rd _ _ :: t => read t x
      end.

    (* Our model of computation is gonna be essentially a non-deterministic
   stateful computation using historys as states *)
    Definition myMonad (X : Type) : Type :=
      history -> itree void1 (history * X) -> Prop.
    Definition myOtherMonad (X : Type) : Type :=
      (history -> itree void1 (history * X)) -> Prop.

    (* We can now define our handler.
   - we simply record writes in the history
   - Reads are deterministic if we find a write.
   - Reads are unspecified if we haven't written yet to it, i.e. can return any value
   We can remark that we don't use the reads from the history, we could ditch them
     *)
    Variant handler_prop: StateE ~> myMonad :=
    | SetVarH : forall x v h,
        handler_prop _ (SetVar x v) h (ret (Wr x v :: h, tt))
    | GetVarSetH : forall x v h,
        read h x = Some v ->
        handler_prop _ (GetVar x) h (ret (Rd x v :: h, v))
    | GetVarUnsetH : forall x v h,
        read h x = None ->
        handler_prop _ (GetVar x) h (ret (Rd x v :: h, v))
    .

    (* We can also define the model where one cannot read to a variable before it's written to *)
    Variant handler_prop': StateE ~> myMonad :=
    | SetVarH' : forall x v h,
        handler_prop' _ (SetVar x v) h (ret (Wr x v :: h, tt))
    | GetVarSetH' : forall x v h,
        read h x = Some v ->
        handler_prop' _ (GetVar x) h (ret (Rd x v :: h, v))
    .

    (* We can also define the executable model where a default value is used *)
    Definition handler_exec (def : value) : StateE ~> stateT history (itree void1) :=
      fun _ e h =>
        match e with
        | SetVar x v => ret (Wr x v :: h, tt)
        | GetVar x   =>
          match read h x with
          | Some v => ret (Rd x v :: h, v)
          | None   => ret (Rd x def :: h, def)
          end
        end 
    .

    (* Clearly, there is some kind of refinement going on between the models *)
    Lemma handler_prop_refine :
      forall X (e : StateE X) h t,
        handler_prop' _ e h t ->
        handler_prop _ e h t. 
    Proof using.
      intros * HP.
      dependent destruction HP.
      constructor; auto.
      constructor; auto.
    Qed.

    (* Clearly, the implementation is somehow valid *)
    Lemma handler_exec_refine :
      forall X (e : StateE X) def h t,
        handler_exec def _ e h = t ->
        handler_prop _ e h t. 
    Proof using.
      intros * HP.
      destruct e; cbn in *.
      destruct (read h x) eqn:EQ.
      subst t; constructor; auto.
      subst t; constructor 3; auto.
      subst t; constructor; auto.
    Qed.

    (* MGZ'15 takes a different take: it defines axioms that constraint the legal actions
     given an history that a memory model can allow *)
    Definition site (a : action) : var :=
      match a with
      | Rd x _ | Wr x _ => x
      end.

    Definition is_write (a : action) : bool :=
      match a with
      | Wr _ _ => true
      | _ => false
      end.

    Definition modifies (a : action) (x : var) : bool :=
      match a with
      | Wr y _ => y =? x
      | _ => false
      end.

    Record valid (can_do : history -> action -> Prop) : Prop :=
      {
      (* Different sites are separated: actions at different sites commute *)
      Site_comm : forall h a a',
          site a =? site a' ->
          can_do (a :: h) a' <-> can_do (a' :: h) a;

      (* Different sites are separated: an action at a site cannot regulate actions at other sites *)
      Site_drop : forall h a a',
          site a =? site a' ->
          can_do (a :: h) a' <-> can_do h a';

      (* Reads don't regulate possible actions *)
      Read_noop : forall h x v a,
          can_do h (Rd x v) ->
          can_do (Rd x v :: h) a <-> can_do h a;

      (* Writes regulate reads *)
      Read_written : forall h x v v',
          can_do h (Wr x v) -> 
          can_do (Wr x v :: h) (Rd x v') <-> v = v';

      (* Writes can only regulate reads *)
      Write_not_read : forall h x v a,
          can_do h (Wr x v) ->
          ~ is_write a ->
          can_do (Wr x v :: h) a <-> can_do h a;

      (* Writes can only be regulated by actions modifying their location *)
      Not_mod_write : forall h l v a,
          can_do h a ->
          ~ modifies a l ->
          can_do (a :: h) (Wr l v) <-> can_do h (Wr l v);

      (* The value intended to be written does not mandate the legality of a write *)
      
      Write_any_value : forall h x v v',
          can_do h (Wr x v) <-> can_do h (Wr x v');

      (* At the dawn of time, nothing can be read *)
      Base_read : forall l v,
          ~ can_do nil (Rd l v)
            
      }.

    (* Question : can we easily link both approaches? *)
    Definition event_of_action (a : action) : {X : Type & StateE X & X} :=
      match a with
      | Rd x v => existT2 _ _ _ (GetVar x) v
      | Wr x v => existT2 _ _ _ (SetVar x v) tt
      end.
    (* We could define a notion of "can_do", but at least this attempt lacks something:
       we also need to constraint the "h" to be reachable
     *)
    Definition can_do_step : history -> action -> Prop :=
      fun h a => 
        let '(existT2 _ _ X e v) := event_of_action a in
        handler_prop _ e h (ret (a :: h, v)).
    Inductive can_extend : history -> history -> Prop :=
    | Extend_refl : forall h, can_extend h h
    | Extend_step : forall h h' a,
        can_extend h h' ->
        can_do_step h' a ->
        can_extend h (a :: h').

    Definition valid_history : history -> Prop :=
      can_extend nil.

    Definition can_do := fun h a => valid_history h /\ can_do_step h a.

    Lemma handler_prop_valid : valid can_do.
    Proof using.
      constructor.
      (* - intros * SITE; split; intros CAN. *)
      (*   + destruct a, a'; try now constructor.  *)
      (*     * cbn in CAN. *)
      (*       inv CAN. *)
      (*       constructor. *)
      (*       dependent destruction CAN. *)
      (*       cbn in x. *)
    Admitted.

  End WithDom.

End Simple.

Module MGZ.

  Section WithDom.

    Variable (loc value : Type).
    Variable (eqb : loc -> loc -> bool).
    Infix "=?" := eqb (at level 50).

    (* We assume computations interacting through simple read and writes with a memory *)
    Variant MemE : Type -> Type :=
    | RdE (l : loc)             : MemE value
    | WrE (l : loc) (v : value) : MemE unit
    | AllocE                    : MemE loc
    | FreeE (l : loc)           : MemE unit.

    (* [action]s map one to one to events, but carry the answer as well *)
    Variant action : Type :=
      Wr (l : loc) (v : value)
    | Rd (l : loc) (v : value)
    | Al (l : loc)
    | Fr (l : loc).

    (* A history is a finite list of actions that has occurred. We add to the left, never remove *)
    Definition history : Type := list action.

    (* The semantics of a read is deterministic if at least one write to the same cell has taken place before *)
    Variant can_read : Type := | SuccessR (v : value) | UninitR | FreedR.
    Fixpoint read (h : history) (l : loc) : can_read :=
      match h with
      | nil                     => UninitR
      | Wr l' v :: h            => if l =? l' then SuccessR v else read h l
      | Fr l' :: h              => if l =? l' then FreedR else read h l
      | Rd _ _ :: h | Al _ :: h => read h l
      end.

    Variant can_write : Type := | SuccessW | UninitW | FreedW.
    Fixpoint write (h : history) (l : loc) : can_write :=
      match h with
      | nil                       => UninitW
      | Fr l' :: h                => if l =? l' then FreedW else write h l
      | Al l' :: h                => if l =? l' then SuccessW else write h l
      | Rd _ _ :: h | Wr _ _ :: h => write h l
      end.

    Variant can_alloc : Type := | SuccessA | BoundA.
    Fixpoint alloc (h : history) (l : loc) : can_alloc :=
      match h with
      | nil                       => SuccessA
      | Fr l' :: h                => if l =? l' then SuccessA else alloc h l
      | Al l' :: h                => if l =? l' then BoundA else alloc h l
      | Rd _ _ :: h | Wr _ _ :: h => alloc h l
      end.

    Variant can_free : Type := | SuccessF | AlreadyFreedF | UninitF.
    Fixpoint free (h : history) (l : loc) : can_free :=
      match h with
      | nil                       => UninitF
      | Fr l' :: h                => if l =? l' then AlreadyFreedF else free h l
      | Al l' :: h                => if l =? l' then SuccessF else free h l
      | Rd _ _ :: h | Wr _ _ :: h => free h l
      end.

    (* Our model of computation is gonna be essentially a non-deterministic
   stateful computation using historys as states *)
    Definition myMonad (X : Type) : Type :=
      history -> itree void1 (history * X) -> Prop.

    (* We can now define our handler.
     Here is only the "well defined, successful, deterministic" bit.
     What should be the semantics of the other cases?
     *)
    Variant handler_prop: MemE ~> myMonad :=
    | RdH : forall l v h,
        read h l = SuccessR v ->
        handler_prop _ (RdE l) h (ret (Rd l v :: h, v))

    | WrH : forall l v h,
        write h l = SuccessW ->
        handler_prop _ (WrE l v) h (ret (Wr l v :: h, tt))

    | AlH : forall l h,
        alloc h l = SuccessA ->
        handler_prop _ AllocE h (ret (Al l :: h, l))

    | FrH : forall l h,
        free h l = SuccessF ->
        handler_prop _ (FreeE l) h (ret (Fr l :: h, tt))
    .


    (* MGZ'15 takes a different take: it defines rules to describes legal actions given an history *)
    Definition site (a : action) : loc :=
      match a with
      | Rd l _ | Wr l _ | Al l | Fr l => l
      end.

    Definition is_write (a : action) : bool :=
      match a with
      | Wr _ _ => true
      | _ => false
      end.

    Definition modifies (a : action) (l : loc) : bool :=
      match a with
      | Wr l' _ | Al l' | Fr l' => l' =? l
      | _ => false
      end.

    Record valid (can_do : history -> action -> Prop) : Prop :=
      {
      (* Different sites are separated: actions at different sites commute *)
      Site_comm : forall h a a',
          site a =? site a' ->
          can_do (a :: h) a' <-> can_do (a' :: h) a;

      (* Different sites are separated: an action at a site cannot regulate actions at other sites *)
      Site_drop : forall h a a',
          site a =? site a' ->
          can_do (a :: h) a' <-> can_do h a';

      (* Reads don't regulate possible actions *)
      Read_noop : forall h l v a,
          can_do h (Rd l v) ->
          can_do (Rd l v :: h) a <-> can_do h a;

      (* Writes regulate reads *)
      Read_written : forall h l v v',
          can_do h (Wr l v) -> 
          can_do (Wr l v :: h) (Rd l v') <-> v = v';

      (* Writes can only regulate reads *)
      Write_not_read : forall h l v a,
          can_do h (Wr l v) ->
          ~ is_write a ->
          can_do (Wr l v :: h) a <-> can_do h a;

      (* Writes can only be regulated by actions modifying their location *)
      Not_mod_write : forall h l v a,
          can_do h a ->
          ~ modifies a l ->
          can_do (a :: h) (Wr l v) <-> can_do h (Wr l v);

      (* The value intended to be written does not mandate the legality of a write *)
      Write_any_value : forall h l v v',
          can_do h (Wr l v) <-> can_do h (Wr l v');

      (* Allocation enable writes *)
      Alloc_allows_write : forall h l v,
          can_do h (Al l) ->
          can_do (Al l :: h) (Wr l v);
      (* A location cannot be allocated twice *)
      Alloc_forbids_alloc : forall h l,
          can_do h (Al l) ->
          ~ can_do (Al l :: h) (Al l);
      (* Allocation enables free *)
      Alloc_allows_free : forall h l,
          can_do h (Al l) ->
          can_do (Al l :: h) (Fr l);

      (* Free forbids reads (but it can still write???) *)
      Free_forbids_read : forall h l v,
          can_do h (Fr l) ->
          ~ can_do (Fr l :: h) (Rd l v);
      (* A location cannot be freed twice *)
      Free_forbids_free : forall h l,
          can_do h (Fr l) ->
          ~ can_do (Fr l :: h) (Fr l);
      (* A freed location can be reallocated *)
      Free_allows_alloc : forall h l,
          can_do h (Fr l) ->
          ~ can_do (Fr l :: h) (Al l);

      (* At the dawn of time, nothing can be read *)
      Base_read : forall l v,
          ~ can_do nil (Rd l v);
      (* At the dawn of time, everything can be allocated *)
      Base_alloc : forall l,
          can_do nil (Al l);
      (* At the dawn of time, nothing can be freed *)
      Base_free : forall l,
          ~  can_do nil (Fr l)

      }.

  End WithDom.
End MGZ.

