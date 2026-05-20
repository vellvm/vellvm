From Vellvm Require Import
  Utilities
  Syntax.

From Vellvm Require Import
  Params.IPtr
  Params.Provenance
  Integers
  VellvmIntegers.

From QuickChick Require Import Show.

(* TODO: look into how to use decidable equality more uniformaly and cleanly *)
Definition eq_dec_option [A]
  (dec : forall (a b : A), {a = b} + {a <> b}) :
  forall (a b : option A), {a = b} + {a <> b}.
  refine (fun a b => match a,b with
                  | Some a, Some b =>
                      match dec a b with
                      | left e => _
                      | right ne => _
                      end
                  | None, None => left eq_refl
                  | _, _ => _
                  end).
  left; f_equal; exact e.
  right; intros abs; apply ne; inv abs; reflexivity. 
  right; intros abs; inv abs.
  right; intros abs; inv abs.
Defined. 
  
Instance ProvenanceV : Provenance :=
  {|
    provenance := N ;
    allocationId := option N; (* None is wildcard *)
    (* TODO: Should probably make this an NSet, but it gives universe inconsistency with Module addr *)
    prov := option (list N); (* provenance *)

    wildcard_prov := None;
    nil_prov := Some [];

    (* Does the provenance set pr allow for access to aid? *)
    access_allowed pr aid :=
      match pr with
       | None => true (* Wildcard can access anything; *)
       | Some prset =>
           match aid with
           | None => true (* Wildcard, can be accessed by anything; *)
           | Some aid =>
               existsb (N.eqb aid) prset
           end
       end;

    aid_access_allowed pr aid :=
      match pr with
       | None => true
       | Some pr =>
           match aid with
           | None => true
           | Some aid =>
               N.eqb pr aid
           end
       end;

    allocation_id_to_prov aid := fmap (fun x => [x]) aid;

    provenance_to_allocation_id pr := Some pr;

    provenance_to_prov pr := Some [pr];

    initial_provenance := 0%N;
    next_provenance pr := N.succ pr;

    eq_dec_provenance  := N.eq_dec ;
    eq_dec_aid := eq_dec_option N.eq_dec;

    provenance_lt := N.lt;
    
    (* Debug *)
    show_prov pr  := Show.show pr;
    show_provenance pr := Show.show pr;
    show_allocation_id aid := Show.show aid;

  |}.

Instance ProvenanceVTheory : ProvenanceTheory.
Proof.
  constructor; auto.
  - intros; cbn; break_match; auto.
    now rewrite N.eqb_refl.
  - intros []; cbn; auto.
    cbn; now rewrite N.eqb_refl.
  - cbn; intros; repeat break_match_hyp; congruence.
  - cbn; intros; congruence.
  - cbn; intros. 
    destruct N.eq_dec; auto; congruence.
  - intros aid; destruct (eq_dec_aid aid aid); auto; congruence.
  - intros x y H x0 y0 H0.
    subst.
    cbn.
    symmetry in H0.
    eapply proj_sumbool_true in H0.
    subst.
    reflexivity.
  - cbn; repeat intro; lia.
  - cbn; repeat intro; lia.
  - cbn; repeat intro; lia.
  - cbn; repeat intro; lia.
  - cbn; repeat intro; lia.
Qed.

