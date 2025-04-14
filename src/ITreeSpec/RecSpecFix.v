From Stdlib Require Export
  Morphisms
  Setoid
  Program.Equality
  Lists.List
  Logic.EqdepFacts
  Eqdep EqdepFacts.

From ITree Require Import
  Basics.HeterogeneousRelations
  Core.ITreeDefinition
  Eq.Eqit.

From ITreeSpec Require Import
  ITreeSpecDefinition
  MRecSpec.

Definition unCall {In Out} (c : callE In Out) : In :=
  match c with Call _ _ i => i end.
#[global] Instance ReSum_id {E} `{EncodingType E} : (ReSum E E) :=
  fun e => e.

#[global] Instance ReSumRet_id {E} `{EncodingType E} : (ReSumRet E E) :=
  fun e x  => x.

#[global] Instance callESpecReSum {E In Out} `{EncodingType E} :
  ReSum (callE In Out + E) (SpecEvent (callE In Out + E)) := 
SpecEventReSum (callE In Out + E) (callE In Out + E). 

#[global] Instance callESpecReSumRet {E In Out} `{EncodingType E} :
  ReSumRet (callE In Out + E) (SpecEvent (callE In Out + E)) :=
SpecEventReSumRet (callE In Out + E) (callE In Out + E).

(* ReSum (callE In Out + ?B) (SpecEvent (callE In Out + E) *)
Definition call_spec {E} `{EncodingType E} {In Out} (a : In) : entree_spec (callE In Out + E) Out :=
  @trigger _ _ _ _ callESpecReSum callESpecReSumRet ((inl (Call In Out a) )).

Definition calling' {F A B} `{EncodingType F} : 
  (A -> entree F B) ->
  (forall (c : callE A B), entree F (encodes c) ) :=
  fun f c => f (unCall c).

Definition rec_spec {A B E} `{EncodingType E} 
           (body : A -> entree_spec (callE A B + E) B) (a : A) : entree_spec E B :=
  mrec_spec (calling' body) (Call A B a).

Definition rec_fix_spec {A B E} `{EncodingType E}  (body : (A -> entree_spec (callE A B + E) B ) -> 
                                A -> entree_spec (callE A B + E) B  ) : 
  A -> entree_spec E B :=
  rec_spec (body call_spec).
