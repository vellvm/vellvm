Require Import Floats.
Require Import Coq.ZArith.ZArith.

Require Import Flocq.IEEE754.Binary.

Definition can_convert_exactly (target_prec target_emax : Z) (m : positive) (e : Z) : bool
  :=
    let '(res_m, res_e) := shl_align_fexp target_prec target_emax m e in
    bounded target_prec target_emax res_m res_e.

Definition can_convert_float_to_float32 (v: float) : bool
  :=
    match v with
    | B754_finite _ m e _ => can_convert_exactly 24 128 m e
    | _ => true
    end.
