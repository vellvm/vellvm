From Vellvm Require Import
  Utilities
  Syntax.

From Vellvm Require Import
  Params.Address.

(* TODO: move this? *)
Module Type PTOI (Addr : ADDRESS).
  Import Addr.
  
  Parameter ptr_to_int : addr -> Z.
End PTOI.

(* TODO: move this? *)
Module Type ITOP (Addr : ADDRESS) (PROV:PROVENANCE(Addr)) (PTOI:PTOI(Addr)).
  Import PROV.
  Import PTOI.
  Import Addr.

  Parameter int_to_ptr : Z -> Prov -> EOB addr.
  Parameter int_to_ptr_provenance :
    forall (x : Z) (p : Prov) (a : addr),
      int_to_ptr x p = ret a ->
      address_provenance a = p.

  Parameter int_to_ptr_ptr_to_int :
    forall (a : addr) (p : Prov),
      address_provenance a = p ->
      int_to_ptr (ptr_to_int a) p = ret a.

  Parameter int_to_ptr_ptr_to_int_exists :
    forall (a : addr) (p : Prov),
    exists a',
      int_to_ptr (ptr_to_int a) p = ret a' /\
        ptr_to_int a' = ptr_to_int a /\
        address_provenance a' = p.

  Parameter ptr_to_int_int_to_ptr :
    forall (x : Z) (p : Prov) (a : addr),
      int_to_ptr x p = ret a ->
      ptr_to_int a = x.
End ITOP.

Module Type ITOP_BIG (Addr:MemoryAddress.ADDRESS) (PROV:PROVENANCE(Addr)) (PTOI:PTOI(Addr)) (ITOP : ITOP Addr PROV PTOI).
  Import ITOP.

  Parameter int_to_ptr_safe :
    forall z pr,
      match int_to_ptr z pr with
      | raise_ret _ => True
      | _ => False
      end.
End ITOP_BIG.
