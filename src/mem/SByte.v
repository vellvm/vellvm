From Mem Require Import
  StoreId.

Module Type SBYTE.
Parameter SByte : Type.
Parameter sbyte_sid : SByte -> store_id.
End SBYTE.
