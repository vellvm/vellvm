Variant UndefE : Type -> Type :=
  | pick (u:uvalue) (p : dvalue -> Prop) : UndefE dvalue.
