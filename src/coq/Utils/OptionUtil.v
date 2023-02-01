Definition guard_opt (x : bool) : option unit
  := if x then Some tt else None.

Definition from_option {A} (def : A) (opt : option A) : A
  := match opt with
     | Some x => x
     | None => def
     end.

Definition option_rel2 {X1 X2 : Type} (R : X1 -> X2 -> Prop) : (option X1 -> option X2 -> Prop) :=
  fun mx my => match mx,my with
            | Some x, Some y => R x y
            | None, None => True
            | _, _ => False
            end.
#[export] Hint Unfold option_rel2 : core.
