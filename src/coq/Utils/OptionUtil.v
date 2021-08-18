Definition guard_opt (x : bool) : option unit
  := if x then Some tt else None.

Definition from_option {A} (def : A) (opt : option A) : A
  := match opt with
     | Some x => x
     | None => def
     end.
