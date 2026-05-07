Definition option_pred {A} (pred : A -> bool) (ma : option A) : bool
  := match ma with
     | Some x => pred x
     | None => false
     end.

