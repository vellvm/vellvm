Definition from_option {A} (def : A) (opt : option A) : A
  := match opt with
     | Some x => x
     | None => def
     end.

