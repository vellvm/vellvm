(** Debug utilities **)

Definition debug_hom {E} (R : Type) (e : DebugE R) : itree E R :=
  match e with
  | Debug _ => Ret tt
  end.

Definition into_debug {E F} (h : E ~> LLVM F) : CallE +' Locals +' CallE +' IO +' (F +' E) ~> LLVM F :=
  fun x e =>
    match e with
    | inr1 (inr1 (inr1 (inr1 (inr1 e)))) => h _ e
    | inr1 (inr1 (inr1 (inr1 (inl1 e)))) => vis e (fun x => Ret x)
    | inr1 (inr1 (inr1 (inl1 e))) => vis e (fun x => Ret x)
    | inr1 (inr1 (inl1 e)) => vis e (fun x => Ret x)
    | inr1 (inl1 e) => vis e (fun x => Ret x)
    | inl1 e => vis e (fun x => Ret x)
    end.

Definition ignore_debug {E} : LLVM (E +' debugE) ~> LLVM E :=
  interp (into_debug debug_hom).

