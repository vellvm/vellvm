From Stdlib Require Import Program String Ascii List Decimal ZArith.
From Vellvm.Utils Require Import ListUtil.
Import ListNotations.
Open Scope string.

(* Reduction on a string of the shape ["foo" ++ show(i) ++ ...]
   breaks "foo" into a sequence of [Chars], rendering the goal unreadable.
   We prevent reduction in [append] as a quick fix.
 *)
Arguments append : simpl never.

Fixpoint string_fold_left {A} (f : A -> ascii -> A) (s:string) (acc:A) : A :=
  match s with
  | EmptyString => acc
  | String ch s =>
      string_fold_left f s (f acc ch)
  end.

Definition rev_string (s : string) : string
  := string_fold_left (fun acc x => String x acc) s EmptyString.

Definition string_of_list_ascii_tail_rec (s : list ascii) : string
  := rev_string (fold_left (fun acc ch => String ch acc) s EmptyString).

Definition list_ascii_of_string_tail_rec (s : string) : list ascii
  := rev_tail_rec (string_fold_left (fun acc ch => ch :: acc) s []).

(* The following is reproduced from the QuickChick library to avoid a heavy dependency *)
Section Show.

  Fixpoint contents {A : Type} (s : A -> string) (l : list A) : string :=
    match l with
    | nil => ""%string
    | cons h nil => s h
    | cons h t => append (append (s h) "; ") (contents s t)
    end.

  Class Show (A : Type) : Type :=
    { show : A -> string }.

  Fixpoint show_uint (n : uint) : string :=
    match n with
    | Nil => ""
    | D0 n => String "0" (show_uint n)
    | D1 n => String "1" (show_uint n)
    | D2 n => String "2" (show_uint n)
    | D3 n => String "3" (show_uint n)
    | D4 n => String "4" (show_uint n)
    | D5 n => String "5" (show_uint n)
    | D6 n => String "6" (show_uint n)
    | D7 n => String "7" (show_uint n)
    | D8 n => String "8" (show_uint n)
    | D9 n => String "9" (show_uint n)
    end.

  Definition show_int (n : int) : string :=
    match n with
    | Pos n => show_uint n
    | Neg n => String "-" (show_uint n)
    end.

  Definition show_nat (n : nat) : string :=
    show_uint (Nat.to_uint n).

  Definition show_bool (b : bool) : string :=
    match b with
    | true => "true"
    | false => "false"
    end.

  Definition show_Z (n : Z) : string :=
    show_int (Z.to_int n).

  Definition show_N : N -> string :=
    show_Z ∘ Z.of_N.

  #[global] Instance showUint : Show uint :=
    {|
      show := show_uint
    |}.

  #[global] Instance showInt : Show int :=
    {|
      show := show_int
    |}.

  #[global] Instance showNat : Show nat :=
    {|
      show := show_nat
    |}.

  #[global] Instance showBool : Show bool :=
    {|
      show := show_bool
    |}.

  #[global] Instance showZ : Show Z :=
    {|
      show := show_Z
    |}.

  #[global] Instance showN : Show N :=
    {|
      show := show_N
    |}.

  Fixpoint from_list (s : list ascii) : string :=
    match s with
    | [] => EmptyString
    | c :: s' => String c (from_list s')
    end.

  Definition unit_digit (n : nat) : ascii :=
    ascii_of_nat ((n mod 10) + 48 (* 0 *)).

  Definition three_digit (n : nat) : string :=
    let n0 := unit_digit n in
    let n1 := unit_digit (n / 10) in
    let n2 := unit_digit (n / 100) in
    from_list [n2; n1; n0].

  Definition digit_of_ascii (c : ascii) : option nat :=
    let n := nat_of_ascii c in
    if ((48 <=? n)%nat && (n <=? 57)%nat)%bool then
      Some (n - 48)
    else
      None.

  Definition unthree_digit (c2 c1 c0 : ascii) : option ascii :=
    let doa := digit_of_ascii in
    match doa c2, doa c1, doa c0 with
    | Some n2, Some n1, Some n0 =>
        Some (ascii_of_nat (n2 * 100 + n1 * 10 + n0))
    | _, _, _ => None
    end.

  Fixpoint show_quoted_string (s:string) : string :=
    match s with
    | EmptyString => """"
    | String c s' =>
        let quoted_s' := show_quoted_string s' in
        let n := nat_of_ascii c in
        if ascii_dec c "009" (* TAB *) then
          "\t" ++ quoted_s'
        else if ascii_dec c "010" (* NEWLINE *) then
               "\n" ++ quoted_s'
             else if ascii_dec c "013" (* CARRIAGE RETURN *) then
                    "\r" ++ quoted_s'
                  else if ascii_dec c """" (* DOUBLEQUOTE *) then
                         "\""" ++ quoted_s'
                       else if ascii_dec c "\" (* BACKSLASH *) then
                              "\\" ++ quoted_s'
                            else if ((n <? 32)%nat (* SPACE *)
                                     || (126 <? n)%nat (* ~ *))%bool then
                                   "\" ++ three_digit n ++ quoted_s'
                                 else
                                   String c quoted_s'
    end.

  #[global] Instance showString : Show string :=
    {|
      show s := String """" (show_quoted_string s)
    |}.

  
  #[global] Instance showPair {A B : Type} `{_ : Show A} `{_ : Show B} : Show (A * B) :=
    {|
      show p := match p with (a,b) => ("(" ++ show a ++ ", " ++  show b ++ ")")%string end
    |}.
  
  #[global] Instance showOpt {A : Type} `{_ : Show A} : Show (option A) :=
    {|
      show x := match x with
                | Some x => "Some " ++ (show x)
                | None => "None"
                end
    |}.

  #[global] Instance showList {A : Type} `{_ : Show A} : Show (list A) :=
    {|
      show l := append "[" (append (contents show l) "]")
    |}.

  Definition newline := String "010" ""%string.
  
End Show.
