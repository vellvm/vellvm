(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)
%{
open Imp
open Integers

let str = Camlcoq.coqstring_of_camlstring
(* let coq_of_int = Camlcoq.Nat.of_int *)
(* let coq_of_int n = Imp.Int64.signed (Camlcoq.Z.of_sint n) *)
let coq_of_int n = Int64.repr (Camlcoq.Z.of_sint n)

%}

%token EOF
%token <int>  INT
%token <string> IDENT
%token IFB      
%token THEN
%token FI
%token ELSE     
%token WHILE    
%token DO
%token END
%token SKIP
%token TRUE
%token FALSE
%token SEMISEMI /* ;; */
%token PLUS     /* + */
%token DASH     /* - */
%token STAR     /* * */
%token EQ       /* = */
%token LTEQ     /* <= */
%token LPAREN   /* ( */
%token RPAREN   /* ) */
%token BANG     /* ! */
%token AMPER    /* & */
%token COLONCOLONEQ /* ::= */

/* ---------------------------------------------------------------------- */

%start com_top
%type <Imp.aexp> aexp
%type <Imp.bexp> bexp
%type <Imp.com> com
%type <Imp.com> com_top

%left PLUS DASH
%left STAR
%right SEMISEMI
%left AMPER
%nonassoc BANG
%%

com_top:
  | c=com EOF { c }

ident:
  | x=IDENT  { (str x) }

aexp:
  | n=INT                   { ANum (coq_of_int n) }
  | id=ident                { AId id }
  | a1=aexp PLUS a2=aexp    { APlus(a1, a2) }
  | a1=aexp DASH a2=aexp    { AMinus(a1, a2) }
  | a1=aexp STAR a2=aexp    { AMult(a1, a2) }
  | LPAREN a=aexp RPAREN    { a } 

bexp:
  | TRUE                    { BTrue }
  | FALSE                   { BFalse }
  | a1=aexp EQ a2=aexp      { BEq(a1, a2) }
  | a1=aexp LTEQ a2=aexp    { BLe(a1, a2) }
  | BANG b=bexp             { BNot(b) }
  | b1=bexp AMPER b2=bexp   { BAnd(b1, b2) }
  | LPAREN b=bexp RPAREN    { b }

com:
  | SKIP                         { CSkip }
  | x=ident COLONCOLONEQ a=aexp  { CAss(x, a) }
  | c1=com SEMISEMI c2=com       { CSeq(c1,c2) }
  | IFB b=bexp THEN c1=com ELSE c2=com FI   { CIf(b,c1,c2) }
  | WHILE b=bexp DO c=com END    { CWhile(b, c) }


