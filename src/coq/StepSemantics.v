Require Import Arith List.
Require Import String.
Require Import Omega.
Require Import Vellvm.Util Vellvm.Ollvm_ast.
Import ListNotations OptionNotations.

Set Implicit Arguments.

(* This definition of paths is relative to a single, implicit module, which is 
   given by a list of toplevel_entries, per the Ollvm_ast datatypes. 

   path p = (f, id) 
      f : the function identifier 
     id : location of the instruction within the function
*)
Definition path := (ident * instr_id)%type.

Inductive cmd : Set :=
| Step  (i:instr) (p:path)
| Jump  (i:instr)
| Phis  (phis : list (instr_id * instr)) (p:path)
.                    
                          
Definition cfg := path -> option cmd.


(* The set of dynamic values manipulated by an LLVM program. This datatype
   uses the "Expr" functor from the Ollvm_ast definition, injecting new base values.
   This allows the semantics to do 'symbolic' execution for things that we don't 
   have a way of interpreting concretely (e.g. undef).   
*)
Inductive dvalue : Set :=
| DV : Expr dvalue -> dvalue
| DVALUE_CodePointer (p : path)
| DVALUE_Addr (a:nat)
.  

(* global or local environments *)
Definition env  := list (raw_id * dvalue).
Inductive frame : Set :=
| KRet      (e:env) (id:raw_id) (q:path)
| KRet_void (e:env) (q:path)
.       
          

Definition stack := list frame.
Definition state := (path * env * stack)%type.

Definition id_of_path (p:path) : option raw_id :=
  match p with
  | (_, IId id) => Some id
  | _ => None
  end.

Definition lookup_env (e:env) (id:raw_id) : option dvalue :=
  None.

Fixpoint eval_op (e:env) (o:value) : option dvalue :=
  None.


Fixpoint step (CFG:cfg) (s:state) : option state :=
  let '(p, e, k) := s in
  do cmd <- CFG p;
    match cmd with
    | Phis _ _ => None  (* not handled here *)
      
    | Step (INSTR_Op op) p' =>
      match id_of_path p, eval_op e op with
      | Some id, Some dv => Some (p', (id, dv)::e, k)
      | _, _ => None
      end
        
    | Step (INSTR_Call f args) p' => None
  
    | Step (INSTR_Alloca t nb align) p' => None  (* typ, nb el, align *)

    | Step (INSTR_Load volatile t ptr align) p' => None
    | Step (INSTR_Store volatile val ptr align) p' => None

    | Step (INSTR_Unreachable) _ => None
                                                       
    | Jump (INSTR_Ret v) =>
      None

    | Jump (INSTR_Ret_void) =>
      None

    | Jump (INSTR_Br v br1 br2) =>
      None
        
    | Jump (INSTR_Br_1 br) =>
      None
        
    | Jump (INSTR_Switch v default_dest br) => None
    | Jump (INSTR_IndirectBr v brs) => None  (* address * possible addresses (labels) *)
    | Jump (INSTR_Resume v) => None
    | Jump (INSTR_Invoke fnptrval args to_label unwind_label) => None
                                                              
    | Step (
        INSTR_Fence
      | INSTR_AtomicCmpXchg
      | INSTR_AtomicRMW
      | INSTR_VAArg
      | INSTR_LandingPad) _ => None

                              
    | _ => None
    end.