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

Definition cont := option path.

(* SAZ: is 'cmd' (command) a good name for the pair of an instruction and its continuation? *)
Definition cmd  := (instr * cont)%type.
                          
Definition cfg := path -> option cmd.


(* The set of dynamic values manipulated by an LLVM program. *)
Inductive dval : Set :=
| DInt (n:nat)

.  

(* global or local environments *)
Definition env := list (raw_id * dval).
Inductive frame : Set :=
| KRet (e:env) (id:raw_id) (q:path)
.       
          

Definition stack := list frame.
Definition state := (path * env * stack)%type.

Definition id_of_path (p:path) : option raw_id :=
  match p with
  | (_, IId id) => Some id
  | _ => None
  end.

Definition lookup_env (e:env) (id:raw_id) : option dval :=
  None.

Fixpoint eval_op (e:env) (o:value) : option dval :=
  None.


Fixpoint step (CFG:cfg) (s:state) : option state :=
  let '(p, e, k) := s in
  do cmd <- CFG p;
    let '(i, q) := cmd in

    match i, q  with
    | INSTR_Op op, Some p' =>
      match id_of_path p, eval_op e op with
      | Some id, Some dv => Some (p', (id, dv)::e, k)
      | _, _ => None
      end

    | INSTR_Call f args, Some p' =>
      match id_of_path p, 
      

    (* PHI Evaluation is handled as part of jump *)
    | INSTR_Phi t args, _ => None  (* Cannot directly execute a Phi *)

                              
    | INSTR_Alloca t nb align, _ => None  (* typ, nb el, align *)

    | INSTR_Load volatile t ptr align, Some p' => None
    | INSTR_Store volatile val ptr align, None (* SHOULD NOT DEFINE *) => None


    | INSTR_Ret v, None =>
      None

    | INSTR_Ret_void, None =>
      None

    | INSTR_Br v br1 br2, None =>
      None
        
    | INSTR_Br_1 br, None =>
      None
        
    | INSTR_Unreachable, _ => None

    | INSTR_Switch v default_dest br, None => None
    | INSTR_IndirectBr v brs, None => None  (* address * possible addresses (labels) *)
    | INSTR_Resume v, None => None
    | INSTR_Invoke fnptrval args to_label unwind_label, _ => None
                                                              
    | ( INSTR_Fence
      | INSTR_AtomicCmpXchg
      | INSTR_AtomicRMW
      | INSTR_VAArg
      | INSTR_LandingPad), _ => None

                              
    | _, _ => None
    end.