From Coq Require Import
     List
     String
     Ascii
     FSets.FMapAVL
     FSets.FSetAVL
     Structures.OrderedTypeEx
     ZArith.

From Vellvm Require Import
     Utils.NonEmpty.


(* N maps *)
Module NM := FMapAVL.Make(Coq.Structures.OrderedTypeEx.N_as_OT).
Definition NMap := NM.t.

(* N sets *)
Module NS := FSetAVL.Make(Coq.Structures.OrderedTypeEx.N_as_OT).
Definition NSet := NS.t.


(* Memory model layout information... *)
Variant Alignment : Type :=
| ALIGN_ABI (abi : N)
| ALIGN_ABI_PREF (abi pref : N)
.

Variant FunctionPointerAlignment : Type :=
| FPA_I (abi : N) (* Indepedent of alignment of functions *)
| FPA_N (abi : N) (* Multiple of abi and multiple of alignment of functions *)
.

Variant Endianess : Type :=
| ENDIAN_BIG
| ENDIAN_LITTLE
.

Variant Mangling : Type :=
| MANGLING_ELF
| MANGLING_MIPS
| MANGLING_MACH
| MANGLING_WINDOWS_X86_COFF
| MANGLING_WINDOWS_COFF
| MANGLING_WINDDOWS_XCOFF
.

Record PointerSize : Type :=
  mk_PointerSize
    {
      ps_size : N;
      ps_alignment : Alignment;
      ps_index_size : option N;
    }.

Record DataLayout : Type :=
  mk_DataLayout
    {
      dl_endianess             : Endianess;
      dl_stack_align           : N;
      dl_program_address_space : N;
      dl_global_address_space  : N;
      dl_alloca_address_space  : N;

      (* Not sure about this, but non-empty list for address spaces *)
      dl_pointer_alignments : NonEmpty PointerSize;

      (* Integer alignments... Map from size to alignment... *)
      dl_integer_alignments : NMap Alignment;

      (* Vector alignment, Map from bit-size to alignment *)
      dl_vector_alignments : NMap Alignment;

      dl_floating_point_alignments : NMap Alignment;

      dl_function_pointer_alignment : FunctionPointerAlignment;

      dl_mangling : Mangling;

      dl_native_integer_widths : NSet;

      (* TODO: add non-integral pointer types *)

      (* Alignment for aggregate types *)
      dl_aggregate_alignment : Alignment
    }.
