From Coq Require Import
     List
     ZArith.

From Vellvm Require Import
     Utils.NonEmpty
     Utils.Default
     Utils.NMaps.

Import ListNotations.

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
      dl_stack_align           : option N;
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

Record Foo : Type :=
  mkFoo { blah : bool; flurp : nat }.

#[global] Instance DefaultEndianess : Default Endianess :=
  {
  def := ENDIAN_BIG
  }.

#[global] Instance DefaultAlignment : Default Alignment :=
  {
  def := ALIGN_ABI_PREF 64 64
  }.

#[global] Instance DefaultPointerSize : Default PointerSize :=
  {
  def := {| ps_size := 64;
            ps_alignment := def;
            ps_index_size := None
         |}
  }.

#[global] Instance DefaultFunctionPointerAlignment : Default FunctionPointerAlignment :=
  {
  (* TODO: Double check this, not specified in LangRef. *)
  def := FPA_I 64
  }.

#[global] Instance DefaultMangling : Default Mangling :=
  {
  (* TODO: Double check this, not specified in LangRef. *)
  def := MANGLING_ELF
  }.

#[global] Instance DefaultDataLayout : Default DataLayout :=
  {
  def :=
    {| dl_endianess := def;
       dl_stack_align := None;
       dl_program_address_space := 0;
       dl_global_address_space  := 0;
       dl_alloca_address_space  := 0;
       dl_pointer_alignments  := nempty def [];
       dl_integer_alignments :=
         NM_from_list [(1, ALIGN_ABI_PREF 8 8);
                       (8, ALIGN_ABI_PREF 8 8);
                       (16, ALIGN_ABI_PREF 16 16);
                       (32, ALIGN_ABI_PREF 32 32);
                       (64, ALIGN_ABI_PREF 32 64)
                      ]%N;
       dl_vector_alignments :=
         NM_from_list [(64, ALIGN_ABI_PREF 64 64);
                       (128, ALIGN_ABI_PREF 128 128)
                      ]%N;
       dl_floating_point_alignments :=
         NM_from_list [(16, ALIGN_ABI_PREF 16 16);
                       (32, ALIGN_ABI_PREF 32 32);
                       (64, ALIGN_ABI_PREF 64 64);
                       (128, ALIGN_ABI_PREF 128 128)
                      ]%N;
       dl_function_pointer_alignment := def;
       dl_mangling := def;
       (* TODO: double check this, not specified in LangRef... *)
       dl_native_integer_widths :=
         NS_from_list [8; 16; 32; 64]%N;
       dl_aggregate_alignment := ALIGN_ABI_PREF 0 64
    |}
  }.
