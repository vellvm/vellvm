
    Definition handle_intrinsic : IntrinsicE dvalue ~>  MemState
      := fun T e =>
           match e with
           | Intrinsic t name args =>
               (* Pick all arguments, they should all be unique. *)
               (* TODO: add more variants to memcpy *)
               (* FIXME: use reldec typeclass? *)
               if orb (Rocqlib.proj_sumbool (string_dec name "llvm.memcpy.p0i8.p0i8.i32"))
                      (Rocqlib.proj_sumbool (string_dec name "llvm.memcpy.p0i8.p0i8.i64"))
               then
                 handle_memcpy_prop args;;
                 ret (inr DVALUE_None)
               else
                 if orb (Rocqlib.proj_sumbool (string_dec name "llvm.memset.p0i8.i32"))
                      (Rocqlib.proj_sumbool (string_dec name "llvm.memset.p0i8.i64"))
                 then
                   handle_memset_prop args;;
                   ret (inr DVALUE_None)
                 else
                   if (Rocqlib.proj_sumbool (string_dec name "malloc"))
                   then
                     addr <- handle_malloc_prop args;;
                     ret (inr (DVALUE_Addr addr))
                   else
                     if (Rocqlib.proj_sumbool (string_dec name "free"))
                     then
                       handle_free_prop args;;
                       ret (inr DVALUE_None)
                     else
                       raise_error ("Unknown intrinsic: " ++ name)
           end.

