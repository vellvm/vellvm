Definition MemPropT_lift_PropT {MemState X} {E} `{UBE -< E} `{OOME -< E} `{FailureE -< E} (spec : MemPropT MemState X) :
  stateT MemState (PropT E) X.
Proof.
  unfold PropT, MemPropT, stateT in *.
  refine
    (fun ms t =>
       (* UB *)
       (exists msg_spec,
           spec ms (raise_ub msg_spec)) \/
         (* Error *)
         ((exists msg,
              t ≈ (raise_error msg) /\
              exists msg_spec, spec ms (raise_error msg_spec))) \/
           (* OOM *)
           (exists msg,
               t ≈ (raise_oom msg) /\
               exists msg_spec, spec ms (raise_oom msg_spec)) \/
           (* Success *)
           (exists ms' x,
               t ≈ (ret (ms', x)) /\
               spec ms (ret (ms', x)))).
Defined.
