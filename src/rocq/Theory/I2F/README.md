# Infinite to Finite Correctness

## General idea

By infinite/finite, we refer to the space of addresses available in the memory model. Vellvm takes the perspective of reasoning in an infinite model as much as possible, where neither `alloc` nor `PtoI` fail, and then lower itself to a finite model.

In the semantics, this is captured by parameterizing the development by an instance of the type class `IPtr`, or more broadly by `Params`. Subsequently, two implementations are provided: `IPZ` and `IP64Bit`.

In this folder, we prove that this lowering is sound in the sense that the resulting computations are bisimilar, _except_ that the finite model may suddenly run out of memory---it is in this sense treated dually to a non-time-travelling UB.

At the level of the denotation, where events are uninterpreted, we introduce a variant of `rutt`, named `ruttc`, to do so (see `Utils/rutt_cutoff.v`). The differences can be summed up as follows:

- [eutt RR] : weakly bisimilar computations whose leaves are related by [RR]
- [rutt REv RAns RR] : weakly bisimilar computations whose leaves are related by [RR], events by [REv], and answers by [RAns]
- [ruttc Rcutl Rcutr REv RAns RR] : weakly bisimilar computations whose leaves are related by [RR], events by [REv], and answers by [RAns], and such that if an event predicated by [Rcutl] occurs in the left tree, then any subtrees are related, and symmetrically for [Rcutr]

The crux of the refinement then relies on:
- Lifting the injection of [int64] into [Z] to a relation
- Lifting this relation in particular to dynamic values
- Using [Rcutr] to capture that [OOM] can be introduced by lowering
- Using [REv/RAnv] to lift the relation on dynamic values and addresses to relate events at both levels
- Propagating everywhere the invariant on computed dynamic values

## Structure of the folder

- [refinement.v] : defining the refinement relation and its elementary meta-theory
- [exp.v] : proving the refinement for expressions---this contains most of the heavy-lifting in the sense that a lot of arithmetic and address manipulation happens there
- [denotation.v] : lifting things all the way to [denote_mcfg]---this goes more smoothly once the structural results are in place
- [memS.v] : defines the same notion of refinement _at the memS level_
- [memory.v] : defines and prove a refinement for the memory model _at the memM level_
- [interp.v] : transporting the invariant along [interp_mcfg], proving it for every handler on the way
- [toplevel.v] : finally lifting things to the top level

## TODO

The current refinement is established for the interpreter. We will naturally want it for the model once it is plugged in.

Most of the code should be reused. The [denotation] and [memory] are completely shared. Most of the [interp] should be shared as well.
The main lemma that is absolutely interpreter specific is [I2F_memM_interp],
which talks about the deterministic implementation of [memM]: it should be replaced by a similar lemma for the model implementation of it.
However there will be more ripples: we will also move into a different monad,
where the invariant will have to be expressed in its own way, and the structure adapted in consequence.

