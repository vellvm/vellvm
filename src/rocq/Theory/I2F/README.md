# Infinite to Finite Correctness

## General idea

By infinite/finite, we refer to the space of addresses available in the memory model. Vellvm takes the perspective of reasoning in an infinite model as much as possible, where neither `alloc` nor `PtoI` fail, and then lower itself to a finite model.

In the semantics, this is captured by parameterizing the development by an instance of the type class `IPtr`, or more broadly by `Params`. Subsequently, two implementations are provided: `IPZ` and `IP64Bit`.

In this folder, we prove that this lowering is sound in the sense that the resulting computations are bisimilar, _except_ that the finite model may suddenly run out of memory---it is in this sense treated dually to a non-time-travelling UB.

At the level of the denotaiton, where events are uninterpreted, we introduce a variant of `rutt`, named `ruttc`, to do so (see `Utils/rutt_cutoff.v`). The differences can be summed up as follows:

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

## TODO

We now need to push things down the interpretation stack. In particular we need.
- to express the invariant over [MemS] to show the refinement over the memory handler when agnostic to the semantics of non-deterministic operations (this will likely require axiomatizing how these operations relate on both sides)
- proving a meta-theorem to transport this result from [MemS] to stateful trees given sufficient hypotheses on this monad morphism
- proving meta-theorems to transport the result through the adequate handlers---first stateful trees, then stateful ctrees

