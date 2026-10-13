# Testing vs. `llubi`
Steve wrote and ran a suite of UB-related (and other tests) against `llubi`, LLVM's now-official UB-aware interpreter. 
We did fairly well: we are missing a few cases w.r.t. `llubi` (in particular, calling a non-function global pointer, such as an array, yields an Uninterpreted Call in our semantics but UB in theirs.)
There is a chart Steve has with improvements he will make. 

# CTrees 
The refactor is nearly complete and Roger had a few questions before wrapping up. 
It is now clear that the weak bisimilarity problem- that is, stating a more useful version of weak bisimilarity over ctrees (e.g. that may respect bind, be termination sensitive, etc). 
is a problem to punt for later, as we want to get this refactor done as soon as possible so Vellvm is unblocked. 

From Yannick:
## The vis-splitting change

Having `vis e k -obs e v> k v` has two issues

When considering strong simulation `<=`, we have `trigger fail <= t` for any `t`. This can be fixed via complete strong simulation, but is weird
When considering strong bisimulation `~`, we do not respect interpretation. With a `e : E bool` event, `P = (e.(1|2) + e.(3|4))` and `Q =(e.(3|2) + e.(1|4))` then `P ~ Q`. However if `h e = Step e` then strong simulation breaks after interpretation. Once `vis e k -ask e> ?k -rcv e v> k v` then it is no longer true that `P ~ Q` and I believe that `forall h, Proper (sbism ==> sbisim)  (interp h)`


## Challenges ahead

There are orthogonal difficulties left after this full change. Essentially `Guard^ω <= t` for all `t`, much like `trigger fail` did before the split. Paired with the fact that `Guard` is the constructor guarding iteration, it may be troublesome.


Again, one answer is to simply say: let's use complete strong simulations! That is true, but the definition is not very comfortable in that the productivity constraint is quite global. 
Nicolas in his popl paper defines an alternative termination sensitive refinement `<<`: we may want to use this?
However my understanding is that `<<` does not respect `~`. If that is confirmed, how do we resolved the tension?


Orthogonally, a solution for adequate support for UB is in Nicolas's paper, and support for OOM should be symmetric.

## More immediate things


But these questions come up once having settled on a first semantics for Vellvm (with the important note that the exact choice of semantics may be tied to the equalities and refinements available, but we need a basis).
The relationship between model and executable interpreter should be reframed in terms of a scheduler for the branching events of the model and therefore a refinement for free
The move to ctrees should enable the modelling of concurrency features
