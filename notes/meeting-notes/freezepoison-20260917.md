# Yannick's `freeze poison` Commentary, September 17th, 2026

For my own future self, just to recap the point discussed that may be a gap in the transition to undef-less, byte types, and bit-level poison:

In the old time, a non-initialized allocation would result in undef bytes in memory. Loading would load undef, and computing over it would draw from it
In the main branch, a non-initialized allocation would result in poison bytes in memory. Loading would load poison (even if we read several bytes and a single of these poison bytes are poison actually). Many manipulation of poison may trigger UB

In Steve's branch I believe, a non-initialized allocation would result in poison
bits in memory. Loading would still load poison though (even if we read several
bytes and a single of these poison bits are poison actually). Many manipulation
of poison may trigger UB 

We recall that `freeze (poison)` draws, but it is not sufficient, loading should
be finer grained I think? More generally I guess it is not clear to me anymore
what loading should do:

keep the defined bits, draw the poison bits, serialize the result?

Ah actually I also did change somehow the semantics of `load` , that's what I
thought, but we were not looking at the right place: it is done in the
denotation of the instruction, in `Denotation.v`: `v <- load dt a;; v' <- freeze v`

And this change was sufficient for the "eager UB" failing test to actually pass

However I do not think (but may be wrong?) that it is sufficient: it should happen this way, but also load should be fine-grained enough to not collapse the whole value into poison if only some of the ~~bytes~~ bits are poisoned, as is done in `main`

But perhaps that's already what Steve does, in which case as far as I can see we would be all good