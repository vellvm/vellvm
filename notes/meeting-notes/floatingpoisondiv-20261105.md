# Meeting on Nov. 5th.

## FP and Poison
Steve has continued to work on building out Vellvm using Claude 
Yannick is curious about the intended behavior for floating point division by zero 

The shape of poison is determined by its type. An all-poison vector is canonically a single value of type DVALUE_POISON. We consider if this changes optimizations or behavior. 
Yannick’s question:
* If indeed poison can be refined by any value, it can be refined by 0
* But I thought division by 0 was UB
* Which is in contradiction with this division by poison being poison

IEEE suggests floating point division by zero may return positive infinity, negative infinity, or NaN. 
Specifics are on pages 52 & 53 of this document. 
https://www-users.cse.umn.edu/~vinals/tspot_files/phys4041/2020/IEEE%20Standard%20754-2019.pdf

Peter Sewell found a performance bug in Vellvm raised by left shifts of unspecified sizes (e.g. -1) that led to the interpreter OOM'ing 

## ctrees
We discuss the imminent refactor to ctrees. The choice of 'ctrees everywhere' vs. 'ctrees only in the memory model' remains open 
but we decide to begin in the memory model. ctrees become the model at this stage, and there are opportunities for expansion into 
other areas such as draw. 

In the chain of interpreters right now, we have local/global/other memory at once in a single pass. If we separate part into itrees and part into ctrees, 
there will likely be two passes. 

Sebastian Ertel's group offers another model of Angelic and Demonic nondeterminism based purely on itrees, which is more similar to Paul He and Lucas Silver's work. 
The main idea is still to make a model in ctrees, but we may go in that direction. 

Steve notes there may be other areas of nondeterminism in which ctrees could be useful. 
