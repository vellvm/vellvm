---
title: "Research"
---


# Related Publications

 - "Vellvm: Formalizing the informal LLVM (Experience Report)", ([NFM25](http://www.cis.upenn.edu/~stevez/papers/nfm25.pdf)) Calvin Beck, Hanxi Chen, and Steve Zdancewic. 

 - "Choice trees: Representing and reasoning about nondeterministic, recursive, and impure programs in Rocq" ([JFP'25](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/choice-trees-representing-and-reasoning-about-nondeterministic-recursive-and-impure-programs-in-rocq/797B95A45813CAE54CFFFA3D7B163BA4)), Nicolas Chappe, Paul He, Ludovic Henrio, Eleftherios Ioannidis, Yannick Zakowski, and Steve Zdancewic. 

 - "A Two-Phase Infinite/Finite Low-Level Memory Model" ([ICFP'24](https://icfp24.sigplan.org/details/icfp-2024-papers/28/A-Two-Phase-Infinite-Finite-Low-Level-Memory-Model-Reconciling-Integer-Pointer-Casts)), Calvin Beck, Irene Yoon, Hanxi Chen, Yannick Zakowski, Steve Zdancewic

- "Choice Trees: Representing Nondeterministic, Recursive, and Impure Programs in Coq
 ([POPL'23](http://www.cis.upenn.edu/~stevez/papers/CHHZZ23.pdf)) Nicolas Chappe, Paul He, Ludovic Henrio, Yannick Zakowski, and Steve Zdancewic

 - "Formal Reasoning About Layered Monadic Interpreters" ([ICFP'22](https://doi.org/10.1145/3547630)), Irene Yoon, Yannick Zakowski, and Steve Zdancewic.

 - "Modular, Compositional, and Executable Formal Semantics for LLVM IR" ([ICFP'21](https://icfp21.sigplan.org/details/icfp-2021-papers/6/Modular-Compositional-and-Executable-Formal-Semantics-for-LLVM-IR)),
    Yannick Zakowski, Calvin Beck, Irene Yoon, Ilia Zaichuk, Vadim Zaliva, Steve Zdancewic

 - "An Equational Theory for Weak Bisimulation via Generalized Parameterized Coinduction" ([CPP'20](http://www.cis.upenn.edu/~stevez/papers/ZHHZ20.pdf)) Yannick Zakowski, Paul He, Chung-Kil Hur, and Steve Zdancewic.

 - "Interaction Trees" ([POPL'20](http://www.cis.upenn.edu/~stevez/papers/XZHH+20.pdf)), Li-yao Xia, Yannick Zakowski, Paul He, Chung-Kil Hur, Gregory Malecha, Benjamin C. Pierce, and Steve Zdancewic.

 - "Verifying Dynamic Race Detection" ([CPP'17](http://www.cis.upenn.edu/~stevez/papers/MPZD17.pdf))

 - "A Formal C Memory Model Supporting Integer-Pointer Casts" ([PLDI'15](http://www.cis.upenn.edu/~stevez/papers/KHM+15.pdf)), Jeehoon Kang, Chung-Kil Hur, William Mansky, Dmitri Garbuzov, Steve Zdancewic, and Viktor Vafeiadis.

 - "An Axiomatic Specification for Sequential Memory Models" ([CAV'15](http://www.cis.upenn.edu/~stevez/papers/MGZ15.pdf)), William Mansky, Dmitri Garbuzov, and Steve Zdancewic

 - "WatchdogLite: Hardware-Accelerated Compiler-Based Pointer Checking" ([CGO'14](http://www.cis.upenn.edu/~stevez/papers/4tr.pdf)), Santosh Nagarakatte, Milo M. K. Martin, Steve Zdancewic

 - "Formal Verification of SSA-Based Optimizations for LLVM" ([PLDI'13](http://www.cis.upenn.edu/~stevez/papers/ZNMZ13.pdf)), Jianzhou Zhao, Santosh Nagarakatte, Milo M. K. Martin, and Steve Zdancewic.

 - "Hardware-enforced Comprehensive Memory Safety" ([IEEE Micro Top Picks 2013](http://ieeexplore.ieee.org/xpl/articleDetails.jsp?arnumber=6487479)), Santosh Nagarakatte; Milo M.K. Martin; Steve Zdancewic

 - "Ironclad C++: A Library-Augmented Type-Safe Subset of C++" ([OOPSLA'13](http://www.cis.upenn.edu/~stevez/papers/DENO+13.pdf)), Christian DeLozier, Richard Eisenberg, Santosh Nagarakatte, Peter-Michael Osera, Milo M. K. Martin, Steve Zdancewic

 - "Formalizing an SSA-based Compiler for Verified Advanced Program Transformations", Jianzhou Zhao's Ph.D. dissertation, 2013

 - "Formalizing the LLVM Intermediate Representation for Verified Program Transformations" ([POPL'12](http://www.cis.upenn.edu/~stevez/papers/ZNMZ12.pdf)), Jianzhou Zhao, Santosh Nagarakatte, Milo M. K. Martin, and Steve Zdancewic.

 - "Mechanized Verification of Computing Dominators for Formalizing Compilers" ([CPP'12](http://www.cis.upenn.edu/~stevez/papers/ZZ12.pdf)), Jianzhou Zhao and Steve Zdancewic.

 - "CETS: Compiler-Enforced Temporal Safety for C" ([ISMM'10](http://www.cis.upenn.edu/~stevez/papers/NZMZ10.pdf)), Santosh Nagarakatte, Jianzhou Zhao, Milo M. K. Martin, and Steve Zdancewic

 - "SoftBound: Highly Compatible and Complete Spatial Memory Safety for C" ([PLDI'09](http://www.cis.upenn.edu/~stevez/papers/NZMZ09.pdf)), Santosh Nagarakatte, Jianzhou Zhao, Milo M. K. Martin, and Steve Zdancewic. 


# Vellvm History

{{< img src="images/vellvm-logo.png" style="height:120px" >}}

{{< img src="images/deepspec-logo-300dpi.png" style="height:110px" >}}

  - Vellvm started as an outgrowth of the [SoftBound and CETS](https://github.com/santoshn/softboundcets-34) projects around 2010.  See a [more modern implementation](https://github.com/Fraunhofer-AISEC/softboundcets) by Orthen et. al. of those ideas.

  - The "original" Vellvm development code base (called Vellvm-legacy) was built by Jianzhou Zhao and is [available here](https://github.com/vellvm/vellvm-legacy). (But the code is quite bitrotted.)

  - Vellvm was a component of the [DeepSpec NSF Expedition](http://www.deepspec.org).


# Past Contributors

Vellvm has had many contributors over the years. Some contributed to the "legacy" Vellvm project and some contributed to its modern incarnation.  Thanks to all of them!

 - Calvin Beck
 - Roger Burtonpatel
 - Hanxi (Gary) Chen
 - Noé de Santo
 - Vivien Durey
 - Dmitri Garbuzov
 - Eduardo Gonzalez
 - Olek Gierczak
 - Nicolas Koh
 - William Mansky
 - Milo Martin
 - Joel McCarthy
 - Santosh Nagarakatte
 - Emmett Neyman
 - Christine Rizkallah
 - Valentin Robert
 - Zak Sines
 - Nathan Sobotka
 - Alix Trieu
 - Vighnesh Vijay
 - Irene Yoon
 - Robert Zajac
 - Ilia Zaichuk
 - Yannick Zakowski
 - Vadim Zaliva
 - Richard Zhang
 - Jianzhou Zhao

# Funding

- NSF Grant 1521539 Collaborative Research: Expeditions in Computing: *The Science of Deep Specification*

- NSF Grant XPS 1337174 CLCCA: *Improving Parallel Program Reliability Through Novel Approaches to Precise Dynamic Data Race Detection*

- NSF Grant 1065166: *Validating Program Transformations in a Mechanized LLVM*

- NSF Grant 2247088 *Secure and Formally-verified Low-level Languages*

- DARPA HR001124S0035 *MACCHIATO: Machine-Learning Assisted Compilers for
Computationally Heterogeneous Infrastructures with Automated
Transformations and Optimizations* (with Peraton Labs)

- DARPA TRACTOR: *CLEAR: Concurrent LLVM Equivalence Analysis through Refinement*

- NSF REU Grant CNS-2244494 *Research Experience in Programming Languages (REPL)* 

{{< img src="images/NSF_Official_logo_Med_Res_600ppi.png" style="height:120px" >}}
{{< img src="images/Darpa-logo-2026.png" style="height:110px" >}}


