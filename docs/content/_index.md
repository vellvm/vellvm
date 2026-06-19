---
title: "Vellvm"
---

[Vellvm](https://github.com/vellvm/vellvm) is a specification of [LLVM IR](https://www.llvm.org/) implemented in [Rocq](https://rocq-prover.org). The Vellvm framework provides an abstract semantics aimed at _formal verification_ of LLVM-based software and optimizations passes, along with an _executable interpreter_ suitable for running LLVM IR code for testing purposes. The interpreter is proved to be a valid refinement of the spec.

# Getting Started

1. Follow the installation instructions in the [`README`](https://github.com/vellvm/vellvm/blob/dev/README.md) to get the `vellvm` executable and add it to your `$PATH`.

2. Try out `vellvm` from the command line, e.g., in the root of the project repo:

```bash
~/vellvm> vellvm -interpret tests/ll/factorial.ll 
(* -------- Vellvm Test Harness -------- *)
Processing: tests/ll/factorial.ll
Program terminated with: i64 120
```

3. Use `vellvm -help` to list command-line options

---

# Digging Deeper

- Find the [Vellvm source on github](https://github.com/vellvm/vellvm/) {{< img src="images/git-icon.svg" style="height:15px" >}} 

- Find out more [about the Vellvm framework](about)

- Learn how to [run and add test cases](tests)

- Understand the [structure of the semantics](structure)

- Take a look at our [research papers](research)

- Check out the [FAQ](faq)

---

# Related Projects

- [Interaction Trees](https://github.com/DeepSpec/InteractionTrees) - interactive, nonterminating, effectful programs in Rocq

- [CTrees](https://github.com/vellvm/ctrees) - ITrees with nondeterministic _choices_

- [Helix](https://github.com/vzaliva/helix) - A Rocq DSL for high-performance numerical algorithms that compiles to Vellvm

- [DeepSpec](http://deepspec.org) - Formal verification research

---

# Acknowledgments

Vellvm is being developed at the [University of Pennsylvania](https://www.upenn.edu) with 
collaborators at [Inria](https://www.inria.fr).

## Recent Contributors

 - [Steve Zdancewic](https://www.cis.upenn.edu/~stevez)
 - [Yannick Zakowski](https://cambium.inria.fr/~yzakowsk/)
 - [Calvin Beck](https://scholar.google.com/citations?user=XdZ9xysAAAAJ&hl=en)
 - [Irene Yoon](https://www.ireneyoon.com/)
 - [Gary (Hanxi) Chen](https://www.hanxic.com/)
 - [Roger Burtonpatel](https://rogerburtonpatel.github.io/)

## Funding

Funding for the Vellvm project has been provided by the NSF and DARPA. 

{{< img src="images/NSF_Official_logo_Med_Res_600ppi.png" style="height:120px" >}}
{{< img src="images/Darpa-logo-2026.png" style="height:110px" >}}

See the [Research Page](research) for more details.

