# FOR ARTIFACT EVALUATION

The description below has been augmented with comments that indicate the
relevant parts of the ICFP paper.  We've called them out using by marking them
with **ARTIFACT** so they are easier to find.  We also list the specific claims
in the paper and their locations in the development below:

### Definitions / Lemmas 

- [PropT laws from Figure 7](src/coq/Utils/PropT.v) search for comments including "Figure 7"
- [laws from Figure 8](src/coq/Utils/PropT.v) search for comments including "Figure 8"
- [Definition 5.1](src/coq/Utils/PropT.v) search for "Definition 5.1"
- [Definition 5.2](src/coq/Utils/PropT.v) search for "Definition 5.2"
- [Lemma 5.4](src/coq/Utils/PropT.v) search for "Lemma 5.4"
- [Lemma 5.5](src/coq/Utils/PropT.v) search for "Lemma 5.5"
- [Definition 5.6](src/coq/Theory/Refinement.v) search for "Definition 5.6"
- [Lemma 5.7](src/coq/Theory/TopLevelRefinements.v) search for "Lemma 5.7" (see related definitions in [Refinement.v](src/coq/Theory/Refinement.v)
- [Lemma 5.8](src/coq/Theory/TopLevelRefinements.v) search for "Lemma 5.8"

### ITrees ###

Although we have made significant contributions to the itree library for the sake of this project, most of it
is orthogonal to the material described in this paper, and can be treated entirely as an external library to understand this project.

The content of Section 5.1 that gives a taste of how the underlying equational theory works can be found in more details in
the files [Eq.v](https://github.com/DeepSpec/InteractionTrees/blob/master/theories/Eq/Eq.v) and [UpToTaus.v](https://github.com/DeepSpec/InteractionTrees/blob/master/theories/Eq/UpToTaus.v) in the [Interaction Trees github repo](https://github.com/DeepSpec/InteractionTrees)


### Unit Tests

After compiling vellvm the development, running `src/vellvm --test` should successfully run 145 unit tests.  Running
`src/vellvm --test-file tests/helix/test_dynwin64.ll` should successfully run the HELIX test case mentioned in Section 7 of the paper.

### QuickChick Tests

The QuickChick tests can be run using the command `make qc-tests` in
the source directory. This test generates random LLVM programs that
are then run with the Vellvm interpreter and the `clang` compiler
(which must also be installed). If QuickChick fails to find a counterexample (i.e., the tests pass) it will say "Gave up!"

[comment]: # (TODO: Calvin add something here)


### HELIX Case Study

The paper's Section 6 refers to our use of this library for verifying a
front-end for the Helix tool chain.  That development is available in a separate
repository [Helix](https://github.com/vzaliva/helix) and it relies on a slightly
older version of Vellvm (Helix requires MetaCoq which isn't compatible yet with
coq v. 8.13) that was current at the time the paper was submitted. 
Since the Helix development points to another specific version of this repository and
is still under active development, we chose to not include it in this artifact. 
The interested reviewer can however get it and run it directly from its Github.

## Getting started

There are two options: build Vellvm from scratch in your own environment, or
use the virtual machine image we provide.

### Building in your own environment
Our development has been packaged into vellvm.tar.gz. See [Installing and Compiling Vellvm](#installing-and-compiling-vellvm) for build instructions.


### Using the virtual machine image
The Debian QEmu image has been packaged into `vellvm.tar.gz`. 
Run the image with `start.sh` for Unix-like systems (you might need `sudo` for 
Linux) and `start.bat` for Windows.

 * Username: artifact
 * Password: password

If the VM does not start, check `Debugging.md` provided in the directory.

See [Installing and Compiling Vellvm](#installing-and-compiling-vellvm) to 
compile and run the project.