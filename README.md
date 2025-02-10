# Linear Actris Artifact

A version of Actris where Hoare triples guarantees deadlock and leak freedom.

This artifact contains Coq source code that proves the results in the paper.

## Installation

This artifact has been tested with Coq 8.20.0 and OCaml 5.1.0.
A custom version of Iris is required, see below. The features of this custom version will be upstreamed to Iris in the future.

1. Install `opam`. You can find the instructions on https://opam.ocaml.org/doc/Install.html
  Do not forget to use `opam init` and add `eval $(opam env)` to your `.bashrc` or `.zshrc` file. This makes the `coqc` command, and other commands installed by `opam`, available in your terminal.
2. Install `git`. You can find the instructions on https://git-scm.com/book/en/v2/Getting-Started-Installing-Git
3. Make a directory that will contain the artifact, and `cd` into it:

        mkdir artifact
        cd artifact

4. Download a custom version of Iris using

        git clone -b robbert/sbi https://gitlab.mpi-sws.org/iris/iris.git

5. Build and install this version of Iris using

        cd iris
        opam pin add -y coq-iris .
        cd ..

6. Download and unzip the `sources.zip` file, and build it:

        unzip sources.zip
        make

## File structure

- [`prelude/`](theories/prelude): Miscellaneous lemmas and definitions that could be upstreamed to std++ and Iris.
- [`algebra/`](theories/algebra): Algebraic structures, including step-indexed multisets for modeling the incoming edges of the connectivity graph.
- [`lang/`](theories/lang): The syntax and operational semantics of our language ChanLang, including some meta theory and notations.
- [`base_logic/`](theories/base_logic): The model, WP rules, and adequacy one-shot LinearActris logic.
- [`session_logic/`](theories/session_logic): The multi-shot LinearActris logic, derived in multiple layers from the one-shot LinearActris logic.
- [`examples/`](theories/examples): Examples
  * [`tour.v`](theories/examples/tour.v): Examples from this paper, Section 2
  * [`basics.v`](theories/examples/basics.v): Examples from the Actris 2.0 paper, Section 1 and 10
  * [`sort.v`](theories/examples/sort.v): Example from Actris 2.0 paper, Section 5
  * [`sort_br_del.v`](theories/examples/sort_br_del.v): Example from Actris 2.0 paper, Section 5
  * [`sort_fg.v`](theories/examples/sort_fg.v): Example from Actris 2.0 paper, Section 5
  * [`list_rev.v`](theories/examples/list_rev.v): Example from Actris 2.0 paper, Section 6.3
- [`logrel/`](theories/logrel): The semantic session type system
  * [`theories/logrel/examples`](theories/logrel/examples): Examples of using the semantic type system to type check sample programs.
