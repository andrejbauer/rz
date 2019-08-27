# RZ

**RZ** is a tool for automatic generation of program specifications from
definitions of mathematical theories. It was written by [Chris
Stone](http://www.cs.hmc.edu/~stone/) and [Andrej Bauer](http://andrej.com). The
purpose of RZ is to help programmers and mathematicians design data structures
which properly implement mathematical structures (algebras, real numbers,
Hilbert spaces, etc.)

A good starting point to learn about RZ is the paper ["RZ: a Tool for Bringing
Constructive and Computable Mathematics Closer to Programming
Practice"](http://math.andrej.com/2007/01/21/rz-a-tool-for-bringing-constructive-and-computable-mathematics-closer-to-programming-practice/). You may also browse [RZ-related blog
posts](http://math.andrej.com/category/rz/).


## Compiling RZ

RZ is a pretty old piece of software written in the
[OCaml](http://www.ocaml.org/) programming language.

You will also need [make](http://www.gnu.org/software/make/) and possibly
`diff`, which you likely have already.


To compile RZ, perform the following steps from the command line

* change to the subdirectory `src`
* run `make` to create the executable `rz.exe` (so called also on Linux and MacOS)
* optionally, to test whether RZ has compiled properly, run `make test`.


## Usage and help

Run

    ./rz.exe --help

to see basic usage information.

The subdirectory [`examples`](./examples) contains examples of RZ input files.
If you run RZ on them, it will generate corresponding output file (with
extension `.mli`).

Unfortunately, there is no user manual for RZ at this time. If you need help
with getting RZ to work, please contact us.
