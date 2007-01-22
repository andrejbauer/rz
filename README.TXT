CONTENTS:

1. Basic information
   - availability
   - licence
   - version

2. Requirements
   - Objective Caml
   - Make

3. Compilation instructions

4. Usage and Help

1. Basic information
====================

The latest version of RZ is available at http://math.andrej.com/rz/,
together with other RZ resources.

RZ is an academic project. We have released the source code under the
MIT licence, see the file src/LICENCE.

Currently RZ is still in alpha testing. The file VERSION contains
exact information about this version of RZ.


2. Requirements:
================

To compile RZ, you will need:

* Objective Caml version 3.09 or later, see http://www.ocaml.org

  Very likely RZ will work with earlier versions of Objective Caml,
  but we have not tested this.

* Make

  Make is a tool which controls the generation of executables and
  other non-source files of a program from the program's source files.
  It is installed on most Linux/Unix systems. If you do not have it,
  get it from http://www.gnu.org/software/make/. On MS Windows you can
  get Make as part of the Cygwin environment, see
  http://www.cygwin.com/.

* Diff

  If you want to run the tests to make sure RZ has properly compiled,
  you need the diff utility. It is usually installed on Linux/Unix
  systems. Cygwin (http://www.cygwin.com/) provides it on Windows.


3. How to compile
=================

* Make sure the ocaml compiler "ocamlc" and the Make utility "make"
  are in your path.

* Change to the subdirectory "src".

* Edit Makefile to select the name of the executable (rz or rz.exe).

* Run "make".

* Optionally, to test whether RZ has compiled properly, run "make test".


4. Usage and Help
=================

Run

  rz --help

to see basic usage information.

The subdirectory "examples" contains examples of RZ input files. If
you run RZ on them, it will generate corresponding output file (with
extension .mli).

Unfortunately, there is no user manual for RZ at this time. If you
need help with getting RZ to work, please contact us at:
- Andrej Bauer <Andrej.Bauer@andrej.com>
- Chris Stone <stone@cs.hmc.edu>
