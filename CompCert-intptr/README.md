# CompCert
The formally-verified C compiler.

## Overview
The CompCert C verified compiler is a compiler for a large subset of the
C programming language that generates code for the PowerPC, ARM, x86 and
RISC-V processors.

The distinguishing feature of CompCert is that it has been formally
verified using the Coq proof assistant: the generated assembly code is
formally guaranteed to behave as prescribed by the semantics of the
source C code.

For more information on CompCert (supported platforms, supported C
features, installation instructions, using the compiler, etc), please
refer to the [Web site](https://compcert.org/) and especially
the [user's manual](https://compcert.org/man/).

## CompCertSSA version

This development is a version of CompCert extended with an SSA
middle-end:

- construction of the SSA form, from RTL
- SSA-based optimizations
- SSA-related librairies on dominance and dominators
- SSA destruction with coalescing, on the Conventional SSA form

The following people contibuted to this extension (alphabetic order):
Sandrine Blazy, Delphine Demange, Yon Fernandez de Retana, David
Pichardie, Léo Stefanesco.

## License
CompCert is not free software.  This non-commercial release can only
be used for evaluation, research, educational and personal purposes.
A commercial version of CompCert, without this restriction and with
professional support and extra features, can be purchased from
[AbsInt](https://www.absint.com).  See the file `LICENSE` for more
information.

## Copyright
The CompCert verified compiler is Copyright Institut National de
Recherche en Informatique et en Automatique (INRIA) and 
AbsInt Angewandte Informatik GmbH.

The additions related to the SSA middle-end are Copyright Univ Rennes,
Inria, IRISA.

## Contact
General discussions on CompCert take place on the
[compcert-users@inria.fr](https://sympa.inria.fr/sympa/info/compcert-users)
mailing list.

For inquiries on the commercial version of CompCert, please contact
info@absint.com

For inquiries on the SSA-specific additions, please contact Delphine
Demange.
