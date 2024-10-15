#!/bin/bash

# Set up OPAM and Coq environment
opam switch create . 4.10.0
eval $(opam env)
opam pin add coq 8.13.2 -y
opam repo add coq-released https://coq.inria.fr/opam/released
eval $(opam config env)

# Install dependencies
opam pin add coq-paco 4.1.1 -y
opam pin add menhir 20230608 -y
opam pin add coq-itree 3.2.0 -y
opam pin add coq-iris 3.4.0 -y
opam pin add coq-ordinal 0.5.0 -y

# Build CompCert
cd CompCert-intptr
chmod 755 ./configure
./configure x86_64-linux -clightgen
make -j 2 -k

# Build CCR
cd ../CCR
make -j 2 -k
