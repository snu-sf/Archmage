# Archmage and CompCertCast: End-to-End Verification Supporting Integer-Pointer Casting

This is the artifact for the paper "Archmage and CompCertCast: End-to-End
Verification Supporting Integer-Pointer Casting".

## List of Claims
We claim that the artifact provides a Coq development of the definitions and proofs
presented in the paper (with minor simplifications for presentation purposes)
and compiles without any issues.

## Download, installation, and sanity-testing
The artifact is presented as a VirtualBox image ("artifact.ova"), but we
are also submitting the latest source code ("Archmage.tar.gz") just in
case. If there is a need to update our artifact in the middle of the review
process, we will make the latest version available on [here](https://github.com/snu-sf/Archmage).

### Installing via VirtualBox image
1. Install [VirtualBox](https://www.virtualbox.org/) (version 7.1.2 is
tested).

Now, you can use the VirtualBox image that we submitted:

2. Import the downloaded `artifact.ova` file into Virtual Box.

3. Launch the VirtualBox Image, Log-in, open a terminal, and run `cd ~/Archmage`

4. ID/PW: artifact/artifact

Note: The submitted VirtualBox image has emacs and Proof General installed, 
      which can be used to explore the Coq development.

### Installing manually with raw source code
1. Install opam in your system with the version at least 2.1.5.
2. In Archmage artifact directory, install a local opam switch and install the dependencies:
    ```
    opam switch create . 4.10.0 &&
    eval $(opam env) &&
    opam pin add coq 8.13.2 -y &&
    opam repo add coq-released https://coq.inria.fr/opam/released &&
    opam config env &&
    opam pin add coq-paco 4.1.1 -y && opam pin add menhir 20230608 -y && opam pin add coq-itree 3.2.0 -y && opam pin add coq-iris 3.4.0 -y && opam pin add coq-ordinal 0.5.0 -y &&
    cd CompCert-intptr &&
    chmod 755 ./configure &&
    ./configure x86_64-linux -clightgen &&
    make -k &&
    cd ../CCR &&
    make -k
    ```

Now, you can either use the source code from the Github (make sure you
have internet connection):

3. Run `git clone git@github.com:snu-sf/Archmage.git && cd Archmage` and run the script above

or you can use the raw source code that we submitted:

4. Run `tar -zxvf Archmage.tar.gz && cd Archmage` and run the script above.

## CompCertCast Quick Start
1. Compiling CompCertCast follows the same optimization scenarios as for CompCert

   ./ccomp [option] [target]

   (ex) ./ccomp -dall many_cast1.c
2. Compile using an optimization scenario that includes Cast Propagation.

   ./ccomp -ssa on [option] [target]

   (ex) ./ccomp -ssa on -dall many_cast1.c
3. Help on CompCertCast

   ./ccomp --help

## Evaluation Instructions
To evaluate this artifact, we propose the following steps:
1. Check that the source code does not contain any `admit` or
   `Admitted.` (e.g., typing `grep -ri "admit" --include="*.v" .`  in
   the project root should print nothing).

    Note: 
    - You only need to check CCR and CompCert-intptr directories, as other directories (like _opam) may contain the keyword in their documentation.
    - For CompCert-intptr directory, you can also use the make target: `make check-admitted`

2. Read the Section "Mapping from the paper to the Coq development"
   and check that the Coq development indeed corresponds to the
   paper's presentation.
3. Compile the `many_cast1.c` file in the `CompCert-intptr/small-examples`   
   directory using two optimization scenarios: one with Cast Propagation   
   included and one without. Then compare the results to check the effect of 
   Cast Propagation. As shown in the CompCertCast Quick Start guide, it is 
   recommended to compile with the `-dall` flag to extract all compilation stages. 
   After compilation, compare the stack size of many_cast1.mach for each 
   scenario. (The stack size is printed above each mach function.)
4. Run the `test_compare.sh` script located in the `CompCert-intptr` directory. 
   Check that it generates the same assembly as the Original CompCert 
   when compiling existing CompCert benchmarks (which do not contain integer-
   pointer casts). 
   (`render.c` is an exception for reasons mentioned in the paper) Note: `ccomp_orig` is the binary of the original CompCert v3.9, and `test_orig` contains the exactly same benchmarks as `test`.

5. (VirtualBox Image Users Only) If you are using a pre-compiled Coq development, 
   confirm that the Coq development compiles without any problem.
   To do so, type `make clean` in both `CCR` and `CompCert-intptr` directories
   if you have previously built Coq development or are using the VirtualBox Image.
   Check that no `.vo` file remains (e.g., typing `find . -iname "*.vo"` in the project root should print nothing). Then, execute script behind in the root directory. 
   ```
   eval $(opam env) &&
   cd CompCert-intptr &&
   chmod 755 ./configure &&
   ./configure x86_64-linux -clightgen &&
   make -k &&
   cd ../CCR &&
   make -k
   ``` 
## Mapping from the paper to the Coq development

### Section 3. The Memory Model Archmage
Fig. 4
(in CompCert-intptr/common directory)
- M -->  `mem_contents`, `mem_access`, `mem_concrete` in Memory.v
- BlockID --> `block` in Values.v
- Val --> `val` in Values.v

Fig. 5
(in CompCert-intptr/common directory)
- alloc --> `alloc` in Memory.v and `extcall_malloc_sem` in Events.v
- free --> `free` in Memory.v and `extcall_free_sem` in Events.v
- ptoi --> `capture` in Memory.v and `extcall_capture_sem` in Events.v
- range --> `addr_is_in_block` in Memory.v means physical address in range
- valid_pa --> `valid_address_bounded`, `weak_valid_address_range`, `no_concrete_overlap` in Memory.v
- $toPtr_M$ --> `to_ptr` in Memory.v
- $toInt_M$ --> `to_int` in Memory.v
- v1 ⊼ v2 --> `val_join`(⊼ for value), `bool_optjoin` (⊼ for boolean) in IntPtrRel.v
- $⟦⊗⟧_M$(v1, v2) --> `cmplu_join_common` (⊗ is comparison), `psubl_join_common` (⊗ is psub) in IntPtrRel.v

Note: In the submitted paper, the semantics of `psub` in Fig. 5 is oversimplified. 
An updated version of the figure is available in `psub.pdf` in the `Archmage` directory.

Integers refines Pointers in Section 3.1
(in CompCert-intptr/x86 directory)
- Proof of Integers refines Pointers -> IntPtrRef.v `eval_operation_wrapper_binded` (Refinement lemma for all operations)

Theorem 3.1 `NB` case of ⊼ (in Fig. 5) is unreachable
(in CompCert-intptr/common directory)
- `psub_wrapper_no_angelic` in IntPtrRel.v 
- `psubl_wrapper_no_angelic` in IntPtrRel.v
- `cmpu_no_angelic'` in IntPtrRel.v (wrapper lemma of `cmpu_no_angelic`)
- `cmplu_no_angelic'` in IntPtrRel.v (wrapper lemma of `cmplu_no_angelic`)

### Section 4. CompCertCast: Reconciling CompCert with Archmage

Fig. 6
(in CompCert-intptr/common directory)
- `val_intptr` in IntPtrRel.v

Sec 4.1.1 Mixed Simulations and Memory Relations.
(in CompCert-intptr/common directory)
- Extended Mixed Simulation --> `xsim` in Simulation.v
- Memory Relation for "integers refine pointer" --> `concrete_extends` in IntPtrRel.v
- Definition of $Beh(TGT) ≤_{init_{TGT}} Beh(SRC) ∧ init_{SRC} ≤ init_{TGT}$ --> `observation_improves` in Behaviors.v

Sec 4.1.2 External Call Axioms.
(in CompCert-intptr/common directory)
- New External call axioms --> `extcall_properties_backward` in Events.v
- External call axioms for existing memory relations have been updated to work with backwards simulations. --> `ec_mem_extends_backward`, `ec_mem_extends_backward_progress`, `ec_mem_inject_backward`, `ec_mem_inject_backward_progress`, `ec_sound` in Events.v
- A new axiom stating that external calls may not ‘tamper’ with the memory map --> `ec_binds`, `ec_nonempty` in Events.v
- A new axiom to let new memory relations (`concrete_extends`) work with backwards simulations --> `ec_concrete_extends_backward`, `ec_concrete_extends_backward_progress` in Events.v
- Proof of some external call axioms are relaxed --> `forwrard_axiom_implies_backward_axiom_sim` in ExtCallAxiomRlx.v

Sec 4.2.1 Cast Propagation: Replacing Uses of Pointers with Integers.
(in CompCert-intptr/midend directory)
- Definition of Cast Propagation -> Captureprop.v
- Correctness Proof of Cast Propagation -> Capturepropproof.v
- Definition of Copy Propagation -> Copyprop.v
- Correctness Proof of Copy Propagation -> Copypropproof.v

Sec 4.2.2 Flagging Stack Casts to Enable Stack-Local Optimizations.
(in CompCert-intptr/backend directory)
- "Stack is Casted" Flag --> `am_concrete_stack` in ValueDomain.v

Sec 4.3 The Lower Bound Improvement: Generating CompCert-Asm with Fully Physical
Pointers
(in CompCert-intptr/x86 directory)
- Definition and Correctness Proof of Lowerbound -> Lowerbound.v

Fig. 10
(in CompCert-intptr/driver directory)
- Full Optimization scenarios in Fig. 10 --> `transf_clight_program_via_SSA` in Compiler.v
- Optimization scenarios excluding Cast Propagation --> `transf_clight_program` in Compiler.v
- Adequacy of CompCertCast --> `transf_clight_program_preservation_ssa_lbd` in Complements.v

Section 5. Archmage Logic

Clight+
(in CCR/clightplus directory)
- Semantics of Clight+ --> `compile` in compiler/ClightPlusgen.v
- Adequacy of Whole System --> `compile_behavior_improves_via_SSA_lbd` in compiler_proof/ClightPlus2LBProof.v

Fig. 11 
(in CCR/clightplus/mem/ClightPlusMem1.v)
- Block Data --> `metadata` 
- p1 $≈^m$ p --> `equiv_prov`
- $live_q^m$ (p) --> `is_alive`
- p $↦_q^m$ v --> `points_to`
- offset(m,p,ofs) --> `_has_offset`
- m1 # m2 --> `disjoint`
- vld(m,ofs) --> `valid`
- wvld(m,ofs) --> `weak_valid`

in selected rules for predicates and relations
- rule (1) --> `equiv_dup`
- rule (2) --> `equiv_slide`
- rule (3) --> `equiv_sym`
- rule (4) --> `equiv_trans`
- rule (5) --> `live_ownership`
- rule (6) --> `points_to_ownership`
- rule (7) --> collorary of `equiv_live_comm` and `equiv_dup` and `equiv_sym`
- rule (8) --> collorary of `equiv_point_comm` and `equiv_dup` and `equiv_sym`
- rule (9) --> `equiv_ii_eq`
- rule (10) --> collorary of `live_unique_meta` and `live_unique`

in rules for commands
- hoare triple of alloc(n) --> `malloc_spec`
- hoare triple of free(p) --> `mfree_spec`
- hoare triple of load(p) --> `load_spec`
- hoare triple of store(p, v) --> `store_spec`
- hoare triple of ptoi(p) --> `capture_hoare1`
- hoare triple of itop(i) --> function "itop" is just identity function so that the spec is not neccessary for reasoning
- hoare triple of p1 ⊗ p2 --> `cmp_ptr_hoare5` for comparison, `sub_ptr_spec` for psub
- hoare triple of p1 == p2 --> `cmp_ptr_hoare6`

Fig. 12 
(in CCR/clightplus_examples/xorlist/src directory)
- struct node --> xorlist.h
- delete_hd, delete_tl --> xorlist.c

Fig. 13 
(in CCR/clightplus_examples/xorlist/xorlist1.v)
- frag_q --> `frag_xorlist`
- xorlist --> `full_xorlist`
- hoare triple of add_hd(hdH, tlH, x) --> `add_hd_spec`
- hoare triple of add_tl(hdH, tlH, x) --> `add_tl_spec`
- hoare triple of delete_hd(hdH, tlH) --> `delete_hd_spec`
- hoare triple of delete_tl(hdH, tlH) --> `delete_tl_spec`

Fig. 14 verification of delete_hd
(in CCR/clightplus_examples/xorlist/xorlist01proof.v)
- `sim_delete_hd`

Theorem 5.1 (XorlistReverse)
(in CCR/clightplus_examples/xorlist/xorlist1.v)
- `rev_xorlist`

Fig. 15 (main)
(in CCR/clightplus_examples/xorlist directory)
- `main` source code in src/main.c
- hoare triple of `main` --> `main_spec` in main1.v
- verification --> `sim_main` in main01proof.v

## Guide for Readers

Currently, the artifact only supports x86-64 architecture. (We will clarify this in the paper.)
If you are using a computer with a different architecture, such as an Arm Mac, 
it is recommended to conduct the Artifact Evaluation using the submitted Virtual Box Image.

### Remark on Section 3
1. The major gap between the content of Fig 4. and the implementation is as follows:
   - Among the components of a Block's elements, 'live' and 'size' correspond to permissions of the block in the implementation. (see `mem_access`) 
     'size' is a special case where permissions are arranged consecutively.
   - Among the components of a Block's elements, 'c' is represented as a value, 
     but the implementation stores list of `memval` (in Memdata.v) which encodes the value in memory.
   - The fact that Pointer is a disjoint union of LogicalPtr and Int is not 
     explicitly specified in the Implementation, but it holds true in Archmage because Integer refines Pointer.
2. In the submitted paper, the semantics of `psub` in Fig. 5 is oversimplified. An updated version of the figure is available in `psub.pdf` in the `Archmage` directory.

### Remark on Section 5

The primary discrepancies between the paper and the implementation arise from two main factors in the paper:

1. Simplification of the alignment condition for memory access
2. Simplification of the fact that memory stores encoded values rather than raw values

Additionally, there are several other notable differences:

- Null pointers are considered to have a 'None' block id, so that `metadata` (Block Data in Fig. 11) has an 'option block' type.
- `tag` describes which space (Stack, Heap, Global) the accessibility or liveness refers to. (This prevents freeing of global variables.)
- The implementations of `delete_hd_spec` and `delete_tl_spec` cover not only the general cases outlined in the paper, but also include the specific case when the list is empty.
- In the paper, the hoare triple for pointer comparison has been simplified by omitting the corner case involving null pointers (e.g. cmp_ptr_hoare4).

## Documentation Updates

- Enhanced Item 1 of the Evaluation Instructions based on reviewer's suggestion: 
  introduced additional methods to verify the existence of Admitted Proofs and clearly specified the scope of directories to be checked.
- Modified Item 5 of the Evaluation Instructions to avoid confusion for users working with raw source code, as per reviewer's feedback.
- Improved the clarity of mappings between the paper and Coq formalization.
- Enhanced license and copyright information for both CCR and CompCert-intptr.
