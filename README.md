# Sequential Reasoning for Optimizing Compilers Under Weak Memory Concurrency

## Build
- Requirement: opam (>=2.0.0), Coq 8.15.0
- Install dependencies with opam
```
./configure
```
- Build the project
```
make build -j
```

## Code Structure
### The SEQ model (Section 2 & 3)
- `src/sequential/Sequential.v` - Semantics of SEQ (`Module SeqThread`) and simulation relation (`sim_seq_all`)
- `src/sequential/SequentialBehavior.v` - Behavior (`Module SeqBehavior`) and Advanced behavior refinement (`refine`)

### The PS model with non-atomics (Section 5) and updates of existing proofs
- `src/lang/` - Semantics of PS + non-atomics
- `src/transformation/` - Compiler transformations on atomics (*not contributions of this paper*)
- `src/promotion/` - Register Promotion (*not contributions of this paper*)
- `src/ldrfpf/LocalDRFPF.v`, `src/ldrfpf/LocalDRFRA.v`, and `src/ldrfsc/LocalDRFSC.v` - Local DRF theorems (PF, RA, and SC) (*not contributions of this paper*)

These are based on the Coq development of PS2.1 (https://github.com/snu-sf/promising-ldrf-coq)
Compiler transforamtions on atomics and Register Promotion, and Local DRF theorems are not contributions of this paper.

### Adequacy of reasoning in SEQ (Section 6)
- `src/sequential/SequentialAdequacy.v` - Adequacy (`Theorem sequential_adequacy_concurrent_context`)
- `src/itree/SequentialCompatibility.v` - Compatibility Lemmas of simulation (`Lemma itree_sim_seq_context`)

### Optimizer and Soundness Proof (Section 4)
- `src/itree/ITreeLang.v` - A language for optimization (`Section Stmt`)
- `src/optimizer/WRforwarding.v` and `src/itree/WRforwardingProof2.v` - Store-to-Load Forwarding (`WRfwd_opt_alg`) and its simulation proof (`Theorem WWfwd_sim`)
- `src/optimizer/RRforwarding.v` and `src/itree/RRforwardingProof2.v` - Load-to-Load Forwarding (`RRfwd_opt_alg`) and its simulation proof (`Theorem RRfwd_sim`)
- `src/optimizer/LoadIntro.v` - Loop Invariant Code Motion (`licm`) and its simulation proof (`Theorem LICM_LoadIntro_sim`)
- `src/optimizer/DeadStoreElim.v` and `src/itree/DeadStoreElimProof3.v` - Write-after-Write Elimination (`DSE_opt_alg`) and its simulation proof (`Theorem DSE_sim`)
- `src/sequential/OptimizerAdequacy.v` - Final soundness theorems for optimization passes (`Theorem WRforwarding_sound`, `Theorem RRforwarding_sound`, `Theorem LICM_LoadIntro_sound`, and `Theorem DeadStoreElim_sound`)
