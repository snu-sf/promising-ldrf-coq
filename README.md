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

### The PS 2.1 model extended with non-atomics (Section 5) and updated proofs
These are based on the Coq development of PS2.1 (https://github.com/snu-sf/promising-ldrf-coq)
- `src/lang/` - Semantics of PS 2.1 extended with non-atomic accesses
The following are updated proofs from existing formalization (i.e., they are not contribution of this paper.)
- `src/transformation/` - Soundness of compiler transformations on atomics
- `src/promotion/` - Soundness of register promotion
- `src/ldrfpf/LocalDRFPF.v`, `src/ldrfpf/LocalDRFRA.v`, and `src/ldrfsc/LocalDRFSC.v` - Local DRF theorems (PF, RA, and SC)

### Adequacy of reasoning in SEQ (Section 6)
- `src/sequential/SequentialAdequacy.v` - Adequacy of simulation in SEQ (Theorem 6.2 in the paper and `Theorem sequential_adequacy_concurrent_context` in the Coq development)
- `src/sequential/SequentialRefinement.v` - Equivalence of simulation and behavioral refinement in SEQ (`Theorem refinement_implies_simulation` and `Theorem simulation_implies_refinement`)
- `src/itree/SequentialCompatibility.v` - Compatibility lemmas of simulation (`Lemma itree_sim_seq_context`)

### Optimizer and Soundness Proof (Section 4)
- `src/itree/ITreeLang.v` - A simple programming language for optimization (`Section Stmt`)
- `src/optimizer/WRforwarding.v` and `src/itree/WRforwardingProof2.v` - Store-to-Load Forwarding (`WRfwd_opt_alg`) and its simulation proof under SEQ (`Theorem WRfwd_sim`)
- `src/optimizer/RRforwarding.v` and `src/itree/RRforwardingProof2.v` - Load-to-Load Forwarding (`RRfwd_opt_alg`) and its simulation proof under SEQ (`Theorem RRfwd_sim`)
- `src/optimizer/LoadIntro.v` - Loop Invariant Code Motion (`licm`) and its simulation proof under SEQ (`Theorem LICM_LoadIntro_sim`)
- `src/optimizer/DeadStoreElim.v` and `src/itree/DeadStoreElimProof3.v` - Write-after-Write Elimination (`DSE_opt_alg`) and its simulation proof under SEQ (`Theorem DSE_sim`)
- `src/sequential/OptimizerAdequacy.v` - Final soundness theorems for optimization passes (`Theorem WRforwarding_sound`, `Theorem RRforwarding_sound`, `Theorem LICM_LoadIntro_sound`, and `Theorem DeadStoreElim_sound`)


## Guides for Readers

### The PS model with non-atomics (Section 5)
Mapping between the new transition rules in the paper (Figure 4) and the definitions in Coq (`src/lang/Local.v`)
- (WRITE) with `o_w = na` - `Local.write_na_step`
- (RACY-WRITE) - `Local.racy_write_step`
- (RACY-READ) - `Local.racy_read_step`

### The SEQ model (Section 2)
Mapping between the transition rules in the paper (Figure 1) and the definitions in Coq (`src/sequential/Sequential.v`)
- <sigma, F, P, M> with an oracle `o` - `SeqThread.mk (SeqState.mk sigma (SeqMemory.mk M F)) P o`
- (NA-READ) and (RACY-NA-READ) - `SeqState.na_local_read_step`
- (NA-WRITE) and (RACY-NA-WRITE) - `SeqState.na_local_write_step`
- (ACQ-READ) - `SeqEvent.step_acquire`
- (REL-WRITE) - `SeqEvent.step_release`

How the Coq development is different from the paper presentation
- A racy non-atomic read can read *any* value rather than only the *undef* value. Since any value includes the undef value, two definitions are equivalent for well-formed programs.
- There is no codition `P' <= P` in (REL-WRITE) rule of SEQ. Instead, we use `meet P' P` for a new permission.
- Similarly, there is a no codition `P <= P'` and `dom(V) = P' \ P` in (ACQ-READ) rule of SEQ. Instead, we use `join P' P` for a new permission and ignore `V(x)` for `x` not in `P' \ P`.
- SEQ allows atomic operations on non-atomic locations. In that case, the permission and the value of that location is changed, following the rule `SeqEvent.step_update`.
- There are rules for fences and atomic updates. When executing an acquire-release fence or update, it takes a (REL-WRITE) step after an (ACQ-READ) step.

### Adequacy of reasoning in SEQ (Section 6)
As briefly mentioned in the pear, we show that simulation in SEQ implies behavioral refinement in PS (`Theorem sequential_adequacy_concurrent_context` in `src/sequential/SequentialAdequacy.v`) and that simulation in SEQ is equivalent to behavioral refinement in SEQ for deterministic programs (`Theorem refinement_implies_simulation` in `src/sequential/SequentialRefinement.v`). Theorem 6.2 in the paper is a corollary from these two theorems.  

Though PS model allows mixing of atomic and non-atomic accesses to the same location, our adequacy theorem requires the absence of such mixing.
Therefore, there are assumptions `nomix` in `Theorem sequential_adequacy_concurrent_context`.
