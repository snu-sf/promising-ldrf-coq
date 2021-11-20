# Sequential Reasoning forUnder Weak MemoryOptimizing Compilers Concurrency (supplemental material)

## Build
- Requirement: opam (>=2.0.0), Coq 8.13.2 
- Install dependencies with opam
```
./configure
```
- Build the project
```
make build -j
```

## Code Structure
### The PS model with non-atomics (Section 4)
- `src/lang/` - Semantics of PS
- `src/opt/` - Compiler transformations on atomics
It is based on the Coq development of PS2.1 (https://github.com/snu-sf/promising-ldrf-coq)

### The SEQ model (Section 2 & 3)
- `src/sequential/Simple.v` - Semantics of SEQ and simulation relation
- `src/sequential/SequentialBehavior.v` - Advanced behavior refinement 

### Optimizer and Soundness Proof (Section ?)
- `src/itree/ITreeLang.v` - A language for optimization
- `src/itree/WRforwarding.v` and `src/itree/WRforwardingProof2.v` - Store-to-Load Forwarding and its soundness
- `src/itree/RRforwarding.v` and `src/itree/RRforwardingProof2.v` - Load-to-Load Forwarding and its soundness
- `src/itree/DeadStoreElim.v` and `src/itree/DeadStoreElimProof3.v` - Write-after-Write Elimination and its soundness
- `src/itree/LoadIntro.v` - Loop Invariant Code Motion and it soundness

### Adequacy (Section ?)
- `src/sequential/SequentialAdequacy.v` - Adequacy of SEQ
- `src/sequential/SeqCompatibility.v` - Compatibility Lemmas of simulation 
