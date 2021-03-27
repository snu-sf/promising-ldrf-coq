# Modular Data-Race-Freedom Guarantees in the Promising Semantics

Minki Cho, Sung-Hwan Lee, Chung-Kil Hur, Ori Lahav

Proceedings of the 42nd ACM SIGPLAN Conference on Programming Language Design and Implementation ([PLDI 2021](https://conf.researchr.org/home/pldi-2021))

## Build
- Requirement: opam (>=2.0.0), Coq 8.9.1 
- Install dependencies with opam
```
./configure
```
- Build the project
```
make build -j
```

## The Model & Results Updated from PS 2.0
- `src/lang`: The Promising Semantics 2.1 model (*Figure 5*)

Our Coq development is based on the previous Coq formalization of PS 2.0.
See https://github.com/snu-sf/promising2-coq for a more detailed explanation about the model.  
The only change from PS 2.0 is the definition of capped memory (*Definition 3.1*): `cap` in `Module Mem` (`src/lang/Memory.v`)

- `src/opt` - Compiler transformations (updated from PS 2.0)
- `src/invariant` - An invariant-based program logic (updated from PS 2.0)
- `src/gopt` - Global optimization (updated from PS 2.0)

## Local DRF Theorems

### Local DRF-PF
- `src/ldrfpf/PFStep.v`
  + `L`-PF-machine (*Definition 4.1*): `machine_step` in `Module PFConfiguration`
  + `L`-PF race (*Definition 4.2*): `racy_execution` in `Module PFrace`
- `src/ldrfpf/LocalDRFPF.v`:
  + LDRF-PF theorem (*Theorem 4.3*): `Theorem local_drf_pf`
- `src/prop/Monotonicity.v`:
  + Promise Monotonicity lemma (*Lemma 4.6*): `Lemma promise_monotonicity`

### Local DRF-RA
- `src/ldrfra/OrdStep.v`
  + `L`-RA-machine (*Definition 4.7*): `machine_step` in `Module OrdConfiguration`
- `src/ldrfra/RARace.v`
  + `L`-RA-race (*Definition 4.8*): `race` in `Module RARace`
- `src/ldrfra/LocalDRFRA.v`:
  + LDRF-RA theorem (*Theorem 4.9*): `Theorem local_drf_ra`

### Local DRF-SC
- `src/ldrfsc/SCStep.v`
  + `L`-SC-machine (*Definition 4.10*): `machine_step` in `Module SCConfiguration`
  + `L`-RA-race (*Definition 4.11*): `race` in `Module SCRace`
- `src/ldrfsc/LocalDRFSC.v`:
  + LDRF-SC theorem (*Theorem 4.12*): `Theorem local_drf_sc`

> Note that the race conditions of LDRF-RA and LDRF-SC in Coq are slightly different from the race conditions in the paper:
Instead of defining race-detecting-machines,~
we define a racy machine state to be a state where a thread can take multiple steps ending with a racy step.
However, these conditions are provably equivalent to those in the paper.
