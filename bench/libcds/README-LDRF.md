# Modular Data-Race-Freedom Guarantees in the Promising Semantics

The CDS C++ Library used for performance evaluation

## Requirements

- Armv8 machine
- clang 10.0.0
- clang++ 10.0.0
- Python3 >= 3.6.9

## Run experiments

When you run the script below, each experiment is run 360 times.
You can change the number of runs by modifying *L110* in `scripts/all.sh` (`for i in {1..360}` => `for i in {1..[N]}`).

```bash
scripts/all.sh .
```

Then, the directories `results_32/` `results_128/` will be generated.

## Analyze results of experiments

Run the script below in the directory `scripts/`. 
```bash
./parse.sh [dir] [runs] [todiscard] # e.g., ./parse.sh ../results_32 360 30

```
Then, `[dir]/stat.csv` will be generated.

`runs` is the number of runs, and the `todiscard` fastest results and the lowest results will be discarded.

## Raw data

The directory `rawdata/` contains the raw data we used in the paper.
