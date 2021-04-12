# Modular Data-Race-Freedom Guarantees in the Promising Semantics

Simple litmus tests used for performance evaluation

## Requirements

- Armv8 machine
- clang 10.0.0
- clang++ 10.0.0
- Python3 >= 3.6.9

## Run experiments

When you run the script below, each experiment is run 360 times.
You can change the number of runs by modifying *L24* in `run.sh` (`for i in {1..360}` => `for i in {1..[N]}`).

```bash
all.sh
```

Then, the directory `results/` will be generated.

## Analyze results of experiments

Run the script below. 
```bash
./parse_litmus.sh [dir] [runs] [todiscard] # e.g., ./parse_litmus.sh ../results 360 30

```
Then, `[dir]/out/[n]_stat.csv` will be generated. (where *n* is 9, 10, 11, and 12)

`runs` is the number of runs, and the `todiscard` fastest results and the lowest results will be discarded.

For each *n*, `[dir]/out/[n]_stat.csv` contains the results for:
- out/9_stat.csv - FADD test
- out/10_stat.csv - FADD-RW test
- out/11_stat.csv - XCHG test
- out/12_stat.csv - XCHG-RW test

## Raw data

The directory `rawdata/` contains the raw data we used in the paper.
