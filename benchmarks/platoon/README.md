# Platoon Benchmark

This benchmark evaluates **SPTG** on a leader-based automotive platooning use case, focusing on the symbolic generation of timed test cases for join and leave maneuvers. The experiments cover both **systematic coverage objectives** and **user-defined large scenarios**, and report generation metrics.

### References

Automotive platooning is identified as a representative and challenging use case
for the verification and validation of autonomous systems in the Autonomy Verification
& Validation Roadmap and Vision 2045 published by NASA:

👉 [https://ntrs.nasa.gov/citations/20230003734](https://doi.org/10.1016/j.scico.2025.103285) *(Technical report)*.

The roadmap explicitly cites the work of Kamali et al.:


👉 [https://doi.org/10.1016/j.scico.2017.05.006](https://doi.org/10.1016/j.scico.2017.05.006) *(Open Access)*.


As a reference, this work supports the formal analysis of platoon coordination
protocols and highlights platooning scenarios as a relevant benchmark for
assessing the expressiveness and scalability of V&V techniques.

## Structure of the Experiments

The benchmark is organized into several experiment folders, each corresponding to a specific test purpose family and platoon size.

### Transition-Pair Coverage (Maximum Platoon Size = 3)

These experiments generate test purposes derived from **transition-pair coverage**, which is sufficient to exercise all consecutive transition pairs in the leader model for platoons of size up to 3.

- **Before simplification**
```sh
cd /path/to/SPTG/benchmarks/platoon/pair_transition_coverage_platoon_3_before
  ./run-all.sh
```

- **After simplification**
```sh
cd /path/to/SPTG/benchmarks/platoon/pair_transition_coverage_platoon_3_after
./run-all.sh
```

The comparison highlights the impact of symbolic simplification on the size of generated test cases and generation time.


### Large User-Defined Scenarios

These experiments evaluate scalability on longer and more complex test purposes involving larger platoons. Each test purpose has a length of 50 and encodes extended join/leave behaviors.

**Platoon size 3**

```sh
cd /path/to/SPTG/benchmarks/platoon/large_behavior_platoon_3
./run-all.sh
```
**Platoon size 5**

```sh
cd /path/to/SPTG/benchmarks/platoon/large_behavior_platoon_5
./run-all.sh
```

**Platoon size 10**

```sh
cd /path/to/SPTG/benchmarks/platoon/large_behavior_platoon_10
./run-all.sh
```

These scenarios stress symbolic execution and SMT solving due to the increased number of admissible join and leave positions.

