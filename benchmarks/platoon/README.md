# Platoon Benchmark

This benchmark evaluates **SPTG** on a leader-based automotive platooning use case, focusing on the symbolic generation of timed test cases for join and leave maneuvers. The experiments cover both **systematic coverage objectives** and **user-defined large scenarios**, and report generation metrics.

### References

Automotive platooning is identified as a representative and challenging use case
for the verification and validation of autonomous systems in the Autonomy Verification
& Validation Roadmap and Vision 2045 published by NASA:

👉 [https://ntrs.nasa.gov/citations/20230003734](https://ntrs.nasa.gov/citations/20230003734) *(Technical report)*.

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

The generated report can be found here (its content follows):

`/path/to/SPTG/benchmarks/platoon/pair_transition_coverage_platoon_3_before/report.txt`

```
Tescase                   ; Path length ; TC Transitions ; Max formula (B) ; Solver time (s) ; Max mem. (MB)
testcase_10.sew           ;          26 ;            320 ;           18619 ;            0.02 ;         18.60
testcase_11.sew           ;          26 ;            319 ;           11946 ;            0.02 ;         18.58
testcase_12.sew           ;          14 ;            177 ;           19087 ;            0.02 ;         18.64
testcase_13.sew           ;          14 ;            174 ;            7983 ;            0.01 ;         18.45
testcase_14.sew           ;           6 ;             75 ;            2734 ;            0.01 ;         18.35
testcase_15.sew           ;          12 ;            150 ;           10131 ;            0.02 ;         18.45
testcase_16.sew           ;          14 ;            174 ;           11093 ;            0.02 ;         18.44
testcase_17.sew           ;          14 ;            172 ;            5272 ;            0.01 ;         18.34
testcase_18.sew           ;          14 ;            174 ;           10893 ;            0.01 ;         18.43
testcase_19.sew           ;          14 ;            172 ;            5195 ;            0.01 ;         18.34
testcase_1.sew            ;           4 ;             52 ;            3301 ;            0.02 ;         18.21
testcase_20.sew           ;          13 ;            162 ;           16518 ;            0.02 ;         18.54
testcase_21.sew           ;          13 ;            159 ;            6168 ;            0.01 ;         18.43
testcase_22.sew           ;           5 ;             64 ;            4520 ;            0.02 ;         18.32
testcase_23.sew           ;           5 ;             62 ;            2086 ;            0.01 ;         18.22
testcase_24.sew           ;           2 ;             24 ;             625 ;            0.01 ;         18.09
testcase_25.sew           ;           2 ;             24 ;             561 ;            0.01 ;         18.09
testcase_2.sew            ;           4 ;             50 ;            1794 ;            0.01 ;         18.19
testcase_3.sew            ;           4 ;             52 ;            2714 ;            0.01 ;         18.20
testcase_4.sew            ;           4 ;             50 ;            1794 ;            0.01 ;         18.19
testcase_5.sew            ;          17 ;            213 ;           13718 ;            0.02 ;         18.57
testcase_6.sew            ;          17 ;            212 ;           12542 ;            0.02 ;         18.47
testcase_7.sew            ;          15 ;            187 ;            7983 ;            0.02 ;         18.45
testcase_8.sew            ;          25 ;            311 ;           29215 ;            0.03 ;         18.71
testcase_9.sew            ;          25 ;            308 ;           11034 ;            0.02 ;         18.49
```


- **After simplification**
```sh
cd /path/to/SPTG/benchmarks/platoon/pair_transition_coverage_platoon_3_after
./run-all.sh
```
The generated report can be found here (its content follows):

`/path/to/SPTG/benchmarks/platoon/pair_transition_coverage_platoon_3_after/report.txt`

```
Tescase                   ; Path length ; TC Transitions ; Max formula (B) ; Solver time (s) ; Max mem. (MB)
testcase_10.sew           ;          26 ;            304 ;            7875 ;            0.02 ;         20.19
testcase_11.sew           ;          26 ;            304 ;            7777 ;            0.02 ;         20.20
testcase_12.sew           ;          14 ;            164 ;            4709 ;            0.01 ;         19.97
testcase_13.sew           ;          14 ;            164 ;            4649 ;            0.01 ;         19.97
testcase_14.sew           ;           6 ;             71 ;            1660 ;            0.01 ;         19.74
testcase_15.sew           ;          12 ;            142 ;            3114 ;            0.02 ;         19.86
testcase_16.sew           ;          14 ;            165 ;            3459 ;            0.02 ;         19.85
testcase_17.sew           ;          14 ;            165 ;            3309 ;            0.02 ;         19.85
testcase_18.sew           ;          14 ;            165 ;            3439 ;            0.02 ;         19.85
testcase_19.sew           ;          14 ;            165 ;            3289 ;            0.02 ;         19.86
testcase_1.sew            ;           4 ;             46 ;             836 ;            0.01 ;         19.71
testcase_20.sew           ;          13 ;            152 ;            3934 ;            0.02 ;         19.95
testcase_21.sew           ;          13 ;            152 ;            3785 ;            0.02 ;         19.86
testcase_22.sew           ;           5 ;             58 ;            1429 ;            0.02 ;         19.74
testcase_23.sew           ;           5 ;             58 ;            1328 ;            0.01 ;         19.72
testcase_24.sew           ;           2 ;             23 ;             504 ;            0.01 ;         19.60
testcase_25.sew           ;           2 ;             23 ;             430 ;            0.01 ;         19.59
testcase_2.sew            ;           4 ;             46 ;             735 ;            0.01 ;         19.72
testcase_3.sew            ;           4 ;             46 ;             774 ;            0.01 ;         19.70
testcase_4.sew            ;           4 ;             46 ;             628 ;            0.01 ;         19.62
testcase_5.sew            ;          17 ;            200 ;            5554 ;            0.02 ;         20.08
testcase_6.sew            ;          17 ;            200 ;            5456 ;            0.02 ;         20.08
testcase_7.sew            ;          15 ;            177 ;            5052 ;            0.02 ;         19.98
testcase_8.sew            ;          25 ;            294 ;            7407 ;            0.02 ;         20.18
testcase_9.sew            ;          25 ;            294 ;            7193 ;            0.02 ;         20.18

```

### Large User-Defined Scenarios

These experiments evaluate scalability on longer and more complex test purposes involving larger platoons. Each test purpose has a length of 50 and encodes extended join/leave behaviors.

**Platoon size 3**

```sh
cd /path/to/SPTG/benchmarks/platoon/large_behavior_platoon_3
./run-all.sh
```

The generated report can be found here (its content follows):

`/path/to/SPTG/benchmarks/platoon/large_behavior_platoon_3/report.txt`

```
Tescase                   ; Path length ; TC Transitions ; Max formula (B) ; Solver time (s) ; Max mem. (MB)
testcase_3_50_after.sew   ;          50 ;            585 ;           14561 ;            0.02 ;         20.73
testcase_3_50_before.sew  ;          50 ;            621 ;           43255 ;            0.02 ;         20.65

```

**Platoon size 5**

```sh
cd /path/to/SPTG/benchmarks/platoon/large_behavior_platoon_5
./run-all.sh
```

The generated report can be found here (its content follows):

`/path/to/SPTG/benchmarks/platoon/large_behavior_platoon_5/report.txt`

```
Tescase                   ; Path length ; TC Transitions ; Max formula (B) ; Solver time (s) ; Max mem. (MB)
testcase_5_50_after.sew   ;          50 ;            589 ;           16096 ;            0.02 ;         20.74
testcase_5_50_before.sew  ;          50 ;            618 ;           65524 ;            0.02 ;         20.67


```


**Platoon size 10**

```sh
cd /path/to/SPTG/benchmarks/platoon/large_behavior_platoon_10
./run-all.sh
```

The generated report can be found here (its content follows):

`/path/to/SPTG/benchmarks/platoon/large_behavior_platoon_10/report.txt`

```
Tescase                   ; Path length ; TC Transitions ; Max formula (B) ; Solver time (s) ; Max mem. (MB)
testcase_10_50_after.sew  ;          50 ;            592 ;           18145 ;            0.02 ;         20.98
testcase_10_50_before.sew ;          50 ;            631 ;           94931 ;            0.03 ;         20.93


```

