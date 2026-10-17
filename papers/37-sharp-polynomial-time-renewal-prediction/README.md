# Rate-Optimal Polynomial-Time Prediction of Stationary Renewal Processes

Source: [paper](https://liuchliuch.github.io/repository/sharp-polynomial-time-renewal-prediction/).

## Results

The entry module is `Paper37.lean`. The development connects stationary renewal word risk to concrete integer dynamic programs and finite binary-machine implementations.

| Source result | Lean declaration | Scope |
| --- | --- | --- |
| Theorem 2.2 | `Paper37.MainResults.fixed_time_minimax_rate` | Fixed-time minimax prediction rate, with the finite renewal-cycle input retained where required for the lower bound. |
| Theorem 2.2 / Theorem D.3 | `Paper37.CompleteResults.fixed_time_rate_attainment` | Exact predictor output, rate attainment and a finite TM2 polynomial-time implementation, conditional on the named cycle and simulation principles. |
| Theorem E.4 | `Paper37.CompleteResults.adaptive_rate_attainment` | Adaptive prediction and its risk bound; machine complexity uses the generic simulation principle. |
| Theorem G.1 | `Paper37.CompleteResults.anytime_rate_attainment` | Cumulative risk bounds and the actual anytime program with conditional finite-machine attainment. |
| Proposition H.1 | `Paper37.KnownSupportCycle.risk_bounds` | Known-bounded-support estimator transferred to the original word risk. |

The lower-bound argument retains both observed renewal boundaries and arbitrary private randomization. Program semantics, operation counts, reached-value bit bounds and concrete encodings are proved within the development.

## Build

Run from this directory:

```sh
python3 ../../scripts/verify.py --paper 37 --check static
python3 ../../scripts/verify.py --paper 37 --check build
python3 ../../scripts/verify.py --paper 37 --check comparator --suite main
python3 ../../scripts/verify.py --paper 37 --check comparator --suite negative-added-premise
python3 ../../scripts/verify.py --paper 37 --check comparator --suite negative-illegal-axiom
```

## Assumptions

Lean and Mathlib are pinned in the project files. `Paper37.EquilibriumCycle.EquilibriumCyclePrinciple` supplies finite lattice projections of the stationary size-biased renewal construction. The general infinite-support two-sided construction in Lemma F.2 is cited, not formalized here.

`Paper37.BoundedLoopMachine.BoundedLoopSimulationPrinciple` supplies a generic finite bounded-loop compiler into finite Mathlib TM2 machines with a uniform all-input time bound. It is a disclosed specialization of classical simulation, without a supplied Lean compiler proof. It does not assume predictor-specific output, risk or complexity bounds, and statistical statements do not require this simulation principle. See [external dependencies](EXTERNAL_DEPENDENCIES.md).

## Verification

The complete dependency-consistent build, official comparison, full production axiom audit and fresh kernel replay remain incomplete. The fixed theorem contracts need no regeneration. Negative controls test an added premise and an unauthorized axiom. The machine claims must be read conditionally on the generic simulation principle.

## References

- [Exact external interfaces and bibliography](EXTERNAL_INPUTS.md).
- Arratia–Goldstein–Kochman, [Size bias for one and all](https://doi.org/10.1214/13-PS221), section 3.
- Savage, [Models of Computation, chapter 8](https://cs.brown.edu/people/jsavage/book/pdfs/ModelsOfComputation_Chapter8.pdf).
