# Dependencies and mathematical model

No additional unformalized external mathematical theorem, registered external `sorry`, or new axiom is used by the production entry. The proofs use the pinned Lean kernel and existing mathlib results in finite combinatorics, real analysis, measure theory and probability. The full transitive package pins are retained in `lake-manifest.json`. A static source review found no production `sorry`, `admit` or axiom; this is not a fresh transitive kernel audit.

The exact source-model boundaries are as follows:

- Behavioral forecasters are Borel probability kernels on actual public histories. The simultaneous adversary sees only the strict past; it does not see the current private forecast. Strategies are encoded for all natural-number rounds, while each finite-horizon law reads only its first T transitions. This permits every finite-horizon strategy, extended arbitrarily after T, and strategies may know T.
- Calibration distance is the genuine infimum over perfectly calibrated comparators. The upper value is independently defined over the original positive-integer grid domain; its optimizer is proved rather than built into the desired rate.
- The exact implementation uses cached complete binary trees implementing the same grid forecasts. Its word-RAM model counts constant-size record operations and arithmetic on fitting words, continuation scheduling and root-handle activation. The formal guarantees concern record visits, widths, suspended initialization deadlines and arena footprints; Lean compiler, evaluator, garbage-collector and wall-clock runtime are outside that cost model. No balanced-tree complexity theorem is assumed.
- The randomized-oblivious square-root lower bound remains an open source question. The actual fixed-string value and quantifier-order obstruction are formalized, without resolving the open bound.

Related-work citations are background rather than proof premises. `Verification/source-result-map.json` retains the model and result-level correspondence.
