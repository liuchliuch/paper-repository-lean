# External results and the original conditional premise

The project uses ordinary explicit theorem/algorithm/object parameters. No custom production axiom or production `sorry` supplies their witnesses. [external-inputs.json](external-inputs.json) retains the exact English ledger, ten grouped standard inputs/background comparisons, and the paper-owned conclusions that are not externalized. The corresponding external theories and algorithms are not constructed as closed Lean proofs here.

The exact-real query model counts actual repeated oracle invocations. Exact prox evaluation and internal exact-real arithmetic are uncharged, as in the source model. Composite and Hilbert engines supply their own standard objective/dual-metric guarantees and true stage query counts, never the final continuation, gradient/minimax theorem, transport, path or full query budget. Constants are required before dimension/scales.

## Original Assumption 6.1

`P31.LowerBound.SimultaneousHardFamily` is the **original conditional hard-family assumption**, not a proved external theorem. Corollary 1.3 remains conditional on it. The interface supplies simultaneous normalized objective hard instances with the source constants and dimension conditions for each actual query protocol; it supplies no gradient lower-bound conclusion. Separate literature constructions are not claimed to establish this simultaneous premise. Localization, genuine oracle rescaling, the appended output query and conditional minimax combination are local deductions.

## scalar-clarkson

[3] Clarkson, Uniformly convex spaces (1936), doi:10.1090/S0002-9947-1936-1501880-4; scalar weighted consequence (2.9)

Interfaces: `P31.ScalarWeightedClarkson`.

External scope: Exact real-p scalar weighted Clarkson inequality for p>=2.

Own derivation: Coordinate summation, normalization a_p=2^(p-2), Frechet derivative, dual norm, radial geometry, all continuation steps.

## complementary-composite

[6] Diakonikolas--Guzman, Mathematical Programming 208 (2024), Theorem 2; arXiv:2101.11041v2 Theorem 2.1, nonlogarithmic branch.

Interfaces: `P31.ExternalComplementaryComposite`, `P31.ExternalCompositeFamily`, `P31.Schatten.ExternalMatrixComposite`, `P31.Schatten.ExternalMatrixCompositeFamily`.

External scope: Objective-error and integer query bound only, with q_src=p, lambda=mu, psi=H, phi=normalized shifted atom, eta=mu*delta^p/p. Source constants and fixed normalization absorbed in C(p,kappa). Constructor takes only known H, center, scales, exact prox; no f, gradient or minimizer. One common C before all dimensions.

Own derivation: Raw source power substitution; ceil cost; objective-gap-to-distance contraction; constructed minima and prox; adaptive history/warm-start induction; transport, path, stationarity, calibration, actual cumulative executed queries and all zero/easy branches.

Primary source: [reference](https://arxiv.org/html/2101.11041v2).

## raw-spectral-theory

Finite real rectangular compact SVD; standard Schatten norm, trace Holder and differential facts; Clarkson--McCarthy midpoint [2] Ball--Carlen--Lieb (1994), doi:10.1007/BF01231769.

Interfaces: `P31.Schatten.SpectralInput`.

External scope: Genuine compact SVD pins the sorted nonnegative singular list and raw powerGradient to actual matrices; raw norm laws/continuity/topological comparison, midpoint inequality, raw supporting derivative and raw dual norm identity.

Own derivation: Trace pairing equality; Bregman lower bound (5.5); normalized atom a_p^S=2^(2p-3), Jensen modulus/radial/gradient bounds; generic compact/coercive matrix prox and objective minima; Hilbert p=2 formula; actual continuation.

## diagonal-spectral-facts

Standard Schatten theory: rectangular diagonal norm equals finite lp norm and diagonal extraction is contractive.

Interfaces: `P31.DiagonalLowerBound.DiagonalNormInput`.

External scope: Only the exact diagonal norm identity and extraction contractivity, on the supplied genuine SVD Schatten realization.

Own derivation: Literal embedding/extraction continuous linear maps, trace adjoint, derivative, Holder/radius transfer, exact one-query adaptive simulation, conditional lower transfer and sharp flat diagonal witness.

## gaussian-facts

Standard finite-dimensional Gaussian covariance, Gaussian absolute moments, integrability and probability Jensen.

Interfaces: `P31.QuadraticMetric.GaussianInput`.

External scope: Actual probability measures and Bochner integrals; covariance trace identity; coordinate p-moment identity; Jensen moment comparison; positivity of actual standard Gaussian moment.

Own derivation: Gaussian trace bound <= gamma_p L_A, its combination with SDP, positive diagonal perturbation and final norm bound.

## sdp-duality-attainment

Standard finite-dimensional conic/semidefinite strong duality and attainment for the strictly feasible diagonal-majorant problem (7.12).

Interfaces: `P31.QuadraticMetric.SDPInput`.

External scope: Unspecified attained optimum of actual Diag(w)-A PSD problem, and dual-support principle on actual PSD X and lp_(p/2)(diag X). No numerical optimum/majorant bound.

Own derivation: Numerical trace majorant, existence with norm <=gamma_p L_A; addition of gamma_p L_A*d^(-1/s_p) I; positivity and norm <=2 gamma_p L_A.

## finite-norm-facts

Standard finite-dimensional operator supremum boundedness/homogeneity and finite lp/lq norm duality.

Interfaces: `P31.QuadraticMetric.OperatorNormInput`, `P31.QuadraticMetric.LpDualityInput`.

External scope: Facts about actual sSup operatorNorm and universal bounded pairings; no PSD quadratic-sup equality or diagonal-majorant conclusion.

Own derivation: PSD Cauchy-Schwarz from quadratic discriminant, actual operatorNorm=quadraticSup, D-smoothness, primal/dual Hilbert conversions, zero operator case.

## hilbert-small-gradient

[14] Kim--Park--Ozdaglar--Diakonikolas--Ryu, arXiv:2311.17296v2, Section 4.1 Corollary 3, p_src=2, with Section 3.4 Corollary 2. Uniform numeric-constant N-query normalization of the source 2N statement.

Interfaces: `P31.HilbertDiagnostics.EuclideanRateInput`, `P31.QuadraticMetric.HilbertRateInput`, `P31.QuadraticMetric.HilbertUniformRateInput`, `P31.QuadraticMetric.HilbertQueryInput`.

External scope: Only supplied Euclidean/Hilbert dual gradient norm <= C_H*radius/N^2 and true executed query count. Constructor receives only known metric/scales/initial/N. Fixed same numeric C_H before dimension.

Own derivation: Finite support smoothness/radius/target conversions, d^(1-2/p), actual main-accuracy cost inversion, query-program choice and (7.9) envelope; own diagonal construction/smoothness/conversions yield (7.11).

Primary source: [reference](https://arxiv.org/html/2311.17296v2).

## historical-objective-benchmark

[4] dAspremont--Guzman--Jaggi, Optimal affine-invariant smooth minimization algorithms, SIAM J Optim 28 (2018), doi:10.1137/17M1116842; standard smooth steepest-descent decrease.

Interfaces: `Explicit hobjective and hdescent arguments of P31.objective_plus_descent_rate`.

External scope: External objective budget f(x0)-fstar <= C L R^2/N^(1+2/p), and standard per-step decrease ||grad||_q^2 <=2L(f_j-f_(j+1)). These algorithms are not reconstructed.

Own derivation: Exact telescoping/best-iterate conversion to sqrt(2C) L R/N^((p+1)/p), inverse exponent p/(p+1) and continuation gain N^(-1/p).

## historical-one-shot-and-hasd

[6] Theorem 3 unsimplified one-shot branch; [1] Bai--Bullins, Faster acceleration for steepest descent, COLT 2025 Corollary 9.

Interfaces: `No production axiom or full-rate premise introduced; exact own comparisons in AdditionalClaims and Schedule.`.

External scope: Only cited historical rate/algorithm claims. No claim these external algorithms have been formalized. HASD requires a uniform prefix parameter and Euclidean radius.

Own derivation: Exact gamma-beta identity/equality corner; every actual nonzero-gradient prefix has G_t>=1, coordinate-supported witnesses have exactly G_t=1 in arbitrary dimension, sharp Euclidean radius conversion. No dimension-growing prefix benefit inferred.

## Mathematical representation

Matrix endpoints use actual real rectangular matrices, genuine compact-SVD-pinned singular values and the trace gradient. Raw standard spectral facts remain explicit. Normalized growth, matrix minima/prox constructions, continuation and query counting are own proofs. Gaussian covariance/moment and actual SDP attainment/duality interfaces supply only standard facts; the trace majorant, positive diagonal perturbation, final metric conversion and zero-operator zero-query output are local. Historical one-shot/HASD and objective benchmarks are explicitly cited comparisons, without claims to reconstruct those algorithms.
