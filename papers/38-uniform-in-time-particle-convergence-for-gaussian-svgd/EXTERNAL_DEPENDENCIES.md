# External dependencies

Lean is pinned by `lean-toolchain` to `leanprover/lean4:v4.24.0`. Mathlib is pinned to `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` in the Lake configuration and `lake-manifest.json`; all transitive packages retain exact commit revisions in the manifest. Preserve these pins and use the repository shared tooling.

The complete quantified interface/reference/use-site record is [EXTERNAL_INPUTS.md](EXTERNAL_INPUTS.md). These inputs are explicit proposition or structure arguments; definitions of their interfaces do not constitute proofs of inhabitants. No production axiom or registered external `sorry` is used.

The 13 required named interfaces are:

| Area | Required interface | Boundary |
| --- | --- | --- |
| Raw empirical matching | `ExternalStatisticalInputs.Matching.expected_upper` | Expected raw Gaussian quadratic empirical transport upper rate, before whitening or flow. |
| Sharp raw matching | `ExternalStatisticalInputs.Matching.expected_lower` | Corresponding positive lower rate, with the constant fixed before every sample size. |
| Raw covariance | `ExternalStatisticalInputs.CovarianceMoments` | Raw full-rank/moment facts for divisor-N covariance. |
| Raw concentration | `ExternalStatisticalInputs.Concentration` | Measurable raw Gaussian events and mean/covariance bounds. |
| Initialized log moments | `ExternalStatisticalInputs.InitializedMoments` | Actual initialized affine cloud moments, including log-square endpoint control. |
| Maximal ODE | `GlobalODE.StandardMaximalODETheorem` | Generic local maximal branch and compact escape. |
| Matrix ODE | `LinearMatrixODE.StandardFundamentalMatrixTheorem` | Principal invertible solution for a continuous linear matrix coefficient. |
| Decaying matrix ODE | `LinearMatrixODE.StandardDecayingFundamentalMatrixTheorem` | Uniform exponential-tail corollary for the fundamental matrix. |
| Gaussian analysis | `ExternalGaussianAnalysis.GaussianSteinTheorem` | Gaussian integration by parts. |
| Matrix calculus | `ExternalMatrixAnalysis.PrincipalRootDifferentiation` | Principal positive matrix-root Fréchet derivative. |
| Flow dependence | `ExternalODEAnalysis.GlobalFlowContinuousDependence` | Fixed-time continuity for an already given global family. |
| Arbitrary iid sampling | `ExternalEmpiricalTransport.RawEmpiricalStrongLaws` | On one common a.e. event, raw empirical W2, mean and covariance convergence from only finite second moment. |
| Transport separation | `ExternalEmpiricalTransport.QuadraticTransportSeparation` | Actual zero quadratic-cost probability laws are equal. |

`Main.AnalyticBaselines` is `∀ d, ExternalAnalyticInputs.Baselines d`. `Main.StatisticalBaselines` is **`∀ d, 1 ≤ d → ExternalStatisticalInputs.Baselines d`**. No positive matching lower bound is requested at dimension zero. The statistical bundle packages matching, covariance/concentration and initialized moments. Corollary 2.7 instead adds arbitrary measurable-space raw strong laws and transport separation to the analytic family, without Gaussian matching or concentration inputs.

`ExternalStatisticalInputs.LogWishart` is a declared unused raw alternative, not a field of the production bundle. `ExternalWishartEndpoint.EndpointFacts` is explanatory context for Remark 7.4, not used to prove rate theorems; it separates divergent inverse first moments at minimal sample size from finite log-square moments. These two categories must not be counted as required rate assumptions.

Mobility, Gaussian-energy geometry, compactness, stability, deterministic oracle, whitening/localization, standardized-shape transport, uniform trajectory estimates, spectral floor and particle convergence are paper-owned arguments. Several classical interfaces are disclosed specializations/combined consequences, not claimed verbatim numbered source theorems. No external numerical certificate or compile-time data is needed. Deferred source fixture materialization only copies independently written source contract signatures and retains all explicit external arguments.

Official Comparator uses the repository shared pinned installation. Challenge modules intentionally contain proof placeholders to specify fixed expected theorem types. They and deliberate negative-control axioms are verification fixtures, outside the production build target. The production proof closure must be checked independently of those fixtures.
