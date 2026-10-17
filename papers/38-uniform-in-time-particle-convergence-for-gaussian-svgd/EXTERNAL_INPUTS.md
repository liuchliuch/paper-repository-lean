# Explicit external inputs and their exact scope

This project proves the source Gaussian-SVGD conclusions **relative to the
ordinary external theorem arguments listed here**. These arguments are defined
as Lean propositions or structures, not declared as axioms. Their definitions
are not proofs of their inhabitants. References identify the known mathematical
results intended to supply them; they do not make those results kernel-checked
inside this project.

The inputs below contain raw sampling facts, classical Gaussian integration by
parts, principal-root differentiation, standard ODE facts, raw empirical strong
laws, and zero-cost transport separation. The original mobility identities,
energy geometry, compactness, stability, deterministic oracle, initialization
localization, standardized-shape estimates, weighted trajectory bounds, and
particle convergence conclusions are proved separately. In particular, a
specialized structure in this project must not be described as a verbatim
numbered theorem of its reference.

This document records declarations and read-only source call sites. It does not
perform or replace a whole-project build, a transitive axiom audit, kernel
replay, or Comparator validation.

## 1. Indexing, actual objects, and constant order

The final statistical input family is restricted to **positive dimensions**:

```lean
∀ d : ℕ, 1 ≤ d → ExternalStatisticalInputs.Baselines d
```

Consumers obtain its instance using `hV.dimension : 1 ≤ d`. The corresponding
all-dimension covariance/concentration arguments in `HighProbabilityMain` have
the same guard. A bundle for d=0 is not requested: its positive matching lower
bound would be incompatible with the singleton zero-dimensional sample space
and the definition `rate 0 N = 1`. This guard is necessary for realizable
external premises. `SourceSharpness.proposition23` likewise requests Matching
only for positive dimensions. The generic record definitions themselves retain
a natural-number parameter; their final applications enforce the guard.

The analytic family remains `∀ d : ℕ, ExternalAnalyticInputs.Baselines d`.
Those generic analysis facts also make sense in dimension zero. For arbitrary
law inputs in Corollary 2.7, the probability space and dimension are quantified
as displayed in Section 5.

Use the following notation throughout:

- `E d` is the actual Euclidean space `EuclideanSpace ℝ (Fin d)`.
- The raw sample is `ω : Fin N × Fin d → ℝ`, with its actual finite product
  standard Gaussian probability law `Sampling.law d N`.
- `ξᵢ = Sampling.cloud d N ω i`, `m_N = Sampling.mean d N ω`, and
  `S_N = Sampling.covariance d N ω` are actual finite sums, with covariance
  divisor N. Thus `N S_N` has N−1 Wishart degrees of freedom.
- `rawError` is actual `Transport.w2sq` between the raw empirical law and the
  actual standard Gaussian. `Transport.w2sq` is the extended nonnegative
  quadratic Kantorovich infimum over actual couplings.
- `defect = ‖I−S_N‖_F² + ‖m_N‖²`; `opNorm` is the Euclidean operator norm.
- The fixed good event is
  `G_N = {‖m_N‖ ≤ 1/4 ∧ ‖S_N−I‖op ≤ 1/4}`.
- The exact regularized source rate is

  \[
  r_d(N)=\begin{cases}
  N^{-1}\{1+\log\log(e^e+N)\},&d=1,\\
  N^{-1}(1+\log N)^2,&d=2,\\
  N^{-2/d},&d\ge3.
  \end{cases}
  \]

- The initialized cloud is exactly `μ + covarianceRoot S * ξᵢ`, with fixed
  `S.PosDef`. Mean, trace and log terms below are taken from this actual cloud.
- Expectations of nonnegative quantities are expressed as `lintegral`, with
  `ENNReal.ofReal` embedding a real bound. Restricted integrals are the
  indicator-weighted expectations in the source.

Unless stated otherwise, constants are chosen after the fixed dimension or
fixed initialization and **before every sample size N, tail parameter x,
confidence δ, trajectory and time**. Increasing an upper constant, decreasing a
positive lower constant, or decreasing the admissible positive tail-range
constant is part of the specialized external consequence where needed; it is
not an unidentified uniformity assumption.

## 2. Raw Gaussian statistical inputs

Declared in `Paper38/ExternalStatisticalInputs.lean`. None of its fields contains
an SVGD path, a whitened shape law, a source energy sublevel, or an all-time
particle error.

### 2.1 `Matching d`: upper and lower raw empirical matching

**Original references, frozen source numbering.** The references below are the
ones in `paper.txt` bibliography and source paragraphs `S6.p8` and `S2.p11`:

| Dimension | Upper reference | Lower reference |
| --- | --- | --- |
| d=1 | S. Bobkov and M. Ledoux, *One-dimensional empirical measures, order statistics, and Kantorovich transport distances*, Memoirs AMS **261**(1259), 2019, **Corollary 6.14**, Gaussian p=2 case. [Publisher DOI](https://doi.org/10.1090/memo/1259). | Same two-sided Gaussian order-statistic result, **Corollary 6.14**, p=2. |
| d=2 | M. Ledoux, *On optimal matching of Gaussian samples*, Journal of Mathematical Sciences **238**(4), 495–522, 2019, **Theorem 1**. [Publisher DOI](https://doi.org/10.1007/s10958-019-04253-6). | M. Talagrand, *Scaling and non-standard matching theorems*, Comptes Rendus Mathématique **356**(6), 692–695, 2018, **main result and display (1)**, followed by the independent-two-sample argument described below. [Publisher DOI](https://doi.org/10.1016/j.crma.2018.04.018). |
| d≥3 | M. Ledoux and J.-X. Zhu, *On optimal matching of Gaussian samples III*, Probability and Mathematical Statistics **41**(2), 237–265, 2021, **Theorem 1.1**, specialized to p=2. [Journal DOI](https://doi.org/10.37190/0208-4147.41.2.3). | Same **Theorem 1.1**, p=2 lower bound. |

**Classification:** Gaussian p=2 specializations, with nonasymptotic constant
adjustment to the exact regularized `rate` above. The Lean record, including all
N≥d+1, is a retained **consequence** of these references, not their quoted
literal statement. In d=2 the cited lower result is for two independent samples;
if ν′ is an independent empirical copy, the squared triangle inequality gives
`E W₂²(ν,ν′) ≤ 4 E W₂²(ν,γ_d)`. The fixed positive lower factor is adjusted
accordingly. The finitely many sample sizes outside an asymptotic formulation
are absorbed into constants, as the frozen source explicitly says.

**Original hypotheses in the application:** fixed d≥1, N independent standard
Gaussian observations in Euclidean space, and quadratic transport cost. These
are raw samples, before any centering, whitening or SVGD flow.

| Fields | Exact retained content and order | Actual use |
| --- | --- | --- |
| `upperConstant`, `upper_pos` | A real U>0 fixed for d before N. | Coefficient of the expectation bound below; used in standardized-shape constant construction. |
| `expected_upper` | For every N≥d+1, `E rawError ≤ ofReal(U * rate d N)`. | `StandardizedShape.expected_standardized_shape`; then source Lemma 6.2 and expected Theorem 2.2 / Corollary 2.5. |
| `lowerConstant`, `lower_pos` | A real l>0 fixed for d before N. | Gives strict positivity of the final fixed sharpness coefficient. |
| `expected_lower` | For every N≥d+1, `ofReal(l * rate d N) ≤ E rawError`. | `SourceSharpness.sharpness` and exact `proposition23`; neither an upper matching bound nor a trajectory estimate is used in that proof. |

### 2.2 `CovarianceMoments d`: raw rank and the exact second moment

**Reference:** the ordinary centered-normal/Wishart sampling theorem and its
second moments; in the frozen paper these are used in **(6.11), S6.p8**, with
`N S_N ~ Wishart_d(N−1,I)`. T. W. Anderson, *An Introduction to Multivariate
Statistical Analysis*, **third edition**, Wiley-Interscience, 2003, Chapter 7
provides the Wishart setting; **Lemma 7.2.1** is the specifically cited Bartlett
decomposition used for the determinant facts below. No assertion is made here
that Anderson Lemma 7.2.1 literally states this entire record or the displayed
Frobenius formula.

**Classification:** standard Gaussian/Wishart polynomial moment consequences.
For example `E S_N = (1−1/N)I`; entrywise Wishart covariances plus this bias give
the formula below. Full rank also has an independent local density/affine-span
proof in `GaussianFullRank` and `ModelBridges`; the statistical bundle still
explicitly requests its raw canonical-sample instance.

**Original hypotheses:** d≥1, N≥d+1, independent standard Gaussian samples,
centered covariance with divisor N. No inverse-Wishart moment hypothesis occurs.

| Field | Exact retained content | Actual use |
| --- | --- | --- |
| `full_rank` | For every N≥d+1, almost every raw sample has `S_N.PosDef`. | `StandardizedShape`, `HighProbabilityShape`, `ExpectedMain`, `SourceExpected`, and `SourceSamplingLemmas`; actual initialized covariance positivity is then proved by invertible congruence. |
| `integrable` | For every N≥d+1, the real raw function `‖I−S_N‖_F²` is integrable. | `StandardizedShape.expected_defect` and the additive expectation calculation in `expected_standardized_shape`. |
| `exact_secondMoment` | For every N≥d+1, `E ‖I−S_N‖_F² = ((N−1)d(d+1)+d)/N²`. | Same raw-defect calculation, then Lemma 6.2 and the actual initialized moment mismatch bound. |

The distinct mean identity `E ‖m_N‖²=d/N` is **proved locally** in
`GaussianStatistics.sampleMean_secondMoment`; it is not another retained field.

### 2.3 `Concentration d`: raw measurable Gaussian events

**References and classification:** the following are **standard derived raw
concentration consequences**, as explicitly outlined in frozen source
`S7.p3`, `S7.p7–S7.p8`, formulas **(7.2), (7.5), (7.6)**. A precise textbook
reference for the ingredients is Roman Vershynin, *High-Dimensional Probability:
An Introduction with Applications in Data Science*, **first edition**, Cambridge
University Press, 2018: **Lemma 2.7.7** (products of sub-Gaussians),
**Theorem 2.8.1** (scalar Bernstein), and **Theorems 5.2.1–5.2.2**
(Gaussian isoperimetry and Gaussian Lipschitz concentration), **§5.2.1**. The [author-hosted first-edition text](https://www.math.uci.edu/~rvershyn/papers/HDP-book/HDP-1.pdf)
identifies the edition and numbering. This is a supporting generic ingredient
reference, not a replacement for or alteration of the frozen matching
bibliography.

The raw W₂ functional on the N-tuple is N⁻¹ᐟ²-Lipschitz by coupling
corresponding atoms. Gaussian Lipschitz concentration and the raw matching upper
bound yield (7.5), after squaring and enlarging constants. Each centered product
`ξ_ij ξ_ik−δ_jk` is subexponential. Scalar Bernstein, a union over the fixed d²
entries, the Gaussian mean tail, and finite-dimensional norm comparisons give
(7.2) and (7.6). Reducing c0 enforces the operator threshold throughout
`1≤x≤c0N`. These reductions, including a measurable event with pointwise bounds,
are retained externally in the exact raw form below; the downstream SVGD event
and energy localization are proved inside the project.

**Original hypotheses:** fixed d≥1; independent standard Gaussian observations;
raw finite products and norms. No trajectory, target minimizer, potential V or
initial population covariance enters this structure.

| Fields | Exact retained content and quantifier order | Actual use |
| --- | --- | --- |
| `C`, `c`, `c0`; `C_pos`, `c_pos`, `c0_pos` | Three real strictly positive constants chosen for fixed d before every N and x. The same constants satisfy all record clauses, using finite maxima/minima when deriving a joint instance. | All event and tail coefficients below. |
| `good_measurable` | For **every** natural N, `G_N` is measurable. This clause is an elementary Borel-measurability consequence of finite raw sample moments and matrix norms. | Restricted integrals, good/bad split, and mismatch expectation in `GaussianMomentMismatch`, `ExpectedMain`, `LogEnergyLocalization`. |
| `good_tail` | For all N≥d+1, `P(G_Nᶜ) ≤ ofReal(C exp(−cN))`. | Source Lemma 7.1 tail and the Cauchy–Schwarz bad-event estimate in `LogEnergyLocalization`, giving source Lemma 7.2. |
| `raw_matching_event` | For all N≥d+1 and **all x≥1**, there exists a measurable H with `P(Hᶜ)≤ofReal(exp(−x))`, and every ω∈H satisfies `rawError≤ofReal(C(r_d(N)+x/N))`. H may depend on N,x. | `HighProbabilityShape.standardized_event`; then `HighProbabilityMain.localized_event` and Theorem 2.4. |
| `raw_covariance_event` | For all N≥d+1 and `1≤x≤c0N`, there exists measurable H with `P(Hᶜ)≤ofReal(C exp(−cx))`; on H, `defect≤C(1+x)/N` and `‖S_N−I‖op≤1/2`. | Same high-probability shape event; actual affine moment mismatch and the common compact energy box are derived internally. |

The raw event fields are stronger, more explicit formulations than merely
stating an upper-tail inequality. They are declared as specialized consequences;
there is no claim that the source article or generic textbook prints this Lean
structure verbatim. In particular they do not assert (7.7), (2.14), (2.15), or
a bound for any particle trajectory.

### 2.4 `LogWishart d`: declared raw alternative, not a production bundle field

**Reference and classification:** standard polynomial Gaussian moments and the
Bartlett/chi-square logarithmic **consequences** explained in frozen source
**(7.17)–(7.19), S7.p14**. Bartlett is Anderson [1], **Lemma 7.2.1**. For explicit
special-function ingredients, the NIST DLMF gives the digamma asymptotic in
[§5.11, equation (5.11.2)](https://dlmf.nist.gov/5.11.E2) and the trigamma
series in [§5.15, equation (5.15.1)](https://dlmf.nist.gov/5.15.E1).

| Fields | Exact retained content | Actual use |
| --- | --- | --- |
| `polynomialConstant`, `polynomialConstant_pos` | A positive real constant fixed for d before N. | Declared coefficient for the next field. |
| `polynomial_moment` | For every N≥d+1, `E(‖m_N‖⁴+(tr S_N)²)` is at most that constant. | Raw alternative only; not requested by the current production `Baselines` or `Main` entry points. |
| `logConstant`, `logConstant_pos` | A positive real constant fixed for d before N. | Declared coefficient for the next field. |
| `log_moment` | For every N≥d+1, `E[((−log det S_N)₊)²]` is at most that constant. | Raw alternative only; production uses the initialized-coordinate version below. |

It is important not to count both this record and `InitializedMoments` as two
independent required assumptions of the final rate theorems. The current
`ExternalStatisticalInputs.Baselines` contains `initialized`, not `LogWishart`.

### 2.5 `InitializedMoments d μ S hS`: the raw moments actually used

Here d≥1 and the population mean μ and covariance S≻0 are fixed **before** the
record and its constants. It concerns the actual initialized Gaussian cloud,
without a potential or any dynamics. Write

\[
a_N=\|\widehat\mu_N\|^2,\qquad
b_N=\operatorname{tr}\widehat\Sigma_N,\qquad
\ell_N=(-\log\det\widehat\Sigma_N)_+.
\]

**Original results and derivation:** the Gaussian sample mean has covariance
S/N. Gaussian polynomial moments and a trace bound by a fixed multiple of the
raw average `N⁻¹∑‖ξᵢ‖²` give uniform fourth-mean and squared-trace bounds.
Bartlett gives independent chi-square factors with degrees N−j. For
`Y_k~χ²_k`, differentiating its gamma Mellin transform gives

\[
E\log Y_k=\psi(k/2)+\log2,\qquad
\operatorname{Var}(\log Y_k)=\psi_1(k/2).
\]

The DLMF identities above, the finite small degrees including k=1, and
`det(Σhat)=det(S)det(S_N)` give the uniform initialized log-square bound. This
is a **standard derived consequence** of Anderson [1], Lemma 7.2.1 plus scalar
gamma identities, precisely the reduction in frozen source **(7.17)–(7.19)**.
The entire initialized record is not attributed to a single numbered theorem.

| Fields | Exact retained content and order | Actual use |
| --- | --- | --- |
| `meanConstant`, `meanConstant_nonneg` | A nonnegative constant Mμ depending on fixed d,μ,S, before N. | Coefficient of `mean_fourth`. |
| `traceConstant`, `traceConstant_nonneg` | A nonnegative constant Mtr with the same order. | Coefficient of `trace_second`. |
| `logConstant`, `logConstant_nonneg` | A nonnegative constant Mlog with the same order. | Coefficient of `log_second`. |
| `mean_measurable` | For every N, the actual raw function a_N is measurable. | `LogEnergyLocalization.initialEnvelope_secondMoment` and the measurable envelope in `weighted_bad_event_exponential`. |
| `trace_measurable` | For every N, b_N is measurable. | Same. |
| `log_measurable` | For every N, ℓ_N is measurable. The total real log convention defines it also on the singular null complement. | Same. |
| `mean_fourth` | For every N≥d+1, `E[a_N²] = E‖μhat_N‖⁴ ≤ ofReal(Mμ)`. | Same combined envelope calculation. |
| `trace_second` | For every N≥d+1, `E[b_N²]≤ofReal(Mtr)`. | Same. |
| `log_second` | For every N≥d+1, `E[ℓ_N²]≤ofReal(Mlog)`. | Same, and the weighted bad-event rate. |

The measurability clauses are elementary Borel consequences of raw finite
moments, determinant, and the totalized real log; they are retained explicitly
because the integral assembly needs them. They do not assert measurability of
a selected solution flow.

The project proves from these separate bounds

\[
E(1+a_N+b_N+\ell_N)^2\le
4(1+M_\mu+M_{\rm tr}+M_{\log}),
\]

in `LogEnergyLocalization.initialEnvelope_secondMoment`. Thus the combined
energy-envelope moment **(7.16)** is not an external field. The actual pathwise
energy envelope **(7.20)** and weighted trajectory bound **(7.11)** are also
proved separately.

### 2.6 `ExternalStatisticalInputs.Baselines d`: packaging only

For each d≥1 the final retained statistical record consists of:

- `matching : Matching d`;
- `covariance : CovarianceMoments d`;
- `concentration : Concentration d`;
- `initialized : ∀ μ S (hS : S.PosDef), InitializedMoments d μ S hS`.

The last field means constants may depend on d,μ,S, but precede N. There is no
potential V, trajectory, energy sublevel, standardized shape, or final source
estimate in this package. `Main.theorem22`, `Main.theorem24` and
`Main.corollary25` take this positive-dimension statistical family together with
the analytic family. `Main.proposition23` uses only its matching lower branch.
The complete source sampling statements are also exposed in
`SourceSamplingLemmas.lemma62`, `lemma71`, and `lemma72`.

## 3. Standard analytic inputs

Declared by `ExternalAnalyticInputs.Baselines d`, whose six fields are listed
below. It is a proposition-valued packaging record; it does not supply a
source minimizer, mobility identity, global source flow, stability constant or
particle convergence theorem.

### 3.1 `standardMaximalODE`: generic maximal branch and compact escape

**Reference:** Gerald Teschl, *Ordinary Differential Equations and Dynamical
Systems*, AMS Graduate Studies in Mathematics **140**, 2012,
**Theorem 2.13** and **Corollary 2.16**, §2.6, printed pp.51–53 in the
[author-hosted text](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf).
**Classification:** autonomous finite-dimensional specialization of local
existence/maximal continuation and the compact-escape alternative.

**Original hypotheses:** a locally Lipschitz vector field on an open domain of
a finite-dimensional real space; an interior initial point. The finite-lifetime
branch cannot remain in a compact subset of its domain.

**Exact retained quantifiers:** `GlobalODE.StandardMaximalODETheorem E` ranges
over every open Ω and locally Lipschitz `f : E → E`, and every x₀∈Ω. It returns
`Nonempty (ForwardMaximalSolution Ω f x₀)` with positive possibly infinite
forward lifetime, initial value x₀, domain membership and the actual ODE for
0≤t before the lifetime. If the lifetime is finite, every compact K⊆Ω has some
pre-lifetime point outside K. No bound uniform over f is requested.

The final bundle uses `E = HilbertCoordinates.Tangent d`, the actual finite
Euclidean–symmetric-matrix Hilbert space. `GlobalODE` proves energy trapping and
rules out finite lifetime using the own compact energy sublevels. Actual global
Gaussian moment existence is derived in `SourceMomentFlow.momentWellPosed`.
This input is used by `GaussianGradientFlow.exists_unique_global_flow`; it is
not a global-SVGD-existence premise.

### 3.2 `fundamental`: principal matrix solution for continuous C

**Reference:** Teschl, **§3.4, Theorems 3.9–3.10 and Lemma 3.11**, printed
pp.81–83 in the author-hosted text. **Classification:** standard fundamental
matrix construction and Wronskian invertibility, specialized to initial time
zero and continuous coefficients on the forward half-line.

**Exact retained input:** for every actual continuous `C : ℝ → Mat d` on
`[0,∞)`, `StandardFundamentalMatrixTheorem d` returns L with L(0)=I,
`HasDerivWithinAt L (C(t)*L(t)) (Ici 0) t` for all t≥0, and `IsUnit (L t)` for
all such t. Forward-half-line coefficients can be extended continuously left
of zero when using the book's open-interval formulation. This is a standard
restriction/extension consequence. It has no coefficient decay or limit claim.

**Use:** `SourceParticleFlow.particle_wellPosed_of_moment`,
`DeterministicMain.particleWellPosed` and the actual affine transport construction
inside `DeterministicMain.theorem21`; also `SourceFlowMeasurability` constructs
the selected global particle solution family. Actual affine particle/moment
identities and uniqueness are proved locally.

### 3.3 `decayingFundamental`: a uniform exponential-tail corollary

**Reference:** Teschl, **§3.7, Theorem 3.23**, printed pp.99–100, together with
§3.4 fundamental matrix theory and Gronwall. **Classification:** an explicitly
retained **standard corollary**, not the literal statement of Theorem 3.23.
The theorem provides the integrable-perturbation estimate; boundedness of L and
its inverse, integration of L′=CL, and limits of their products give the
specialized form used here.

**Exact order in `StandardDecayingFundamentalMatrixTheorem d`:**

1. Choose K≥0 and decay>0.
2. Choose M≥0 depending only on fixed d,K,decay, **before C**.
3. For every C continuous on `[0,∞)` with actual Frobenius-square envelope
   `frobSq(C t) ≤ K² exp(−2 decay t)` for all t≥0, obtain L and Linf.
4. L has L(0)=I, solves L′=CL in the forward within-derivative convention,
   every L(t) is invertible, Linf is invertible, L(t)→Linf, and
   `frobSq(L t−Linf) ≤ M² exp(−2 decay t)` for all t≥0.

The uniformity in step 2 matters: an M selected separately after each C would
not be the declared input. The standard proof bounds the coefficient's L¹
norm by K/decay, bounds both fundamental and inverse evolutions, and bounds the
remaining tail integral. Hence the required dependence is only d,K,decay.
This corollary contains no Gaussian field or particle-law conclusion.

**Use:** `ParticleLimitFromODE.uniform_limit_from_lipschitz_moment_decay`, then
`SourceParticleLimit.proposition26_at` and
`SourceNonGaussian.finite_limit_with_floor`. The project itself proves the
actual Gaussian coefficient's exponential envelope from compact-sublevel
regularity, vanishing coefficient at the minimizer and moment energy decay.

### 3.4 `stein`: the Gaussian integration-by-parts specialization

**Reference:** Charles M. Stein, *Estimation of the Mean of a Multivariate
Normal Distribution*, Annals of Statistics **9**(6), 1135–1151, 1981,
**Lemma 1, p.1136**. [Publisher DOI](https://doi.org/10.1214/aos/1176345632).
The source application is frozen P38 `S4.p4`.

**Original generic hypotheses:** Gaussian integration by parts for a weakly
or classically differentiable function with the needed integrable derivatives.
**Our specialization:** an actual C² admissible potential with globally bounded
Hessian. Its gradient has at most linear growth, ensuring the Gaussian
integrability needed for the Stein identity.

**Exact input `ExternalGaussianAnalysis.GaussianSteinTheorem d`:** for every
actual `AdmissiblePotential V α β`, μ,u∈E d, A≻0 and symmetric H,

\[
\int DV(\mu+Az)[u+Hz],d\gamma_d(z)
=\langle m(\mu,A^2),u\rangle+
  \operatorname{tr}(\Gamma(\mu,A^2)AH).
\]

This integral identity, including its conversion to the project's actual
Gaussian pushforwards, is retained as a **specialized consequence** of Stein's
lemma; the whole displayed Lean definition is not claimed to be Stein's printed
statement. There are no existential constants.

**Use:** `HilbertGradientFlow.intrinsic_first_variation`, `actual_gradient` and
the moment/gradient ODE coordinate chain; `SourceGeometry.covarianceEnergy_gradient`;
`CoefficientRegularity` and source path regularity. Differentiation under the
actual Gaussian potential integral is proved separately in
`GaussianDifferentiation`; the energy gradient, mobility positivity, source
moment stability and global convergence are not fields of this input.

### 3.5 `sqrt`: actual principal-root Fréchet differential

**Reference:** Nicholas J. Higham, *Functions of Matrices: Theory and
Computation*, SIAM, 2008, **Chapter 6 (Matrix Square Roots)**,
[chapter DOI](https://doi.org/10.1137/1.9780898717778.ch6).
**Classification:** the standard Fréchet differentiability/Sylvester-derivative
consequence for the principal square root on real symmetric positive definite
matrices. A particular numbered theorem beyond this chapter reference is not
claimed for the project's whole symmetric-Hilbert encoding. It can also be
obtained from the finite-dimensional inverse function theorem for squaring on
the SPD cone; the local inverse Sylvester operator is already proved in this
project.

**Original hypotheses:** positive definite real symmetric S; derivative
directions in Sym(d). If A=√S, the root differential sends H to the unique
symmetric X satisfying AX+XA=H.

**Exact input `PrincipalRootDifferentiation d`:** for every intrinsic q∈Domain d,
`HasFDerivAt principalRoot (HilbertMobility.inverseJ (principalRoot q)) q`.
Here `principalRoot` leaves the mean unchanged and applies the actual `CFC.sqrt`
to the matrix component. The mean derivative is identity; the matrix derivative
is the actual inverse Sylvester operator. Quantification is over the actual
symmetric tangent space; the SPD domain's intrinsic openness and the operator's
invertibility are proved locally. There are no constants.

**Use:** `HilbertGradientFlow.momentSolution_gradientPath`, source path
continuity and source moment uniqueness/stability; also
`NonGaussianInitialization.covarianceRoot_tendsto` and
`principal_whitening_tendsto`. The Frobenius root Lipschitz estimate **(7.4)**,
initialization mismatch and energy localization are own proofs; they are not
assumed by this differential input.

### 3.6 `continuousDependence`: fixed-time continuity of a given global family

**Reference:** Teschl, **Theorem 2.8**, §2.3, printed pp.43–44, continuous
dependence/Gronwall, followed by continuation along a finite solution segment.
**Classification:** standard fixed-time consequence for an already constructed
family, rather than an assumed source solution map.

**Exact input `ExternalODEAnalysis.GlobalFlowContinuousDependence E`:** E is
any finite-dimensional real normed space; for every open Ω and locally
Lipschitz autonomous f, and every family Φ with Φ(x,0)=x and, for every x∈Ω and
t≥0, Φ(x,t)∈Ω and the actual forward within derivative equal to f(Φ(x,t)),
the map x↦Φ(x,t) is continuous on Ω for each fixed t≥0. The bundle requests this
for **every N** with `E = Fin N → Model.E d`.

No numerical global Lipschitz constant, uniform bound over all times or energy
sublevels, or existence of Φ is supplied. The actual global family is
constructed locally before this input is applied. Its primary use is
`SourceFlowMeasurability.selectedFlow_pathSup_measurable` and
`gaussian_solution_family`, establishing the actual measurable random solution
family and all-time expectation in source Theorem 2.2. Countable rational-time
realization of the supremum is proved in `RandomSupremum`.

## 4. The endpoint explanatory boundary: `ExternalWishartEndpoint`

This is separate from both production baseline bundles.
`ExternalWishartEndpoint.EndpointFacts d` retains two known facts used to
explain **Remark 7.4**, not to prove a rate:

| Clause | Exact statement | Reference and classification | Actual use |
| --- | --- | --- | --- |
| Endpoint inverse trace | If 1≤d, then under the actual raw sample law with N=d+1, `∫⁻ ofReal (trace(S_N⁻¹)) = ∞`. | **Standard endpoint corollary** of Anderson [1], Lemma 7.2.1 (Bartlett), or the usual Wishart inverse-moment threshold: for W~Wishart_d(n,I), inverse first moments are finite only for n>d+1. At the actual endpoint n=N−1=d, a final Bartlett diagonal has χ²₁ law, whose reciprocal has infinite mean. The formula for a finite inverse expectation must not be extrapolated beyond its valid degrees. | Explanatory retained input only. Not a field of the rate-theorem statistical bundle. |
| Chi-square log square | `Integrable (fun x => (Real.log x)^2) chiSquareOneLaw`, with `chiSquareOneLaw = (gaussianReal 0 1).map (fun x => x²)`. | **Standard scalar gamma consequence**, the k=1 case of source (7.18). Near zero the density is a constant times x⁻¹ᐟ², for which log² is integrable; the exponential tail controls infinity. | Same explanatory boundary; unproved here as this named input. |

No positive inverse-covariance moment is postulated anywhere in the own
endpoint-valid rate proof. The logarithmic moment remains finite at the
minimal sample size even though the inverse first moment diverges. The
endpoint proposition does not assume or conclude an SVGD estimate and declares
no axiom.

## 5. Arbitrary-law empirical transport inputs for Corollary 2.7

Declared in `Paper38/ExternalEmpiricalTransport.lean`, outside the Gaussian
statistical bundle. They contain **raw** laws and moments only; no empirical
whitening, limiting particle cloud or spectral-floor conclusion is a field.

### 5.1 `RawEmpiricalStrongLaws Ω d`

**Original references:**

- V. S. Varadarajan, *On the convergence of sample probability distributions*,
  Sankhyā **19** (1958), 23–26: the article's almost-sure weak convergence
  result for empirical laws on a separable metric space. No numbered theorem
  is claimed for the entire combined input below.
- The ordinary integrable i.i.d. strong law; a precise supporting reference is
  Rick Durrett, *Probability: Theory and Examples*, **fifth edition**,
  **Theorem 2.4.1**. The [author-hosted text](https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf)
  states the integrable identically distributed strong law, even under the
  weaker assumption of pairwise independence.
- Cédric Villani, *Optimal Transport: Old and New*, Springer Grundlehren **338**,
  2009, **Theorem 6.9**: convergence in p-Wasserstein topology is weak
  convergence together with the p-th moment condition, here p=2.
  [Book DOI](https://doi.org/10.1007/978-3-540-71050-9).

**Classification:** the displayed three-limit conjunction is a **standard
combined consequence**, not a verbatim theorem of any one reference.

**Exact quantifier order:** after fixing an arbitrary measurable space Ω and d,
quantify over every probability P on Ω, every probability ν on E d, and every
sequence of measurable observations `X : ℕ → Ω → E d`. Assume joint i.i.d.
independence (`iIndepFun X P`), all marginals exactly `map (X n) P = ν`, and
only `Integrable (fun x => ‖x‖²) ν`. Then on **one common P-a.e. event**,
as n→∞:

1. actual `w2sq(empiricalLaw(X₀,…,X_n),ν)` tends to 0 in `ℝ≥0∞`;
2. the actual empirical mean of the first n+1 observations tends to
   `populationMean ν = ∫x dν`;
3. their actual centered covariance with divisor n+1 tends to the actual
   entrywise integral `populationCovariance ν`.

Counts n+1 exclude a spurious zero-particle empirical probability. The covariance
strong law follows by applying the ordinary integrable scalar strong law to
coordinates and coordinate products, then subtracting empirical mean products.
Finite second moment suffices because coordinate products are bounded in
absolute value by sums of squared coordinates; **no fourth moment** is assumed.
There are no rates, finite-N tail bounds, or uniform constants.

**Use:** `NonGaussianInitialization.ae_standardized_empirical_tendsto`, then
`SourceNonGaussian.corollary27_at` and `corollary27`. The external input does not
assume a density or positive definite covariance; those additional source
hypotheses are used separately by the own full-rank and principal-whitening
arguments. Simultaneous full rank of all admissible finite clouds on this same
probability space is proved in `NonGaussianWhitening.ae_iid_empiricalCovariance_posDef_succ_all`.
Principal-root/inverse-root continuity, empirical whitening replacement, actual
transport continuity and the final liminf/limsup spectral comparison are proved
inside the project, with only the root differential baseline additionally used
for root continuity.

The final Corollary 2.7 wrapper explicitly takes a family of these raw strong
laws over the chosen universe of measurable spaces Ω and dimensions d, in
addition to the analytic family. No Gaussian-specific concentration or matching
record is required for this arbitrary-law strong-law consequence.

### 5.2 `QuadraticTransportSeparation d`

**Reference:** Villani, *Optimal Transport: Old and New*, **Theorem 4.1**
(existence of an optimal coupling for a lower semicontinuous cost with suitable
integrable lower bounds), applied to the nonnegative continuous Euclidean
quadratic cost. **Classification:** the standard zero-cost separation
**corollary**, not the literal statement of Theorem 4.1.

**Exact retained input:** for every two probability laws μ,ν on E d,
`Transport.w2sq μ ν = 0 → μ = ν`. No finite second moment is required for this
implication: an optimal zero-cost plan is concentrated on the diagonal, so its
two marginals coincide. Nonnegativity supplies the lower-bound hypothesis.
The reverse implication is already proved locally by the diagonal coupling
(`Transport.w2sq_self` in `TransportGluing`). There are no constants, samples,
whitening maps or non-Gaussian premises in the input.

**Use:** `NonGaussianWhitening.population_whitened_cost_pos`, then source
Corollary 2.7. The project proves that equality of the whitened population law
to the standard Gaussian would restore the original law to its Gaussian affine
image. Separation only turns this proved inequality of actual measures into
strict positivity of the actual quadratic cost; it does not supply the
non-Gaussian obstruction or limiting spectral lower bound itself.

## 6. Results that are not external inputs

The following are derived from the original potential/initial-data hypotheses
and the explicitly listed generic baselines; they are not fields retained from
literature:

- actual Gaussian expected-potential and negative log-determinant derivatives,
  the symmetric Hilbert-coordinate norm identity and intrinsic SPD geometry;
- actual inverse Sylvester construction, mobility pairing, symmetry,
  positive definiteness and compact-sublevel ellipticity;
- strong convexity, coercivity, compact energy sublevels, the unique source
  minimizer, dissipation, trapping, moment exponential convergence and
  semiglobal physical-time stability;
- global actual moment/particle well-posedness after the generic ODE input,
  exact finite-particle closure and affine transport;
- source deterministic oracle Theorem 2.1;
- exact standardized-cloud identity (6.9), shape bound (6.10), root estimate
  (7.4), actual Gaussian initialization moment mismatch (7.3), and common
  deterministic sublevel on fixed and high-probability raw events;
- the combined logarithmic envelope moment (7.16), actual all-time pathwise
  envelope (7.20), and weighted bad-event SVGD error (7.11);
- the final expected, sharpness, high-probability and last-iterate conclusions,
  including measurable selected flows and the logarithmic-confidence change
  of parameter;
- finite limiting-cloud construction, preservation of standardized shape up to
  rotation, affine two-sided spectral cost bounds, actual empirical whitening
  continuity and the non-Gaussian limiting-floor conclusion.

The public complete contracts are assembled in `Paper38/Main.lean`,
`HighProbabilityMain`, `SourceSamplingLemmas`, and `SourceNonGaussian`.
Their theorem arguments, rather than this document's descriptions, determine
the exact formal dependency boundary. The explicit baseline propositions remain
known mathematical results retained externally, and are not represented as
locally proved theorems merely by being named or packaged.
