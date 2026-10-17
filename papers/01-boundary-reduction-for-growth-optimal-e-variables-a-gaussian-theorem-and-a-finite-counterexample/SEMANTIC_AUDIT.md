# Statement correspondence

The eight numbered source results are mapped to public Lean declarations in `publication.json`. The fixed Comparator configuration includes these statements and additional analytic checks. No paper-specific external theorem is assumed.

## Lemma 2.1

`NEF.lemma_2_1` proves the measure-theoretic maximin bound for every subfamily
of the actual tilted laws `P₀.tilted (inner θ Y)`. Parameters can be indexed by
any type, which includes an arbitrary set of mean parameters. An open natural
domain and finite exponential moments on that domain supply finite component KL;
convexity of `klFun` supplies finite KL for every finite mixture. Minimality,
centering, and a nonempty index set are unnecessary for this bound.

`MeasureEVar` ranges over measurable real-valued nonnegative statistics with
integrable null expectation at most one. Zeros are permitted. `logExpectation`
is the difference of actual positive and negative Lebesgue integrals; at zero
the negative logarithmic part is infinity. Finite KL gives integrability of the
positive part, and the extended expectation is either a finite real number or
minus infinity. `evar_zero_mean` proves the null-mean-zero case explicitly.
`evar_logExpectation_le_kl_add_log_mean` proves the full inequality (2.9).
No integrability of the untruncated logarithm is assumed in the final upper bound.

## Theorem 3.1

The alphabet, positive masses, partition sum, tilts, and Euclidean mean are
explicit finite expressions in `NinePoint`. `alphabet_minimal` verifies that
the alphabet lies in no proper affine hyperplane; the finite partition sum is
positive at every natural parameter. The natural parameter domain is all ℝ².

`NinePointMeanImage` proves that the closed excluded ball lies in the actual
mean image by minimizing the log-partition potential on a larger closed ball.
`excluded_ball_geometry` proves compact containment and identifies the actual
Euclidean frontier. `mean_injective` proves identifiability of natural parameters
from the mean, and Lusin–Souslin gives the Borel inverse on the mean image.
Thus the Borel transport uses a proved inverse, with no assumed inverse map.

`MeanPrior` has actual mean parameters; `meanInformation_eq` proves exact equality
of its finite-mixture infimum with the natural-coordinate implementation.
`theorem_3_1_mean` proves 0<I(A)<2e-15, I(Γ)>7e-12 and excludes the global
expected-log inequality for every Borel prior on the mean circle. Mixture masses
are actual integrals of the component masses (`meanBoundaryMixture_mass`).

## Proposition 3.2

`FiniteExponential` treats an arbitrary finite alphabet, positive base law,
Euclidean sufficient statistic, and the concrete affine-span definition of
minimality. Every exposed normal is a witness to the usual strict supporting
hyperplane condition. `tilt_tendsto_vertex` and `mean_tendsto_vertex` prove the
exposed limits. `remote_kl_tendsto` includes zero masses of the limiting
conditional distribution and identifies its KL as -log α.

`ExposedTheorem.proposition_3_2_full` uses the actual mean-space exterior M\B,
proves both information bounds and their strict comparison, and excludes the
global inequality for every Borel boundary prior in mean coordinates. Its
measurable inverse is proved in `FiniteMeanCoordinates`. The proof needs fewer
geometric assumptions than the source: containment of the closure in the mean
image suffices for remote feasibility. The dimension/minimality assumptions
imply a nontrivial alphabet; this is proved rather than assumed in the final
statement.

## Theorem 4.1

`GaussianTheorem.theorem_4_1_covariance` takes a centered Gaussian measure Z with
its actual covariance operator Σ, symmetry, and positive definiteness.
`exists_precision_of_covariance` constructs the inverse K. The location laws
are the actual translated measures `Z.map (fun x => x+μ)`.

`mixtureMeasure_apply` identifies the density construction with the countably
additive Borel mixture of these location laws. `mixture_klDiv` identifies the
entropy integral with actual measure-theoretic KL. Compactness of all Borel
priors, continuity, Gaussian tilt/translation, identifiability and strict
convexity are proved in the library. The final conclusion contains unique Borel
minimization, strictly positive finite c, GROW(A)=I(A)=I(Γ)=c, the full exterior
expected-log bound, support equalization, the actual KL Pythagorean inequality
for every finite exterior mixture, and the normalized optimal e-variable.

`BoundaryConclusion` packages these output assertions. It is the theorem's
conclusion and is never required as an input hypothesis.

## Proposition 4.2 and Lemma 4.3

`proposition_4_2_iff` proves both directions of the Borel variational criterion.
The necessity proof uses actual one-point prior perturbations and a controlled
quadratic remainder. `proposition_4_2_gap` proves the computable gap certificate;
`minimizer_support_equalization` proves equality at every support point.
`first_exit_propagation` proves Lemma 4.3 for arbitrary open neighborhoods of
zero, without shape, connectedness, or smoothness assumptions on the set.

## Corollary 4.4

`GaussianCoupling` proves the integral log-sum inequality for a common Borel
mixing measure and the actual Gaussian relative KL bound in (4.22).
`corollary_4_4_map` proves (4.20). `corollary_4_4_finite` supplies a genuine finite
prior on the optimal support with the exact KL identity and quadratic bound
(4.21). `corollary_4_4_family` selects these for every positive δ and proves weak
convergence along the right-neighborhood filter as δ tends to zero.

## Lemma A.1 and unnumbered displays

`lemma_A_1` uses the actual eight tilts at t=200, proves all component means are
exterior, and proves their actual KL sum is below 1.001e-15 by analytic bounds.
`AppendixFormulas.lean` additionally proves all exact normalizer, mass,
KL and component-mean-norm formulas (A.5)–(A.12). They are checked together by
`Verification.appendix_closed_forms`.

The general background characterization of the mean image as an interior
convex hull and the smooth inverse theorem quoted from Brown are not imported
as axioms. The needed containment, injectivity and Borel inverses are proved
directly. No numbered result is waived for that background material.
