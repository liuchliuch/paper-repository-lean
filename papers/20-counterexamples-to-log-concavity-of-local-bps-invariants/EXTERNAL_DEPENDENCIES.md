# External dependencies and scope

Production uses **explicit parameters**, with no new axioms,
`sorry`, `admit`, or `sorryAx` allowance. The original unconditional
Comparator contract is retained separately from the relative contract.

## Type-A Hecke character theory

Source: A. Mathas, *Iwahori–Hecke Algebras and Schur Algebras of the
Symmetric Group*, University Lecture Series 15, AMS, 1999
([author's publication record](https://www.maths.usyd.edu.au/u/ResearchReports/Algebra/Mat/1998-13.html)).
A primary account of the Schur decomposition and seminormal/Murphy
formulas is Mathas, *Matrix units and generic degrees for the Ariki–Koike
algebras*, J. Algebra 281 (2004), 695–730
([preprint](https://arxiv.org/abs/math/0108164),
[publication](https://doi.org/10.1016/j.jalgebra.2004.07.021)):
Definition 2.5, Proposition 3.4, Corollary 3.15 and Corollary 5.16,
specialized to one component.

`Paper20.ExternalInput.MathasAt` states exactly:

* The normalized canonical trace of every element of the **actual original
  polynomial Hecke algebra**, specialized at `z=v-v⁻¹`, is the sum of
  traces in the **constructed actual standard-filling representations**,
  divided by `s_λ(v²)`.
* The actual full twist in each such representation is `(v²)^c_λ` times
  the identity.

Here `s_λ(q)=q^(-ν(λ)) ∏ (1-q^hook)/(1-q)`. Our convention is
`(G_i-q)(G_i+1)=0`, `q=v²`, `G_i=v T_i`. Row eigenvalue is `q` and column
eigenvalue is `-1`. The accessible preprint's page-2 quadratic relation
uses the opposite displayed convention, whereas its seminormal row/column
formulas use these eigenvalues; we therefore record the convention
explicitly and do not treat that displayed relation as a literal match.

The hypotheses are characteristic zero, `v≠0`, and injectivity of the
integer-power map. The latter guarantees generic parameters and excludes
roots of unity. `ExternalInputConditions` explicitly proves nonvanishing
of the type-A semisimplicity product and every actual Schur element.
`MathasInputs` requests the formula only at the two
**proved faithful formal parameters** `v=t` and `v=1+t`, for ranks at
least two. The field, actual representations, relations, their dimensions,
and the original canonical algebra are constructed internally.

Internally proved consequences include the conversion
`s_λ(v²)=v^c_λ ∏[hook]_v`, the partition trace formula, original Hilbert/BPS
expansion, positivity, same-Q evaluation, Q at zero, and the leading
coefficient's equality to the cardinal of genuine transposition returns.
None of those conclusions is a field of the external input.

## Hilbert–HOMFLY and ruling theory

Sources:

* P. Freyd, D. Yetter, J. Hoste, W. B. R. Lickorish, K. Millett and
  A. Ocneanu, *A new polynomial invariant of knots and links*, Bull. AMS
  12 (1985), 239–246, Main Theorem, p.240, and the universal skein-module
  isomorphism lemma, p.241
  ([primary paper](https://www.math.ucdavis.edu/~egorskiy/MAT280-s18/HOMFLY.pdf),
  [DOI](https://doi.org/10.1090/S0273-0979-1985-15361-3)).
* D. Maulik, *Stable pairs and the HOMFLY polynomial*, Invent. Math. 204
  (2016), 787–831, Theorem 1.1
  ([primary paper](https://arxiv.org/html/1210.6323v1#S1.Thmtheorem1)).
* A. Oblomkov and V. Shende, *The Hilbert scheme of a plane curve
  singularity and the HOMFLY polynomial of its link*, Duke Math. J. 161
  (2012), 1277–1303
  ([primary paper](https://arxiv.org/abs/1003.1568)).
* D. Rutherford, *The Bennequin number, Kauffman polynomial, and ruling
  invariants of a Legendrian link: the Fuchs conjecture and beyond*,
  IMRN 2006, Article 78591, Theorem 4.1
  ([primary paper](https://arxiv.org/pdf/math/0511097)).
* T. Su, B. Xie and C. Yu, *Log-concavity from enumerative geometry of
  planar curve singularities*, arXiv:2603.27888v2, 30 April 2026,
  Definition 2.1 and equation (2.1)
  ([primary paper](https://arxiv.org/html/2603.27888v2#S2)).

`GeometricData` supplies the integer Euler characteristics of the punctual
Hilbert schemes of `y^r=x^(rk)`, the full HOMFLY data of its link in both
z conventions, and the ruling value of the rainbow closure of `Delta^(2k)`.
Full HOMFLY values are actual Laurent series in a over the formal parameter
field. `lowestHOMFLY` is the actual Hahn-series coefficient at `mu`, not
an opaque supplied coefficient-extraction functional. **The schemes,
Euler characteristic, link, and Legendrian construction themselves are not
constructed in Lean.** The interpretation of the supplied data as those
geometric invariants is part of the disclosed external boundary.
This includes the usual identification of the singularity link with the
closure of `Delta^(2k)` and its standard parameters `b=r`,
`delta=k choose(r, 2)`, `mu=2 delta+1-r`. The algebraic-link/Milnor-fiber
background is used in the source's §2 and in Su–Xie–Yu §4.1; it is not a
claimed Lean construction of a singularity or its Milnor fiber.

`HOMFLYInputs` records the standard normalized skein characterization and
uniqueness (positive and opposite z), plus the standard pure-braid component
count `r`. The link and crossing types and all usual smoothing/component
properties are explicit supplied data, not constructed link theory.
The universal skein theorem is used after base change
`x=a⁻¹,y=-a,z_original=-z`; both actual formal parameters are proved nonzero.
It supplies no sign-conversion conclusion. The elementary transformation
is internally proved and coefficient extraction uses actual Laurent series.

`GeometricInputs data`, for `r≥2,k≥1`, requests precisely:

1. `Theta_opposite=v^(-mu) (1-v²) H(v²)`, where
   `mu=2 deg(r,k)+1-r`, `H` is built from the supplied integer Euler data,
   and `Theta_opposite` is the actual a coefficient in the original
   opposite-z convention of Hilbert–HOMFLY. The corrected factor
   `(-1)^(r-1)` is **not an input**.
2. `Theta=z R`, the Rutherford specialization for this positive braid,
   whose crossing number is `2 deg(r,k)` and whose branch count is `r`.
3. `R=z^(-r) W`, where **W is the actual already defined closed Hecke
   walk polynomial**, from the original walk/ruling formula (2.1).

We do not copy the missing sign in equation (4.1) of Su–Xie–Yu v 2.
The paper's equations (8), (11), (13), equality of geometric and computed
BPS coefficients, and both counterexamples are **not** external fields.
The sign/exponent cancellation, complete Hilbert series equality,
integer original genus expansion, and identification with the executable
extraction are proved in `Paper20/GeometricInput.lean`.
`Paper20.SkeinParity.convention_sign` proves the opposite-z conversion
for any normalized HOMFLY skein system, using its standard uniqueness
property and the component-number change under smoothing. The elementary
sign transformation itself is therefore not an omitted step.
`HOMFLYInput.homfly_coefficient_sign` applies it to the full invariant and
actual a coefficients. `GeometricInputs.hilbert_homfly` is a **proved
theorem**, deriving precisely the corrected equation(7), used in every
downstream geometric bridge. It is no longer an external structure field.

## Validation meaning

A checked theorem quantified over these inputs is an implication
relative to precisely these dependencies. The full current production graph remains pending heavy verification. It is not an unconditional Lean
construction of the external theories. The full production axiom audit
continues to permit only `propext`, `Classical.choice`, and `Quot.sound`.
An explicit external parameter never licenses a new premise for a step
originating in paper 20, including its finite partition computations.


The shared release tooling installs the pinned official Comparator. Comparator challenge modules may contain specification placeholders; these are isolated from production proofs. Negative controls intentionally contain an added premise or an illegal axiom and are verification fixtures. No new axioms or proof placeholders were introduced by release curation.

## Local generated artifacts

The generation recipe supplies untrusted numeric candidates surrounded by the retained current proof-check scaffolding. Its exact-output manifest is a source integrity boundary, not an external mathematical assumption. Recreating the source does not discharge the kernel computations, complete the deferred whole-graph audit, or change the declared external dependencies. No new axiom, admission or finite-certificate premise is introduced.
