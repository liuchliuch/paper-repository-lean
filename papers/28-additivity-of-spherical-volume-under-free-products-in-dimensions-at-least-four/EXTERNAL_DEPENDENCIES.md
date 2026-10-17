# Explicit standard foundations

The latest delivery records **all eight paper-owned derivations complete relative to 24 explicit standard foundations**. The production entry contains no `sorry` or new axiom. Generic foundational objects and theorem witnesses are parameters and are not constructed in Lean here; neither closed native foundations nor unconditional whole-paper acceptance are claimed.

[external-inputs.json](external-inputs.json) retains the exact English scope, sources, excluded paper-owned conclusions and state of every input. The main standard-input pack and each original-result wrapper expose these parameters. Known combined standard consequences are identified as combined consequences rather than assigned invented numbered source statements.

## Song-standard-round-orbit-metric

A. Song, Spherical volume and spherical Plateau problem, arXiv:2202.10636v6 (7 April 2025), Section 3.1, printed pp. 20-21.

Lean interfaces: `Paper28.SphericalQuotientMetricInput`.

Scope: Only the standard round metric object on the actual native regular Hilbert sphere orbit quotient: its topology is the already constructed quotient topology, and its distance is exactly the infimum over group translates of arccos of the actual Hilbert inner product. The real l2 space, unit sphere, regular action and orbit quotient themselves are native constructions.

Paper-owned boundary: No deformation, map, projection, local Lipschitz bound, homotopy, carrier, current, mass, approximation or transfer is supplied. Chord-angle comparisons, sharp local Lipschitz descent, finite carriers and the relative construction are proved locally.

Status: used as an explicit metric-object theorem parameter; no axiom or closed witness; standard metric realization itself is not rebuilt

Primary references: [source 1](https://arxiv.org/pdf/2202.10636v6).

## AK-metric-current-calculus

L. Ambrosio and B. Kirchheim, Currents in metric spaces, Acta Math. 185 (2000), 1-80, DOI 10.1007/BF02392711. Homotopy product formula is also stated in Riedweg-Schäppi, Proposition 2.8 (Wenger Theorem 3.2). For real test evaluations and Euclidean compatibility, see also U. Lang, Local currents in metric spaces (2011), author preprint revised 5 May 2010: Proposition 2.6, Lemma 3.2, Theorem 5.5, preprint pp.16,18,35-37; the latter cites AK Theorem 11.1 for compact finite-mass currents.

Lean interfaces: `Paper28.CompactIntegralCurrentSupportInput`, `Paper28.CompactIntegralCurrentAlgebraInput`, `Paper28.SphericalSimplexIntegrationInput`, `Paper28.EuclideanSimplexIntegrationInput`, `Paper28.EuclideanCurrentTangentInput`, `Paper28.NeighborhoodCurrentPushforwardInput`, `Paper28.EuclideanCurrentAreaInput`, `Paper28.TwoStagePushforwardFunctorialityInput`, `Paper28.LipschitzSimplexIntegrationInput`, `Paper28.SimplexPushforwardCompatibilityInput`, `Paper28.CurrentMassFaithfulnessInput`, `Paper28.EuclideanAffineSupportTangentInput`, `Paper28.EuclideanSimplexSeparationInput`, `Paper28.ComponentCurrentDecompositionInput`, `Paper28.LocalCurrentPushforwardCalculusInput`, `Paper28.CompactCurrentHomotopyInput`, `Paper28.CanonicalLocalPushforwardInput`.

Scope: Compact integral currents with integer coefficients; boundary squared zero; Lipschitz pushforward preserving integrality and commuting with boundary; individual mass/area estimates; interval-product boundary formula.

Paper-owned boundary: No joint tree-shadow mass bound, no Bass-Serre transfer, no near-isometric relative carrier deformation, and no finite-isotropy sharp approximation are included.

Status: typed standard current, metric-pinned support/boundary/mass, lower semicontinuity and simplex integration/Stokes signatures compiled; used as explicit published-object parameters; no native AK witness claimed

Primary references: [source 1](https://www.mis.mpg.de/de/publications/preprint-repository/article/2000/issue-21), [source 2](https://arxiv.org/pdf/0902.3831), [source 3](https://people.math.ethz.ch/~lang/Lang_LocalCurrents.pdf).

## FF-Euclidean-deformation-and-approximation

H. Federer and W. H. Fleming, Normal and integral currents, Ann. Math. 72 (1960), 458-520, deformation Theorem 5.5 and strong approximation Theorem 8.22; localized forms cited by the source paper in Federer, Geometric Measure Theory (1969), Sections 4.1-4.2. The theorem numbering is confirmed by Fleming’s author retrospective, pp. 179-180.

Lean interfaces: `Paper28.EuclideanDeformationInput`.

Scope: Standard Euclidean deformation and strong approximation of integral currents, with integer multiplicities and the stated mass/boundary controls.

Paper-owned boundary: The exact localized-cycle refinement, sharp mass after piecewise spherical retraction, and finite-isotropy quotient approximation are not assumed.

Status: typed initial localized decomposition and polyhedral-boundary deformation signatures compiled as explicit theorem parameter; no exact-cycle or sharp retraction conclusion supplied

Primary references: [source 1](https://doi.org/10.2307/1970227), [source 2](https://appliedmath.brown.edu/sites/default/files/2021-11/Early%20Developments%20in%20Geometric%20Measure%20Theory.pdf).

## RS-current-homology-comparison

C. Riedweg and D. Schäppi, arXiv:0902.3831v1, Definition 1.1; Corollaries 1.4 and 1.6; homotopy product Proposition 2.8.

Lean interfaces: `Paper28.LipschitzCurrentHomologyComparisonInput`.

Scope: For spaces satisfying locally strong Lipschitz contractions (and completeness for the integral-current comparison), the canonical maps identify compact integral-current, integral Lipschitz-singular and singular homology.

Paper-owned boundary: No finite-carrier contraction hypothesis, simplicial integration homology isomorphism or prescribed filling is supplied. Native actual retraction contraction bounds and biLipschitz transfer prove completeness/local strong contractions for the spherical chart realization. The simplicial integration homology injection and exact filling are derived separately.

Status: typed explicit comparison parameter pinned to the canonical locally constructed Lipschitz singular integration chain map; requires exact CompleteSpace and AdmitsLocallyStrongLipschitzContractions hypotheses; no closed witness

Primary references: [source 1](https://arxiv.org/pdf/0902.3831).

## Song-spherical-volume-framework

A. Song, Spherical volume and spherical Plateau problem, arXiv:2202.10636v6 (7 April 2025), Sections 3.1-3.4.2; Lemma 1.6; Theorem 4.1.

Lean interfaces: `Paper28.IntegralGroupHomologyInput; Paper28.SongSphericalHomologyInput`.

Scope: Standard integral group homology objects, induced maps/identity/composition; Song canonical comparison into the native homology short complex of the actual compact integral-current groups, existence of cycle representatives, and naturality under actual group-homomorphism norm foldings (23). The native groupHomSphereFold/groupHomQuotientFold and their equivariance/1-Lipschitz property are compiled. The identity group homomorphism gives the actual absolute-value map, so its comparison-class preservation is derived from ordinary naturality and map_identity. Spherical volume is the native infimum of masses of actual cycles in the comparison class.

Paper-owned boundary: No approximation in singular quotients, relative filling, transfer, factor transfer recovery, free-product lower bound/additivity or connected-sum conclusion.

Status: precise typed external standard group homology objects and Song comparison/naturality parameters; current homology and mass-infimum are native actual-current constructions; no closed witness claimed

Primary references: [source 1](https://arxiv.org/pdf/2202.10636v6).

## classical-multi-block-Fischer

T. H. Pate, Exterior products, elementary symmetric functions, and the Fischer determinant inequality, Linear Algebra Appl. 255 (1997), 203-242, DOI 10.1016/S0024-3795(96)00044-4. Multi-block form: Linear Principal Minor Polynomials: Hyperbolic Determinantal Inequalities and Spectral Containment, IMRN 2023(24), Corollary 4.5 and Remark 4.6.

Lean interfaces: `Paper28.FischerInput`.

Scope: For every real PSD n-by-n matrix and an injective selection of two coordinates, det M is at most the selected 2-by-2 principal determinant times the product of all remaining diagonal entries.

Paper-owned boundary: No norm folding, tangent plane, current, tree, transfer or spherical-volume assertion is assumed. Diagonal contraction bounds, complement product bounds and the geometric application are derived locally.

Status: used as an explicit theorem parameter; no new axiom or closed external witness

Primary references: [source 1](https://www.sciencedirect.com/science/article/pii/S0024379596000444), [source 2](https://academic.oup.com/imrn/article/2023/24/21346/6819958).

## finite-sphere-rectifiable-tangent-calculus

Ambrosio-Kirchheim (2000), Currents in metric spaces, rectifiable-current representation and finite-dimensional Euclidean compatibility; classical approximate-tangent/Rademacher locality in Federer, Geometric Measure Theory (1969), Section 3.2.

Lean interfaces: `Paper28.RectifiableSphereCalculusInput`.

Scope: Rectifiable sphere-current objects with mass measure, almost-everywhere n-plane dimension and sphere tangency, approximate differentials, smooth restriction, equality-set locality and linearity. Their exact generic signatures are fixed in Lean.

Paper-owned boundary: No field contains a Jacobian inequality. Linear-kernel tangent locality, folding approximate differentials and the full joint n-Jacobian estimate are proved from the generic laws.

Status: opaque external object/calculus signature used as explicit parameter; no native AK object implementation claimed

Primary references: [source 1](https://www.mis.mpg.de/de/publications/preprint-repository/article/2000/issue-21), [source 2](https://doi.org/10.1007/BF02392711).

## classical-Cauchy-Binet

R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd edition, Cambridge University Press (2012/2013), Section 0.8.7, p.28; compound matrices Section 0.8.1. DOI 10.1017/CBO9781139020411.

Lean interfaces: `Paper28.CauchyBinetInput`.

Scope: The universal rectangular Cauchy-Binet determinant identity with canonically ordered k-element row/column subsets.

Paper-owned boundary: No geometric Jacobian, tangent, polyhedron, mass bound or current estimate. Actual Plucker coordinate vectors, their Gram norm identity and actual compound-action Jacobians are constructed locally.

Status: compiled precise explicit classical linear algebra parameter; no axiom or witness

Primary references: [source 1](https://doi.org/10.1017/CBO9781139020411).

## Reshetnyak-strict-polar-continuity

Yu. G. Reshetnyak, The weak convergence of completely additive vector-valued set functions, Siberian Mathematical Journal 9(6) (1968), 1039-1045, DOI 10.1007/BF02196453. Exact bounded-continuous polar formulation: F. Rindler and G. Shaw, Strictly continuous extension of functionals with linear growth to the space BV, Quart. J. Math. 66 (2015), Theorem 2.5, p.958, DOI 10.1093/qmath/hav022.

Lean interfaces: `Paper28.StrictPolarMeasureContinuityInput`.

Scope: Generic actual finite Borel measures on finite Euclidean space, measurable unit vector densities, weak convergence of vector integrals against bounded continuous scalar tests and convergence of total masses imply weak convergence of the actual spatial-polar pushforward finite measures.

Paper-owned boundary: No current/polyhedral approximation, Jacobian, retraction, sharp upper mass or transfer statement is supplied. Native unit-barycenter concentration is separately proved.

Status: compiled generic explicit measure-theory parameter; instantiated for actual Euclidean AK mass measures and Plucker densities in strict_tangent_measure_tendsto and the constructed exact polyhedral approximation

Primary references: [source 1](https://www.mathnet.ru/eng/smj5605), [source 2](https://api.repository.cam.ac.uk/server/api/core/bitstreams/0082de86-e9e7-491c-bf02-f09c09f797aa/content).

## bounded-upper-Portmanteau

P. Billingsley, Convergence of Probability Measures, 2nd edition (1999), Theorem 2.1, bounded upper-semicontinuous integral form; finite-measure form includes total-mass convergence. Mathlib pinned Portmanteau.lean independently provides the closed-set finite-measure form.

Lean interfaces: `Paper28.UpperPortmanteauInput`.

Scope: For weakly convergent actual finite Borel measures on a metric space and a globally bounded nonnegative upper-semicontinuous real function J, its integrals are eventually at most the limiting integral plus every positive epsilon.

Paper-owned boundary: No geometric integrand, current, Jacobian equality or sharp mass bound is included; the actual incident compound-Jacobian envelope and its tangent value are own proofs.

Status: compiled generic explicit measure-theory parameter; instantiated with the actual native bounded incident exterior-Jacobian envelope in sharp_exterior_envelope_integral

Primary references: [source 1](https://doi.org/10.1002/9780470316962), [source 2](https://github.com/leanprover-community/mathlib4/blob/f897ebcf72cd16f89ab4577d0c826cd14afaafc7/Mathlib/MeasureTheory/Measure/Portmanteau.lean).

## classical-simplicial-singular-comparison

A. Hatcher, Algebraic Topology, Section 2.1, Theorem 2.27, printed pp. 128-130. Author-hosted primary PDF verified.

Lean interfaces: `Paper28.SimplicialSingularHomologyComparisonInput`.

Scope: For any native finite Euclidean simplicial complex and a Lipschitz homeomorphic realization, the canonical characteristic-simplex map from its actual strict ordered integer simplicial chain complex to the actual continuous singular chain complex induces homology isomorphisms. Vertices, ordered/strict simplices, alternating boundaries and the actual barycentric map are local constructions.

Paper-owned boundary: No current integration map or its homology injectivity/isomorphism, no sharp approximation, no spherical filling or other own estimate is supplied.

Status: precise explicit standard comparison parameter; no axiom or closed witness; source filling is derived using this and the separate RS comparison

Primary references: [source 1](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf).

## classical-Euclidean-common-cell-subdivision

C. P. Rourke and B. J. Sanderson, Introduction to Piecewise-Linear Topology (1972), Section 2: cell intersections 2.8(5)-(6), simplicial subdivision Proposition 2.9, simultaneous subcomplex Addendum 2.12, printed pp.15-16; with canonical affine integration additivity under subdivision (standard Euclidean polychain/current compatibility). Primary printed text verified, PDF pp.22-23.

Lean interfaces: `Paper28.EuclideanPolyhedralCellSubdivisionInput`.

Scope: For an actual Euclidean integral polyhedral current supported in an open set covered by finitely many convex hulls of finite vertex sets, common affine subdivision supplies a finite integer decomposition into actual affine simplex integration currents, each contained in the open set and one convex cell. The generic input combines classical simultaneous subdivision with canonical affine integration additivity/locality.

Paper-owned boundary: No spherical map, retraction, approximate cycle, homology, prescribed filling, mass estimate, collapsed-image vanishing or spherical-polyhedral preservation is supplied. Explicit projective formulas, actual image geometry, rank-drop zero current and linear pushforward membership are local own proofs.

Status: precise explicit generic Euclidean subdivision parameter; no axiom or closed witness

Primary references: [source 1](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/rsplx.pdf), [source 2](https://doi.org/10.1007/978-3-642-81735-9).

## standard-intrinsic-spherical-cell-metric

M. W. Davis, The Geometry and Topology of Coxeter Groups, Appendix I.3, printed p.508 (author primary PDF p.523): the intrinsic metric of a piecewise spherical polyhedron is the infimum of lengths of finite cellwise geodesic paths; connected components are treated separately.

Lean interfaces: `Paper28.SphericalCellPathMetricInput`.

Scope: Only exact metric-defining data on one connected actual spherical chart realization: finite paths use actual lifted points in actual closed spherical cells and lengths are actual round angles; paths exist between each pair and dist is exactly the infimum of their lengths.

Paper-owned boundary: No Lipschitz constant for h or its inverse, no retraction, deformation, homotopy, current, mass or approximation is supplied. One-cell distance upper bounds and generic Lipschitz gluing along the exact native paths are own proofs.

Status: precise explicit intrinsic metric-object parameter; actual paths and length are native constructions; no closed metric witness or axiom

Primary references: [source 1](https://people.math.osu.edu/davis.12/davisbook.pdf).

## classical-spherical-full-neighborhood-realization

Rourke and Sanderson, Introduction to Piecewise-Linear Topology (1972), Proposition 2.9, Addendum 2.12, and Lemma 3.3(a), printed pp.15-16,31 (primary PDF pp.22-23,38). Applied to the ordinary PL structure of finite spherical cells in gnomonic coordinates, with the defining intrinsic cell-path metric (Davis Appendix I.3).

Lean interfaces: `Paper28.SphericalFullNeighborhoodInput`.

Scope: For a finite spherical triangulation defined independently of any neighborhood atlas, construct only an actual finite Euclidean realization and a classical full-subcomplex neighborhood triangulation, with actual barycentric hats, affine slopes, normalized spherical cell charts, independent unit vertices, cellwise linear isometric coordinate inclusions into the source charts, and exact intrinsic metric identification. Full-subcomplex neighborhood existence and compatibility are an explicit standard PL construction corollary, not claimed as a verbatim single numbered theorem.

Paper-owned boundary: No Lipschitz bound for the realization or inverse, no retraction/homotopy, derivative, sharp mass, current approximation, cycle, homology or filling is supplied. The actual h/h-inverse bounds, actual deleting-and-renormalizing retraction, contractions and all analytic estimates are native proofs.

Status: precise explicit standard geometric-object construction parameter; no axiom or closed witness

Primary references: [source 1](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/rsplx.pdf), [source 2](https://people.math.osu.edu/davis.12/davisbook.pdf).

## classical-finite-geodesic-common-refinement

Rourke and Sanderson, Introduction to Piecewise-Linear Topology (1972), cell intersections 2.8(5)-(6), simplicial subdivision 2.9 and simultaneous subcomplex refinement 2.12, printed pp.15-16. Elementary gnomonic-coordinate corollary for finite spherical geodesic pieces, combined only with canonical AK simplex-integration additivity under subdivision.

Lean interfaces: `Paper28.SphericalFiniteRefinementInput`.

Scope: For any finite collection of actual independent geodesic simplex parameterizations contained, via linear isometric coordinate inclusions, in actual source spherical cells, common geometric refinement returns only an actual refined finite Euclidean/spherical cell realization and finite signed characteristic-simplex decompositions whose canonical integration equals each given simplex current. This is a standard common-subdivision plus canonical integration compatibility corollary, not a separately numbered theorem in the source.

Paper-owned boundary: No simplicial cycle condition, homology comparison, current boundary, filling, approximation or mass estimate is a field. Finite integer assembly of any source polyhedral current, actual integration injectivity, deduction of its simplicial cycle condition and exact prescribed polyhedral filling are native proofs.

Status: compiled precise explicit generic geometric subdivision/integration compatibility parameter; no axiom or closed witness

Primary references: [source 1](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/rsplx.pdf), [source 2](https://www.mis.mpg.de/de/publications/preprint-repository/article/2000/issue-21).

## general-finite-round-quotient-realization

Rourke–Sanderson, Introduction to Piecewise-Linear Topology, §2 (2.8–2.12); Bridson–Haefliger, Metric Spaces of Non-Positive Curvature, I.7 (polyhedral subdivision 7.49; finite distortion 7A.12–7A.13, printed pp.128–129); Davis, Appendix I.3. A combined finite proper geodesic-chart/common-refinement corollary, not a verbatim separately numbered theorem.

Lean interfaces: `Paper28.FiniteRoundQuotientRealizationInput`.

Scope: For any finite collection of actual proper finite-coordinate geodesic charts in the regular round orbit quotient, with explicit finite overlap translates, general common refinement/realization supplies a finite spherical polyhedron, its exact identification with the covered set, ordinary bi-Lipschitz comparison, actual linear isometric chart lifts and round metric agreement along every relative face. No numerical sharp constant is supplied. The actual coordinate carrier is proved natively to admit this presentation: finite_carrier_liftable_simplex_cover plus projected_liftable_simplex_intersection.

Paper-owned boundary: No deformation, current, polyhedral approximation, homology, relative filling, transfer or free-product volume assertion.

Status: precise explicit unformalized general geometric-foundation parameter; actual native presentation hypotheses checked in finite_carrier_spherical_presentation; no axiom or closed witness

Primary references: [source 1](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/rsplx.pdf), [source 2](https://www.maths.ed.ac.uk/~v1ranick/papers/bridsonhaefligerx.pdf), [source 3](https://people.math.osu.edu/davis.12/davisbook.pdf).

## AK-finite-stratified-current-transport

Ambrosio–Kirchheim (2000), rectifiable representation, pushforward/area and locality; Lang, Local currents in metric spaces, Proposition 3.3, equations (3.3)–(3.5), Lemmas 3.7 and 4.6–4.7; common subdivision from Rourke–Sanderson §2. Combined standard canonical-object/compatibility corollary, not a separately numbered approximation theorem.

Lean interfaces: `Paper28.FiniteRoundCurrentTransportInput`.

Scope: On an already supplied finite spherical realization with actual forward/inverse Lipschitz maps, exact chart lifts and relative-face local metric agreement, supply canonical AK algebras on the space/components and their standard calculus foundations. The canonical closed-support pull/push is an additive chain equivalence, preserves mass by finite relative-face restriction and metric locality, and identifies the finite geodesic polyhedral subgroups by common subdivision and change of variables (including positive vertex normalization). This is a universal compatibility theorem on arbitrary finite proper spherical-chart presentations, not a carrier approximation/filling premise.

Paper-owned boundary: No cycle, approximation sequence, homology equivalence of a prescribed cycle, existence of filling, sharp deformation estimate, transfer independence/boundary/joint mass, or additivity conclusion.

Status: precise explicit unformalized standard AK/PL compatibility parameter; no axiom or closed witness; source 3.1 conclusions must be derived using proved 5.1 and 5.2

Primary references: [source 1](https://doi.org/10.1007/BF02392711), [source 2](https://people.math.ethz.ch/~lang/Lang_LocalCurrents.pdf), [source 3](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/rsplx.pdf).

## standard-Bass-Serre-free-product-object

J.-P. Serre, Trees (1980), Chapter I, §4.1, Theorems 6–7, pp.32–35; publisher primary entry and original SMF edition.

Lean interfaces: `Paper28.BassSerreStructureInput`.

Scope: For actual subgroups A,B of G satisfying the exact categorical free-product universal property, the actual coset graph on (G/A) disjoint union (G/B), edge g joining gA and gB, is a tree; its edges are bijectively labeled by G, and incident neighbors are labeled by A or B using the explicit chosen coset representative.

Paper-owned boundary: No branch shadow, contraction, finite transfer, lift/presentation independence, boundary formula, joint mass or additivity. All are separate native proofs.

Status: precise explicit unformalized standard structure parameter; actual coset graph and universal property defined natively; no axiom or closed witness

Primary references: [source 1](https://doi.org/10.1007/978-3-642-61856-7), [source 2](https://smf.emath.fr/publications/arbres-amalgames-sl2-3e-edition).

## generic-geodesic-current-presentation-gluing

Rourke–Sanderson §2, 2.8–2.12, finite common subdivision; AK canonical integration locality and pushforward; Lang Proposition 2.6 and Lemma 3.7 (Euclidean integration/change of variables), finite simplex test-form separation. This is a combined standard geodesic-current presentation corollary, not a separately numbered published transfer theorem.

Lean interfaces: `Paper28.SphericalCurrentGluingInput; Paper28.LiftedSphericalSimplexIntegrationInput`.

Scope: For the canonical integrations of arbitrary proper finite-coordinate spherical simplex charts, the projection of actual lifted integration is actual quotient integration; its finite formal integer presentation kernel is generated by lifted-current zero relations and group-translation relations. Ordinary simplex Stokes admits finite proper-chart common refinement of faces. The actual source hypotheses are carried by LiftableSphericalSimplex (unit/independent/hemisphere/finite coordinates/closed injection/interior local isometry), the native exact finite-overlap theorem and proper regular action. These inputs apply to every countable group and contain no Bass–Serre tree or shadow.

Paper-owned boundary: No transfer, lift/presentation independence of any shadow sum, transfer boundary identity, joint mass, approximation, filling or additivity. Native sphericalLiftRelations_killed and surjective additive descent prove the concrete independence; native finite integer Stokes assembly and raw boundary theorem prove equation (10).

Status: precise explicit unformalized standard PL/canonical-current compatibility corollary; no axiom or closed witness; not counted as a native reconstruction of the general gluing theorem

Primary references: [source 1](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/rsplx.pdf), [source 2](https://people.math.ethz.ch/~lang/Lang_LocalCurrents.pdf), [source 3](https://doi.org/10.1007/BF02392711).

## AK-finite-coordinate-individual-area

Ambrosio–Kirchheim, Currents in metric spaces (2000), rectifiable representation and area formula; Lang, Local currents in metric spaces, Lemma 4.6 (individual pushforward mass), Lemma 4.7 (Borel restriction/mass locality), §8 (rectifiable representation). Finite orthogonal coordinate inclusion/partition compatibility is the ordinary isometric coordinate-change corollary. Not a separately numbered joint estimate.

Lean interfaces: `Paper28.FiniteCoordinateCurrentAreaInput`.

Scope: A current on the native regular sphere supported in a chosen finite coordinate set has its canonical finite-Euclidean rectifiable-current representation, with total mass exactly equal to the actual source current mass and integrable actual Gram Jacobians. For any single coordinate-partition norm map followed by a contracting round orbit projection, its individual pushed mass is at most the integral of the actual finite-partition Jacobian, provided the exact coordinate routing identity is supplied. The actual Bass–Serre routing identities and finite edge inclusion are native proofs.

Paper-owned boundary: No tree, sum of Jacobians, Jacobian upper bound, transfer or joint mass inequality. Native lemma_2_3 and finite integration yield bassSerre_hull_joint_area; native sum extension/triangle inequality yields the raw joint bound.

Status: precise explicit unformalized generic individual AK area/coordinate-compatibility foundation; exact actual finite hull/routing hypotheses checked natively; no axiom or closed witness

Primary references: [source 1](https://doi.org/10.1007/BF02392711), [source 2](https://people.math.ethz.ch/~lang/Lang_LocalCurrents.pdf).

## standard-geodesic-polychain-mass-presentation

Rourke–Sanderson §2, finite common subdivision 2.8–2.12; AK canonical integration and injective locally isometric area/mass locality; Lang Lemmas 3.7, 4.6–4.7. Standard finite geodesic polychain normal-presentation corollary, not a transfer theorem.

Lean interfaces: `Paper28.GeodesicPolyhedralMassInput`.

Scope: Every actual finite integer geodesic polyhedral current admits a finite common-refined presentation with disjoint projected relative interiors. Its actual mass is the sum of absolute integer coefficients times the actual lifted simplex integration masses, using only injective/interior-local-round chart compatibility. All geometries are actual LiftableSphericalSimplex objects; finite relevant overlap translates are natively proved.

Paper-owned boundary: No shadow, transfer, area bound for a family, approximation, homology, filling or additivity. The native joint simplex transfer inequality and native integer triangle/sum assembly prove (11).

Status: precise explicit unformalized standard PL/canonical-AK mass-compatibility corollary under renewed user authorization; no axiom or closed witness

Primary references: [source 1](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/rsplx.pdf), [source 2](https://doi.org/10.1007/BF02392711), [source 3](https://people.math.ethz.ch/~lang/Lang_LocalCurrents.pdf).

## standard-Hilbert-coordinate-regrouping

Ordinary orthogonal l2 direct-sum/Fubini regrouping; the norm-folding construction of Song §3.4.1, formula (23). These two elementary algebraic identities are a standard coordinate-sum corollary, not a separately numbered paper theorem.

Lean interfaces: `Paper28.HilbertGroupingInput`.

Scope: For arbitrary coordinate partitions, composition of the actual native lp fiber-norm maps equals regrouping by the composite partition; a constant partition gives the actual single coordinate vector with coefficient equal to the original norm. Exact identities only.

Paper-owned boundary: No group, tree, current, transfer, homology, mass inequality or volume conclusion. Native actual branch restrictions and pushforward algebra derive factor recovery.

Status: precise explicit unformalized elementary standard Hilbert regrouping parameter under renewed foundation authorization; no axiom/closed witness

Primary references: [source 1](https://arxiv.org/pdf/2202.10636v6).

## standard-injective-coordinate-geodesic-pushforward

Song §3.4.1 formula (23), specialized to an injective group homomorphism (coordinate absolute value followed by zero extension); Rourke–Sanderson §2, 2.8–2.12 common geodesic/sign-plane subdivision; canonical AK simplex pushforward/change of variables. Combined standard compatibility corollary, not a separately numbered transfer or approximation theorem.

Lean interfaces: `Paper28.InjectiveGeodesicFoldingInput`.

Scope: For each single actual proper finite-coordinate spherical simplex and an injective group homomorphism, its actual sphere-current pushforward under the canonical norm fold has an exact finite integer proper-geodesic simplex integration presentation in the target. Coordinate sign cuts turn the operation into isometric coordinate inclusions on finitely many pieces, followed by ordinary proper-chart common refinement. Integer chain assembly, quotient-square compatibility and quotient polyhedral preservation are native proofs.

Paper-owned boundary: No transfer, factor current/class recovery, approximation, filling, joint mass or free-product additivity.

Status: precise explicit unformalized standard PL/AK coordinate-monomorphism compatibility corollary; no axiom or closed witness

Primary references: [source 1](https://arxiv.org/pdf/2202.10636v6), [source 2](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/rsplx.pdf), [source 3](https://doi.org/10.1007/BF02392711).

## standard-oriented-connected-sum-topology

A. Hatcher, Algebraic Topology, Theorem 1.20 (van Kampen), printed pp.43–45; Theorem 3.26 and §3.3 (oriented fundamental classes/excision), printed pp.236–239; connected-sum construction discussed in §3.3 Exercise 6, printed p.257. The free-product and pinch-class identities are the standard n>=3 connected-sum/excision corollary, not a separately numbered spherical-volume theorem.

Lean interfaces: `Paper28.ManifoldTopologyObjectsInput; Paper28.ConnectedSumTopologyInput`.

Scope: Standard topological orientation objects (coherent integral local-homology generators), oriented connected-sum construction, and canonical classifying image of the fundamental class. The underlying closed connected Hausdorff second-countable n-manifolds have native ChartedSpace R^n structures and actual native FundamentalGroup objects. For n>=3, standard topology supplies a countable fundamental-group model with actual subgroups A,B, explicit isomorphisms to the actual three manifold fundamental groups, the exact free-product universal property, and the pinch-map identity of their canonical classifying fundamental classes.

Paper-owned boundary: No metric current, mass, spherical volume, transfer, free-product additivity or connected-sum volume identity. Corollary1.2 must apply the native Theorem1.1 to these purely topological data.

Status: precise explicit unformalized standard topology object/theorem parameters under renewed user authorization; the n>=3 hypothesis is checked natively from dimension k+4; no closed orientation/topology witness or native reconstruction of van Kampen/fundamental-class theory is claimed

Primary references: [source 1](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf).

