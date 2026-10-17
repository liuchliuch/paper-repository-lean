# External dependencies and representation boundary

This is a relative formalization. The delivery ledger records **48 disclosed universal interfaces**; no corresponding Lean instances of the external theories are supplied. Some are derived support interfaces rather than additional independent fields. The production files declare no new axiom and use no production `sorry`. `ClassicalInputs`, its curve-branch inputs and the separate averaging/sharpness inputs retain the exact mathematical hypotheses.

The exact English ledger is [external-dependencies.json](external-dependencies.json). A field is not a proved existence theorem for its witness. The main at-most-two bound, pair-specific geometry, cyclic models, common retractions, normal tensors and the third-fibration obstructions are own deductions rather than assumed input fields.

Ramification is represented by actual derivative critical support and the transverse order of the actual chart Jacobian. Self-intersection uses the degree of the actual honest normal quotient cocycle. A separate global surface divisor/intersection-pairing library is not claimed.

## E01

Interface: `Paper27.Geometry.MetricComparison.ClassicalCurveMapFacts`.

All actual compact curves D,B, all actual HolomorphicMap u:D→B with ∃p q,u p≠u q. All p: analytic finite order of deriv(writtenCoordinateMap u p); actual finite ramification support and finite fibres; surjectivity; for every finiteness witness, χD+degR(u)=mapDegree(u)χB.

Sources: [forster1981](https://www.mathematik.uni-muenchen.de/~forster/books/riem/riemsurf.html), [troyanov1991](https://sma.epfl.ch/~troyanov/Papers/Prescribing.pdf).

Own specialization: R is constructed from analyticOrderNatAt of the actual coordinate derivative; mapDegree is the sum of order+1 over the actual chosen target-point fibre. Euler characteristic is 2−2 genus, where genus is defined from H1 rank.

External formalization boundary: No external instance, surface-classification/genus identification, or general finite-zero/Riemann–Hurwitz proof is formalized.

## E02

Interface: `Paper27.Geometry.MetricComparison.ClassicalPullbackFacts`.

All actual compact curves, nonconstant actual u, finite actual R(u), and concrete ConformalMetric g with HasConeData g 0: pullback u g has cone divisor R(u); if g has curvature −1, pullback has curvature −1 off R(u).

Sources: [troyanov1991](https://sma.epfl.ch/~troyanov/Papers/Prescribing.pdf).

Own specialization: Concrete metric weights, inverse-chart differential densities, actual mfderiv pullback, and Laplacian curvature are defined; quadratic-form pullback identity is own proof.

External formalization boundary: General local degeneracy/curvature instance and the coordinate representation/intrinsic tensor bridge remain unformalized.

## E03

Interface: `Paper27.Geometry.MetricComparison.TroyanovUniqueness`.

Every actual compact curve D, finite effective R:D→₀N, concrete metrics g,h: if χD+degR<0, both have cone order R and curvature −1 off R, then g=h.

Sources: [troyanov1991](https://sma.epfl.ch/~troyanov/Papers/Prescribing.pdf).

Own specialization: Only uniqueness is imported. Own proofs establish θ=2π(m+1)>0, angle defect, negative conical Euler number, equality of actual divisors, and equal pullback metrics.

External formalization boundary: The uniqueness theorem has no Lean instance. Existence of chosen hyperbolic metrics is separately supplied by E20, and local metric charts by E21. Neither is left as an own missing graph bridge.

## E04

Interface: `Paper27.Geometry.BranchGraphs.IsometryFirstJetRigidity`.

Every z:C and actual LocalDiscIsometry a,b at z; same value and complex derivative imply equality of germs at z.

Sources: [petersen2006](https://poisson.phc.dm.unipi.it/~lmigliorini/secondo_magistrale/riemanniana/petersen.pdf).

Own specialization: Restrict to a connected common neighbourhood; density identities define actual local Riemannian isometries. Petersen Proposition 22 then supplies uniqueness.

External formalization boundary: No instance translating actual Poincare density isometries into Petersen's Riemannian formulation is formalized. The own graph-slope and continuity arguments are separate.

## E05

Interface: `Paper27.Geometry.DiscGraphExtension.LocalDiscIsometryExtension`.

Every z:C and actual LocalDiscIsometry φ at z admits an actual GlobalDiscIsometry A agreeing with φ near z.

Sources: [petersen2006](https://poisson.phc.dm.unipi.it/~lmigliorini/secondo_magistrale/riemanniana/petersen.pdf).

Own specialization: Apply Theorem 17 to the complete simply connected curvature −1 disc and the orientation-preserving linear isometry given by the first jet; Proposition 22 matches the given local germ. Complex analyticity is the standard oriented-isometry/conformal correspondence.

External formalization boundary: Completeness/model-curvature/orientation/analyticity translation is not instantiated in Lean. This parameter contains no ramified maps or branch graph conclusion.

## E06

Interface: `Paper27.Geometry.CovectorGauges.ClassicalZeroDifferentialConstancy`.

All actual compact curves D,B and actual holomorphic u:D→B: if every actual written-coordinate derivative at its chart centre is zero, u is constant.

Sources: [fernandes2024](https://doi.org/10.1142/12733).

Own specialization: The constant⇒zero converse, unit-germ comparison, constancy equivalence, and promotion of one nonconstant projection to both are own proofs.

External formalization boundary: The general chart-to-real-differential constancy instance is not formalized.

## E07

Interface: `Paper27.Geometry.CoordinateCalculus.SurfaceAnalyticRegularity`.

Exact current interface: every F:(C×C)→C and z0, (eventually z near z0, DifferentiableAt C F z) implies AnalyticAt C F z0.

Sources: [lebl44](https://www.jirka.org/scv/scv.pdf).

Own specialization: On a smaller closed polydisc, nearby complex Frechet differentiability gives continuity and coordinate-wise holomorphicity; Theorem 1.2.1 supplies a convergent power series. One-source-dimensional analyticity is already proved from mathlib's Cauchy theorem.

External formalization boundary: Only the universal SCV regularity theorem remains uninstantiated; actual one-variable and surface-coordinate applications are proved.

## E08

Interface: `Paper27.Geometry.LineBundleDegreeTheory`.

Degree operation on every actual HolomorphicLineCocycle over every actual compact curve; invariance under same transitions, tensor-power degree law, tangent degree 2−2g, holomorphic connection⇒degree zero, negative degree⇒every actual HolomorphicSection coefficient zero on its chart.

Sources: [abst2013](https://ems.press/content/serial-article-files/38428), [atiyah_weil](https://www.ams.org/journals/tran/1957-085-01/S0002-9947-1957-0086359-5/S0002-9947-1957-0086359-5.pdf), [kobayashi1987](https://www.mathsoc.jp/assets/pdf/publications/pubmsj/Vol15.pdf).

Own specialization: The degree is the unformalized first-Chern number of the bundle represented by the concrete cocycle. Connections contain actual holomorphic coefficients and the connection transformation law.

External formalization boundary: The canonical first-Chern degree operation and universal bundle/connection/section facts remain unformalized. Actual normal cocycles, tangent cocycles, tensor gauges, correction sections and the actual Bott application are now constructed in the own proof chain; do not relist them as missing.

## E09

Interface: `Paper27.Geometry.HomDegreeLaw`.

Every actual D,N,T and HomLineCocycle H whose transitions are T/N: degree(H)=degree(T)−degree(N).

Sources: [kobayashi1987](https://www.mathsoc.jp/assets/pdf/publications/pubmsj/Vol15.pdf).

Own specialization: NormalQuotient constructs H itself, its holomorphic quotient section, factorization, and transition law. The negative Hom degree and resulting covector equality are own proofs.

External formalization boundary: Standard first-Chern Hom law is explicit but not instantiated; the negative-section source is verified, while a separate numbered source for this elementary degree law is not asserted.

## E10

Interface: `Paper27.Geometry.NonconstantCompactCurveMapTheorem`.

All compact actual curves C,D and nonconstant actual holomorphic a:C→D: every fibre is finite and a is surjective.

Sources: [forster1981](https://www.mathematik.uni-muenchen.de/~forster/books/riem/riemsurf.html).

Own specialization: The finite-fibre connected-factor argument proving a bijection and the descent function are own proofs.

External formalization boundary: No independent input is required by ClassicalInputs: FibreGeometry.compactCurveMapTheorem derives this interface from ClassicalCurveMapFacts.fibres_finite/surjective.

## E11

Interface: `Paper27.Geometry.BijectiveHolomorphicInverse`.

Every equivalence e:C≃D of actual compact curves, if e is holomorphic then e.symm is holomorphic.

Sources: [forster1981](https://www.mathematik.uni-muenchen.de/~forster/books/riem/riemsurf.html).

Own specialization: Local z↦z^k form and injectivity force k=1. The interface does not assert any fibration factorization or degree-one result.

External formalization boundary: No general curve biholomorphic-inverse instance.

## E12

Interface: `Paper27.Geometry.ProductCurveRigidity`.

All actual compact curves A,B,C with C hyperbolic; every actual holomorphic F:A×B→C factors through one actual projection by a holomorphic curve map. Constants are allowed.

Sources: [catanese2000](https://www.mathe8.uni-bayreuth.de/de/team/prof-fabrizio-catanese-old/pdf/066.pdf).

Own specialization: This is the one-component consequence of Catanese's proof, not the entire Lemma 3.4.

External formalization boundary: No de Franchis/product-rigidity instance; own proof handles descent and equivalence after this input.

## E13

Interface: `Paper27.Geometry.ProductCoverExistence`.

Every actual finite unramified cover q:X→C×D has a finite unramified product cover A×B→X with actual finite covers A→C,B→D and commuting product diagram.

Sources: [hatcher2002](https://pi.math.cornell.edu/~hatcher/AT/ATch1.pdf).

Own specialization: No normality/regularity of q is required. The finite-index subgroup product inclusion is own algebra; covering classification and transported holomorphic structures supply the geometry.

External formalization boundary: No covering-space construction/complex structure transport instance.

## E14

Interface: `Paper27.Geometry.ConnectedFibreDerivativeConstancy`.

Every actual holomorphic submersion f:X→B with connected fibres and actual holomorphic h:X→C; if dh vanishes on ker df everywhere, h is constant on each fibre.

Sources: [fernandes2024](https://doi.org/10.1142/12733).

Own specialization: Apply zero-differential constancy to each connected smooth fibre. The vertical-kernel statement itself is proved from the actual covering/factorization chain rule.

External formalization boundary: The smooth fibre-submanifold and differential-restriction instance is not formalized.

## E15

Interface: `Paper27.Geometry.HolomorphicSubmersionSections`.

Every actual smooth Fibration f on an actual compact complex surface has actual holomorphic sections over sufficiently small open neighbourhoods of each base point.

Sources: [forstneric_prezelj2001](https://arxiv.org/pdf/math/0101034).

Own specialization: Take a point of a fibre and the singleton case of Proposition 1.3; no global Oka condition is introduced. Fibrewise constancy and construction/holomorphicity of descent are own proofs.

External formalization boundary: No general local-section instance. The local section structure is data; no whole fibration-factorization theorem is imported.

## E16

Interface: `Paper27.Geometry.RamificationSupport.ProperHolomorphicLocalDiffeomorphismCovering`.

Every actual holomorphic map between compact complex surfaces: proper, surjective, finite fibres, and bijective actual differential imply IsCoveringMap.

Sources: [lee2013_metadata](https://sites.math.washington.edu/~lee/Books/ISM/).

Own specialization: Holomorphic inverse-function theorem plus proper local-homeomorphism covering theorem. Properness and actual differential bijectivity from empty ramification are own proofs.

External formalization boundary: No instance; exact primary Proposition 4.46 body and chart-to-local-diffeomorphism translation remain to be registered/verified.

## E17

Interface: `Paper27.Geometry.CriticalCurveNormalizationTheorem`.

Every actual compact complex surfaces X,Y and actual finite surjective holomorphic q:X→Y admit a finite compact-curve cover whose union is exactly the actual nonsurjectivity locus of dq. Normalization curves are genuine connected compact complex curves and their actual maps have finite fibres; embeddings and projection unramifiedness are not supplied.

Sources: [dinh_sibony2008](https://arxiv.org/pdf/0810.0811).

Own specialization: The Jacobian determinant is an analytic section; a nontrivial Jacobian of a finite map cuts out a pure analytic curve or the empty set. Normalize each component; compactness and locally finite component decomposition give finitely many compact smooth curves.

External formalization boundary: The analytic-space/Jacobian-divisor normalization theorem itself and its translation to the displayed manifold data remain unformalized. The external interface does not assert any P27 smooth branch graph or Proposition 2.4.

## E18

Interface: `Paper27.Geometry.CoordinateFiniteGerms.FiniteHolomorphicGermRepresentatives`.

Every analytic germ (F,G):ℂ²→ℂ² at p with isolated actual centre fibre, every analytic φ through its target value, every prescribed open source neighbourhood V of p and positive radius bound r admit raw FiniteGermData with source⊆V and radius≤r. This includes properness, finite fibres, surjectivity onto a graph bidisc, singleton centre fibre, connected source and connected source minus the actual graph preimage. It supplies no critical-image containment.

Sources: [grauert_remmert1984](https://link.springer.com/book/10.1007/978-3-642-69582-7), [gui2022_notes](https://binguimath.github.io/Files/2022_CAG.pdf), [dinh_sibony2008](https://arxiv.org/pdf/0810.0811).

Own specialization: The ordinary finite mapping theorem gives arbitrarily small representatives; finite equal-dimensional holomorphic maps are open, allowing a small target graph bidisc and its connected source component. The inverse image of the smooth graph is a proper analytic subset; its complement is connected.

External formalization boundary: The universal finite representative construction remains uninstantiated. Published Grauert–Remmert chapter metadata is verified but its exact theorem body/number is not; author-hosted Gui Theorem 2.7.2 is body-verified. Arbitrarily small graph-bidisc/connectedness packaging is a standard consequence, not a verbatim quoted theorem. Own critical graph containment is proved separately.

## E19

Interface: `Paper27.Geometry.FiniteAnalyticGerm.SmoothBranchFiniteCoverClassification`.

Every actual analytic (F,G):ℂ²→ℂ², p and analytic smooth target graph φ, with FiniteGraphGerm data (proper finite surjective representative; connected punctured source; actual critical image contained in that graph), admit actual CyclicNormalForm F G p with exactly graph φ. Positive exponent is part of that data; n≥2 is subsequently proved from actual criticality.

Sources: [sga1](https://arxiv.org/pdf/math/0206203), [edixhoven2010](https://arxiv.org/pdf/0807.0184).

Own specialization: Connected finite covers of Δ×Δ* are classified by subgroups of ℤ; normal finite analytic extension is unique. This is general smooth branch-locus classification, not the P27 single-graph theorem.

External formalization boundary: Only the universal cover/classification theorem is unformalized. Actual same-source graph uniqueness, critical containment, actual source isolation, model validity and exponent≥2 are proved by the own chain.

## E20

Interface: `Paper27.Geometry.MetricTangency.HyperbolicMetricTheory`.

Select a concrete ConformalMetric for every actual Curve C. For genus≥2: its weights are positive, cone divisor is zero, curvature is −1. Every unramified actual map between hyperbolic compact curves preserves these metrics under the defined actual pullback. For every actual map between such curves, equality of the two squared norms on one nonzero tangent implies bijective actual differential everywhere.

Sources: [mcmullen2023](https://people.math.harvard.edu/~ctm/home/text/class/harvard/213a/23/html/home/course/course.pdf), [petersen2006](https://poisson.phc.dm.unipi.it/~lmigliorini/secondo_magistrale/riemanniana/petersen.pdf).

Own specialization: Uniformization supplies the metrics; lift maps to the unit disc and apply Schwarz–Pick equality. Covering invariance and equality are general curve-map facts.

External formalization boundary: Uniformization existence and the translation between intrinsic metrics, actual metric weights and the topological genus remain universal uninstantiated theory. McMullen Theorem 2.28 itself was body-verified; no claim of a separate verified numbered existence theorem.

## E21

Interface: `Paper27.Geometry.NormalizedBranchConstruction.UniformizingDiscCharts`.

For every actual hyperbolic curve B and every specified concrete g with HasConeData g 0 and curvature −1, every b has a genuine biholomorphic local chart into the unit disc satisfying equality of the actual quadratic forms under the actual chart differential.

Sources: [petersen2006](https://poisson.phc.dm.unipi.it/~lmigliorini/secondo_magistrale/riemanniana/petersen.pdf), [mcmullen2023](https://people.math.harvard.edu/~ctm/home/text/class/harvard/213a/23/html/home/course/course.pdf).

Own specialization: Local constant-negative-curvature developing coordinates, with orientation chosen compatibly with the complex structure, give the Poincaré density identity.

External formalization boundary: The general local Riemannian/complex chart construction is not instantiated. Choosing the two target charts and transporting the actual map/density identities is own work, now completed.

## E22

Interface: `Paper27.Geometry.FibreGeometry.SmoothProperFibreModels`.

Every actual Fibration f:X→B with proper actual map and surjective actual differential has, over every b, a genuine compact connected complex curve model, a homeomorphism to the actual fibre, and an actual holomorphic inclusion compatible with that homeomorphism. No second fibration is quantified or concluded.

Sources: [ehresmann1952](https://www.numdam.org/item/SB_1948-1951__1__153_0/), [forstneric_prezelj2001](https://arxiv.org/pdf/math/0101034).

Own specialization: Holomorphic submersion/level-set theorem gives the complex fibre; compactness, connected fibres and inherited topology give the remaining data. Ehresmann supplies the surrounding smooth-family interpretation.

External formalization boundary: The universal complex fibre-submanifold construction is not formalized; a separate exact primary numbered holomorphic level-set statement was not body-verified. Per-pair FibreCurveModel is no longer a main theorem premise.

## E23

Interface: `Paper27.Geometry.FibreGeometry.EhresmannDegreeInvariance`.

Given ClassicalCurveMapFacts, every actual smooth proper Fibration f, every actual holomorphic map g:X→C to an arbitrary compact curve, every honest family of actual fibre models and every b,b′, the two restrictions have equal curveDegree. That degree is defined as the actual multiplicity sum mapDegree for nonconstant maps and zero for constants.

Sources: [ehresmann1952](https://www.numdam.org/item/SB_1948-1951__1__153_0/), [hatcher_degree2002](https://pi.math.cornell.edu/~hatcher/AT/ATch2.pdf), [forster1981](https://www.mathematik.uni-muenchen.de/~forster/books/riem/riemsurf.html).

Own specialization: Ehresmann transport identifies fibres orientation-preservingly; restrictions vary by homotopy. Oriented topological degree equals the holomorphic local multiplicity sum. Arbitrary honest fibre parametrizations differ by holomorphic orientation-preserving identifications.

External formalization boundary: Ehresmann plus degree comparison remain a universal explicit input; there is no free degree label or per-pair degree-zero axiom. Zero-degree iff constant and the original-map finite-pair conclusion are proved.

## E24

Interface: `Paper27.Geometry.SmoothCurveDecomposition.EmbeddedSubmanifoldDecomposition`.

Every closed S in every actual compact complex surface X, locally identified with the exact coordinate axis by actual biholomorphic axis charts, is the support of a finite DisjointCurveFamily of actual embedded compact connected curves. No maps to base curves, unramifiedness, exponent or hyperbolicity are included.

Sources: [dinh_sibony2008](https://arxiv.org/pdf/0810.0811).

Own specialization: Transport the one-dimensional complex charts to the locally embedded submanifold S. Its components are open in S, and compactness gives finitely many; each is a closed embedded compact complex curve. This is ordinary submanifold construction, not a ramification theorem.

External formalization boundary: The universal manifold construction and component-to-Curve packaging are unformalized. The source analytic-submanifold discussion supports the background; no exact numbered theorem with this precise Lean statement was body-verified. Actual critical-axis charts, closedness, coverage and unramified/hyperbolic conclusions are own proofs.

## E25

Interface: `Paper27.Geometry.RetractionFactorization.NonsingularJointLocusOpen`.

Every actual pair of holomorphic maps X→B and X→C has an open locus where their actual joint differential ℂ²→ℂ² is bijective.

Sources: [lebl44](https://www.jirka.org/scv/scv.pdf).

Own specialization: In any fixed holomorphic charts, the determinant is holomorphic and nonvanishing is open; chart changes preserve nonsingularity.

External formalization boundary: The generic chart-to-bundle regularity/open-locus fact is not instantiated. It is an elementary determinant consequence, not a separately claimed numbered Lebl theorem.

## E26

Interface: `Paper27.Geometry.RamificationIndexConstancy.FiniteLocalDegreeTheory`.

A localDegree operation for every actual finite surjective holomorphic map between compact complex surfaces. In every actual biholomorphic source/target chart with actual identity (x,y)↦(x,φ(x)+y^n), n>0 and analytic φ, its value at every point of the actual coordinate axis is n. No component constancy is a field.

Sources: [dinh_sibony2008](https://arxiv.org/pdf/0810.0811).

Own specialization: Local topological degree is invariant under biholomorphic coordinates; the transverse map y↦y^n has n nearby preimages counted positively.

External formalization boundary: The canonical general local topological degree and coordinate comparison are unformalized. Constancy on the actual connected component and agreement of all chart exponents are proved.

## E27

Interface: `Paper27.Geometry.RetractionFactorization.CompactUnramifiedCurveCovering`.

Every actual holomorphic map between compact actual curves with bijective actual differential everywhere is IsCoveringMap.

Sources: [forster1981](https://www.mathematik.uni-muenchen.de/~forster/books/riem/riemsurf.html), [lee2013_metadata](https://sites.math.washington.edu/~lee/Books/ISM/).

Own specialization: Holomorphic inverse-function theorem gives a local homeomorphism; compactness makes it proper, hence a covering. The image is open and closed in the connected target.

External formalization boundary: The generic covering interpretation is uninstantiated. Lee Proposition 4.46 remains a proposed anchor whose original body was not independently read; this uncertainty is bibliographic, not a per-pair retraction assumption.

## E28

Interface: `Paper27.Geometry.RetractionFactorization.TopologicalCoverNeighbourhoodLifting`.

Every actual embedded compact curve D⊂X, every actual covering a:D→B and actual holomorphic f:X→B with a=f∘ι admit a continuous covering lift r on some actual open neighbourhood of D, with r∘ι=id and a∘r=f there. The conclusion contains no holomorphicity, cyclic chart, action or degree assertion.

Sources: [hatcher2002](https://pi.math.cornell.edu/~hatcher/AT/ATch1.pdf), [lee2013_metadata](https://sites.math.washington.edu/~lee/Books/ISM/).

Own specialization: A smooth tubular neighbourhood deformation retracts onto D. The covering lift criterion/homotopy lifting extends the specified lift id on D.

External formalization boundary: General tubular-neighbourhood lifting is an explicit unformalized theorem consequence. Hatcher Proposition 1.33 is body-verified; an exact independent primary tubular-neighbourhood theorem number is not claimed verified. Holomorphicity and actual factored retractions are constructed separately.

## E29

Interface: `Paper27.Geometry.RetractionFactorization.HolomorphicEtaleLiftRegularity`.

Every actual unramified holomorphic curve map a:C→B, every actual holomorphic f:X→B, every open V and continuous lift r:V→C with a∘r=f has holomorphic r on V.

Sources: [forster1981](https://www.mathematik.uni-muenchen.de/~forster/books/riem/riemsurf.html).

Own specialization: Locally r is the holomorphic local inverse of a composed with f; continuity chooses the sheet.

External formalization boundary: The general local étale-inverse regularity theorem is not instantiated. It does not choose the lift, a normal atlas, or an action.

## E30

Interface: `Paper27.Geometry.RetractionNormalCoordinates.AnalyticDividedDifferences`.

Every scalar f analytic at a has an analytic two-variable divided difference (x,y)↦dslope f x (x+y) at (a,0), including the diagonal.

Sources: [lebl44](https://www.jirka.org/scv/scv.pdf).

Own specialization: Expand the convergent power series and divide f(x+y)−f(x) by y termwise; the diagonal value is f′(x). This is an ordinary analytic consequence.

External formalization boundary: The general analytic divided-difference lemma is explicit and not instantiated. The specific coordinate straightening and resulting retraction chart are own proofs. No separate numbered divided-difference source is asserted.

## E31

Interface: `Paper27.Geometry.RetractionNormalCoordinates.AnalyticUnitRoots`.

Every analytic F:ℂ²→ℂ with F(p)≠0 and every positive n have an analytic nonzero local n-th root ρ with ρ^n=F as an actual germ at p.

Sources: [lebl44](https://www.jirka.org/scv/scv.pdf).

Own specialization: Choose c with c^n=F(p), shrink so F/F(p) is near 1, and set ρ=c·exp(log(F/F(p))/n) using a local analytic logarithm. This is the ordinary local-unit root theorem.

External formalization boundary: The universal local root instance is not supplied. It neither chooses global roots on canonical curve chart domains nor assumes a P27 normal form. A precise independent numbered local-root anchor is not claimed verified.

## E32

Interface: `Paper27.Geometry.NormalAtlasAction.HolomorphicNormalDivision`.

Every analytic F:ℂ²→ℂ at p with p₂=0 and F(x,0)=0 near p₁ has an analytic h at p with F=y·h as a germ.

Sources: [lebl44](https://www.jirka.org/scv/scv.pdf).

Own specialization: The convergent two-variable power series has no y-degree-zero term, so it factors by y.

External formalization boundary: Only the generic analytic division operation is uninstantiated. The nth-power cancellation, finite-root rotation uniqueness and compatibility are own proofs; whole cyclic action is not external.

## E33

Interface: `Paper27.Geometry.NormalAtlasAction.HolomorphicOpenGermGluing`.

Arbitrary actual local holomorphic open maps X→X on open domains covering an embedded compact curve D, with pairwise equal actual germs at all overlap points of D, have an actual holomorphic open-map representative on some neighbourhood of D agreeing with every specified germ. No group/retraction/index appears.

Sources: [stacks_gluing](https://stacks.math.columbia.edu/tag/00AK).

Own specialization: The sheaf of holomorphic maps glues compatible representatives; compactness and shrinking make germs into representatives along the compact closed set. Local openness is retained because it is local.

External formalization boundary: The generic compact-germ representative/sheaf theorem is unformalized. Stacks supports ordinary sheaf gluing, not verbatim this compact shrinking statement. All action identities, finite invariant shrinking, faithfulness and generator order are own deductions.

## E34

Interface: `Paper27.Geometry.ThreePairNormalObstruction.NormalFrameExistence`.

For every actual embedded compact complex curve D⊂X, there are actual holomorphic normal and tangent line cocycles N,T and RawEmbeddedFrames adapted to actual dι and actual tangent-chart differentials. Frames are holomorphic in actual ambient tangent charts and their normal transition is the actual quotient transition. No retraction or exponent occurs.

Sources: [forstneric2018](https://users.fmf.uni-lj.si/forstneric/papers/2018PAMS.pdf).

Own specialization: On each canonical curve chart domain, an open Riemann surface, normal bundles are holomorphically trivial and the tangent/normal sequence splits holomorphically by Stein theory. Choose the actual tangent-normal frames and construct the normal/tangent cocycles.

External formalization boundary: The universal Oka–Grauert/Cartan-B frame construction remains unformalized. The raw frame type is honest actual tangent data, not NormalizedCovectors existence, a β-section, a tensor identity or negative degree.

## E35

Interface: `Paper27.Geometry.EmbeddedFrames.HolomorphicFrameCalculus`.

For every actual embedding D⊂X, every honest RawEmbeddedFrames, every actual holomorphic u:X→B with unramified actual restriction u|D, every frame index i and vector v, the coefficient of ci_i∘d(u|D)^{-1}∘du∘frame_i applied to v is holomorphic on the canonical chart domain.

Sources: [forstneric2018](https://users.fmf.uni-lj.si/forstneric/papers/2018PAMS.pdf), [lebl44](https://www.jirka.org/scv/scv.pdf).

Own specialization: Differentiation of holomorphic maps, composition of holomorphic bundle maps and inversion of an invertible line-bundle map preserve holomorphicity.

External formalization boundary: The general coefficient-regularity instance is unformalized. Tangent normalization, actual overlap law, constructed β, vanishing and actual kernel/tangency conclusion are all own proofs.

## E36

Interface: `Paper27.Geometry.NormalDegreeInvariance.LineBundleDegreeGaugeInvariance`.

For every actual compact curve C, actual holomorphic line cocycles L,K and explicit nowhere-zero holomorphic gauge with its actual overlap compatibility, degree(C,L)=degree(C,K). No embedding, fibration, exponent or sign appears.

Sources: [kobayashi1987](https://www.mathsoc.jp/assets/pdf/publications/pubmsj/Vol15.pdf).

Own specialization: The gauge is a holomorphic line-bundle isomorphism and first-Chern degree is isomorphism invariant.

External formalization boundary: The universal degree-isomorphism theorem remains uninstantiated. Actual normal tensor gauge and common-index cancellation are constructed. A separate exact numbered primary gauge-degree theorem is not claimed body-verified.

## E37

Interface: `Paper27.Geometry.NeighbourhoodSplittings.HolomorphicSplittingCalculus`.

For every actual retraction r and actual globally holomorphic h with actual joint differential bijective throughout U, the actual inverse joint differential applied to (w,0) is a holomorphic bundle section. For every actual neighbourhood action preserving r, differential pushforward of an actual holomorphic section remains holomorphic.

Sources: [lebl44](https://www.jirka.org/scv/scv.pdf), [forstneric2018](https://users.fmf.uni-lj.si/forstneric/papers/2018PAMS.pdf).

Own specialization: Inverse matrices and derivatives of holomorphic bundle maps are holomorphic in local charts; pushforward is their composition at the actual inverse point.

External formalization boundary: Only universal regularity is supplied; Section, projection, differential representation, averaging, splitting preservation, normal tangency and actual line subbundle are own constructions. No free module/Leaf or degree-zero-from-average input is used.

## E38

Interface: `Paper27.Geometry.NeighbourhoodSplittings.BottTangentialSubbundleDegreeZero`.

Every actual compact embedded curve D, actual neighbourhood/retraction r, honest actual normal frames N, and actual holomorphic injective line-bundle map r*TD→TX whose image along D equals actual dι(TD), have degree(N)=0. No averaging, arbitrary Leaf, group action or negative degree appears.

Sources: [abst2013](https://ems.press/content/serial-article-files/38428).

Own specialization: ABST Theorem 7.1 gives the tangential normal partial connection; Corollary 7.3 gives Chern vanishing for compact Kähler D. Every compact complex curve is Kähler. Integrability need not be separately imposed for this implication.

External formalization boundary: The general Bott/Atiyah and cocycle-to-first-Chern interpretation remain explicit unformalized theory. Actual subbundle/tangent equality is constructed before application, so Lemma 2.2 is a required disclosed dependency, not an automatic whole-step exemption.

## E39

Interface: `Paper27.Geometry.TaylorGerms.TaylorCalculus`.

An ordinary finite jet operation d,f↦J.jet d f∈ℂ[X], bounded by d, invariant under equality of actual germs, with constant/first/second coefficients for analytic f, exact polynomial truncation, addition, multiplication/powers/composition modulo X^(d+1), and leading monomial-factor coefficient. Quantified only over scalar functions/polynomials/degrees.

Sources: [lebl44](https://www.jirka.org/scv/scv.pdf).

Own specialization: Convergent Taylor series truncated to degree d have these universal ring/substitution laws. The operation can be extended to nonanalytic functions without using them in analytic claims.

External formalization boundary: The universal jet operation/laws have no Lean instance. Actual normal/retraction germs, full intermediate terms, equation (7), connection cocycle and degree contradiction are own proofs, not fields of J.

## E40

Interface: `Paper27.Geometry.RetractionCoefficientHolomorphic.ParametricTaylorCalculus`.

Given TaylorCalculus J: general SurfaceAnalyticRegularity and, for every open V⊂ℂ², every analytic F near V, every d,k and every (x,0)∈V, analyticity in t near x of coeff_k(J.jet d (z↦F(t,z))).

Sources: [lebl44](https://www.jirka.org/scv/scv.pdf).

Own specialization: The locally convergent multivariable power series has holomorphic parameter coefficients; the Cauchy coefficient formula yields the same statement.

External formalization boundary: The generic parameter-Taylor instance is unformalized. Own code constructs actual centred coordinate functions, chart-choice independence, global leading coefficient, compact constancy and connection data.

## E41

Interface: `Paper27.Geometry.HolomorphicEmbeddedFactorization`.

Every two actual embedded compact curves D,E⊂X with D.support⊆E.support have an actual holomorphic factor map a:D→E with ιE∘a=ιD.

Sources: [forster1981](https://www.mathematik.uni-muenchen.de/~forster/books/riem/riemsurf.html).

Own specialization: Locally an embedded complex submanifold has holomorphic inverse coordinate charts; maps whose image lies in it factor holomorphically.

External formalization boundary: Known generic submanifold calculus remains explicit in these supporting results; it is NOT a field or premise of the current main theorem, which uses actual tangency and common retractions directly. No exact numbered primary statement was body-verified.

## E42

Interface: `Paper27.Geometry.NormalDegreeInvariance.HolomorphicMixedFrameCalculus`.

For every actual embedding and two honest RawEmbeddedFrames, each scalar normal coordinate of the actual mixed-frame map B_i^{-1}∘A_i applied to v is holomorphic on the canonical chart domain.

Sources: [forstneric2018](https://users.fmf.uni-lj.si/forstneric/papers/2018PAMS.pdf), [lebl44](https://www.jirka.org/scv/scv.pdf).

Own specialization: Inversion and composition of actual holomorphic frames preserve holomorphicity.

External formalization boundary: Optional mixed-frame regularity is explicit; current main proof chooses one honest frame and uses three_exponents_equal_common_frames, so this is not a main record field.

## E43

Interface: `Paper27.Geometry.MeromorphicSplittingAverage.LaurentCalculus`.

A linear Laurent-coefficient operation on all scalar functions (arbitrary linear extension outside meromorphic germs), invariant under equality on a punctured germ; exact monomial, lower-order/leading analytic-factor, rotation laws for meromorphic functions and nonzero scalar; no negative coefficients implies an analytic punctured-germ extension whose value is coefficient zero.

Sources: [lebl44](https://www.jirka.org/scv/scv.pdf), [popescu2011](https://math.univ-lille1.fr/~popescu/2011-Jung-resol.pdf).

Own specialization: Ordinary scalar Laurent theory; use linear extension from the subspace of meromorphic germs for the all-functions operation.

External formalization boundary: Universal scalar Laurent extraction/removal is uninstantiated. The actual quotient −r_x/r_y, pole order, leading coefficient, finite root-of-unity cancellation and formula (6) are own deductions. The main at-most-two proof independently uses the Appendix path. The full original-map formula-(6) path is now constructed via AveragingInputs; no pair-specific section/action/leading-coefficient assumptions remain.

## E44

Interface: `Paper27.Geometry.PuncturedSplittingSections.HolomorphicPuncturedCalculus`.

On every actual punctured neighbourhood U\D, inverse actual joint retraction differential defines a holomorphic actual section; for every actual action fixing D, its actual derivative pushforward preserves holomorphicity.

Sources: [lebl44](https://www.jirka.org/scv/scv.pdf), [forstneric2018](https://users.fmf.uni-lj.si/forstneric/papers/2018PAMS.pdf).

Own specialization: Local holomorphic matrix inversion and bundle-map composition on the actual open punctured domain.

External formalization boundary: Only generic regularity is unformalized. Actual Point/Section types, restricted permutation, inverse joint map, pushforward representation and finite global formula (6) are own definitions/proofs.

## E45

Interface: `Paper27.Geometry.PuncturedSplittingSections.LaurentSectionExtension`.

For every actual retraction r, ordinary adapted coordinates C (no second retraction or exponent), and actual holomorphic punctured bundle section σ, if both actual scalar coefficients on every normal slice are meromorphic with all negative Laurent coefficients zero, there is an actual holomorphic section on U restricting to σ, with the stated constant-coefficient values along D.

Sources: [lebl44](https://www.jirka.org/scv/scv.pdf), [popescu2011](https://math.univ-lille1.fr/~popescu/2011-Jung-resol.pdf), [stacks_gluing](https://stacks.math.columbia.edu/tag/00AK).

Own specialization: Use parameter-dependent Laurent/Cauchy coefficients in fixed adapted charts: pointwise vanishing of the negative coefficients gives joint holomorphic removal across the smooth hypersurface; compatible local extensions glue uniquely. This is a universal analytic extension theorem, not pole cancellation.

External formalization boundary: The universal parametric Laurent removal and actual bundle sheaf gluing instance is not formalized. A primary exact theorem with the full slice-to-bundle statement has NOT been independently body-verified; the cited scalar bounded-removal/gluing theorems are ingredients, not verbatim the full interface. Actual nonpositive-coefficient cancellation and chart compatibility remain own work.

## E46

Interface: `Paper27.Geometry.KodairaBaseHyperbolicity`.

For every actual compact complex surface X and actual Fibration f, actual Smooth f and actual NonIsotrivial f imply genus(base f)≥2. NonIsotrivial means there exist two actual compact fibre models not biholomorphic; hyperbolicity is not part of the definition.

Sources: [catanese_rollenske2009](https://arxiv.org/pdf/math/0611428), [llosa_py2021](https://arxiv.org/pdf/2001.03694).

Own specialization: The standard period-map argument excludes base P¹ or elliptic curve; Liouville/compactness makes the period map constant, and Torelli contradicts varying actual fibres.

External formalization boundary: The universal base-hyperbolicity theorem and its translation to actual fibre models have no Lean instance. Actual Corollary 1.2 is derived from this separate background theorem and the own at-most-two bound.

## E47

Interface: `Paper27.Geometry.DoubleKodairaExistence`.

There exist an actual compact complex surface X and two actual KodairaFibration X, each smooth and nonisotrivial in the actual fibre-model sense, inequivalent under a biholomorphic change of base alone. No upper bound or exactly-two conclusion is included.

Sources: [catanese_rollenske2009](https://arxiv.org/pdf/math/0611428).

Own specialization: The published double Kodaira examples supply the surface and two distinct smooth varying fibrations; own upper-bound reasoning supplies exact sharpness.

External formalization boundary: The example surface/construction is not recreated in Lean. Its existential input is explicit. The deduction of exactly two actual classes and product_exactly_two are own theorems.

## E48

Interface: `Paper27.Geometry.CheckingBothProjections.ZaalIntermediateConstruction`.

Existence of actual compact curves C3,F,B and compact complex surface X, actual nonconstant π:F→C3 with genera 9 and 3 and actual multiplicity-sum degree 2, an actual surjective unramified b:B→F, an actual holomorphic secondProjection:X→C3 and actual local double-cover coordinate charts along π∘b at every t∈B. No ramification-degree-eight or nonsubmersion conclusion is a field. The original possibly reducible B is replaced by one connected component with no degree64 assertion.

Sources: [zaal1995](https://pure.uva.nl/ws/files/3875454/1106_11965y.pdf).

Own specialization: Zaal printed pp.186–187 constructs the translated fibre-product genus-nine curve, its two degree-two projections, étale squaring-Picard base change and local squared-line-bundle double cover branched on the two graphs. Choosing a connected component gives the displayed minimal raw data.

External formalization boundary: The concrete historical algebraic construction is not reconstructed in Lean; its minimal actual-map existence is an explicit published input. The own theorem proves second-projection failure for an actual HolomorphicMap, without presuming unverified connected fibres of that projection. The later genus-three family is outside this diagnostic input.

## Source qualifications

Dinh–Sibony printed pp.115–118 correspond to zero-based PDF pages114–117. In particular normalization A.1.4/ExampleA.1.5 is printed117 and connected-complement ExerciseA.1.4 printed118.

Grauert–Remmert published chapter metadata is body-unverified; Gui gives a precise verified primary exposition. Do not promote metadata to a checked theorem statement.

Forstnerič2018 p2987 directly verifies open-surface bundle triviality. Cartan-B splitting and exact-sequence packaging are standard additional theorem consequences; no invented numbered anchor.

Lee Proposition4.46 and an exact tubular-neighbourhood numbered body remain unverified. Hatcher covering lift criterion is verified.

General LaurentSectionExtension is a parametric Laurent-removal+sheaf consequence. Scalar removable theorem alone does not verbatim supply the full bundle statement.

Kodaira actual fibre-model variation matches the nonisotrivial family meaning; hyperbolic base is a separate external theorem, not a definition field.

Zaal total B is possibly reducible and total degree64 must not be silently assigned to a connected component.

Proposition 2.4 is represented by actual critical support, all actual cyclic-chart Jacobian orders and honest normal cocycle degree. A global surface-Divisor/intersection pairing API is not separately implemented; do not claim that such a library was built.
