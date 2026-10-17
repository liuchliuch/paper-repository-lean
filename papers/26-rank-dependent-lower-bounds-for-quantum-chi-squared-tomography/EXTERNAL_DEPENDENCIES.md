# External mathematical inputs

The final delivery records **34 registrations, 29 source records and 31 actual primary Lean interfaces**. Three registrations are background or regular-case records. The production theorem statements retain explicit propositions or structures; the corresponding external witnesses are not constructed in this project. No paper-owned theorem is supplied by a new axiom or a production `sorry`.

The exact English registry is [external-inputs.json](external-inputs.json). It retains original hypotheses and quantifiers, exact Lean interface declarations, the source-to-interface specialization, missing formalization and scope qualifications. Historical source matching is separate from fresh Lean or Comparator validation.

## P26-EXT-SOBOLEV-SHARP

For n≥3, the critical exponent is 2n/(n−2). The p=2 sharp squared constant is S_n = [π n(n−2)]⁻¹ [Γ(n)/Γ(n/2)]^(2/n): ||u||_(2n/(n−2))² ≤ S_n ∫|∇u|².

Interface: `Paper26.H1PosteriorBound.TalentiH1SharpInput`. The witness remains external.

Sources: [TALENTI1976](https://math.jhu.edu/~js/Math646/talenti.sobolev.pdf), [MEYERS_SERRIN1964](https://www.pnas.org/content/pnas/51/6/1055.full.pdf).

Missing formalization: No identified local closed theorem with the required dimension-uniform 4/n coefficient and H¹ domain. Existing FisherVolume provides a C¹ theorem with a library constant and does not discharge this input.

## P26-EXT-SOBOLEV-COARSE

Analytic specialization of the stated sharp constant: for every integer n≥3, S_n≤4/n. This is a scalar Gamma/factorial inequality, not a loss/concentration theorem and not the verbatim statement of Talenti’s theorem.

Interface: `Paper26.H1PosteriorBound.TalentiCoarseInput`. The witness remains external.

Sources: [TALENTI1976](https://math.jhu.edu/~js/Math646/talenti.sobolev.pdf).

Missing formalization: Scalar specialization not yet formalized locally; exposed as an exact independent proposition parameter rather than attributed verbatim to the source.

## P26-EXT-POSTERIOR-REGULAR

For the joint density π(θ)ℓ_θ(y), the parameter score is the sum of prior and likelihood scores; its expected squared norm is I(π)+E_π Tr F_θ. Bayes normalization is independent of θ, so this is also the mean posterior information when regular posterior scores exist.

Sources: [GILL_LEVIT1995](https://dspace.library.uu.nl/bitstream/handle/1874/1190/van_trees.pdf?isAllowed=y&sequence=1).

Missing formalization: No generic regular-score framework witness is built here. A verbatim primary theorem with every weak P26 hypothesis was not found; the actual local regular weak-H1 extension now replaces the need to cite the whole information identity as external.

## P26-EXT-GRASSMANN-CHART

On complex Grassmann rank-r projectors in C^(r+s), the full graph chart X∈C^(s×r) has Haar probability density [V_sr det(I+X*X)^(r+s)]^(-1) relative to Cartesian complex Lebesgue, V_sr=π^(sr)∏_(j<r)j!/(s+j)!. The corresponding saturated Haar-frame projector-image event has that integral for every measurable X-set.

Interface: `Paper26.ChartVolume.GraphChartInput.image_density`. The witness remains external.

Sources: [DKM2018](https://pure.mpg.de/rest/items/item_3023275_2/component/file_3070922/content?download=true), [FK2006](https://arxiv.org/pdf/math-ph/0610045v2).

Missing formalization: The exact Haar projector chart density witness is not constructed locally; its explicit actual-event field is retained as the known generic input.

## P26-EXT-HAAR-TRUNCATION

For all1≤r≤s and every invariant probability on actual (r+s)×r orthonormal complex frames, the bottom s×r block has law V⁻¹ times Cartesian Lebesgue measure restricted to {Z:I−Z*Z>0}, where V=π^(sr)∏_(j<r)j!/(s+j)!.

Interface: `Paper26.HaarTruncation.TruncatedHaarInput.bottom_law`. The witness remains external.

Sources: [FK2006](https://arxiv.org/pdf/math-ph/0610045v2), [DKM2018](https://pure.mpg.de/rest/items/item_3023275_2/component/file_3070922/content?download=true).

Missing formalization: No identified local formal Haar push-forward theorem for rectangular matrix corners.

## P26-EXT-BRUNN-MINKOWSKI

For 0<λ<1 and nonempty bounded measurable K,L⊆R^n with measurable Minkowski combination, vol((1−λ)K+λL)^(1/n) ≥ (1−λ)vol(K)^(1/n)+λ vol(L)^(1/n).

Interface: `Paper26.TailVolume.BrunnMinkowskiInput.compact_sets`. The witness remains external.

Sources: [GARDNER2002](https://www.ceremade.dauphine.fr/~carlier/Brunn-Minkowski).

Missing formalization: No Brunn–Minkowski theorem was identified in the pinned local mathlib search.

## P26-EXT-LYAPUNOV-POSITIVITY

For complex C, equation C*X+XC+Q=0 has a unique solution if every eigenvalue of C is in the open left half-plane; this solution is X=∫_0^∞ exp(C*t) Q exp(Ct)dt. If Q is Hermitian positive semidefinite, the solution is positive semidefinite.

Interface: `Paper26.TailConvexity.LyapunovPositivityInput.solution_psd`. The witness remains external.

Sources: [POLONI2020](https://pages.di.unipi.it/fpoloni/publications/files2/Pol20_doubling_review_submitted.pdf).

Missing formalization: The exact generic complex equation-positivity theorem is an explicit structure field; its witness is not constructed in local Lean. The cited integral formula and positivity corollary remain unformalized.

## P26-EXT-UNITARY-LEBESGUE

For every n≥1, orthogonal real linear map Q:R^n→R^n and arbitrary set E⊆R^n, Lebesgue outer measure satisfies L^n(Q(E))=L^n(E). The source states this for all subsets, not only measurable ones.

Interface: `Paper26.TailVolume.UnitaryLebesgueInput.image_measure`. The witness remains external.

Sources: [SIMON2018](https://math.stanford.edu/~lms/ntu-gmt-text.pdf).

Missing formalization: The local Lean file exposes the measure-invariance theorem as an explicit structure field; the coordinate orthogonal-map witness/measure-preserving proof is not constructed here.

## P26-EXT-NZ-FISHER

For ρ_X=P_graph(X)/r and m=d−r, Section 4.2.1 gives single-copy trace bound 4m/r at X=0; Section 4.2.3 transports it to every X by a Frobenius contraction. Lemma 4.6 gives I_transcript(X)=E_X∑_i I_i(H_i;X). Section 3.4 gives measured≤SLD Fisher and tensor-product additivity.

Sources: [NZ2026](https://arxiv.org/html/2609.10514v1).

Missing formalization: POVM outcome distributions, classical/quantum Fisher matrices, tensor families and adaptive transcript kernels are not implemented locally.

## P26-EXT-NZ-PRIOR

There exists one universal C>0 such that for all d≥2,1≤r<d,a>0, writing m=d−r,p=2rm, a nonnegative C∞ compactly supported real root ψ on C^(m×r) has support compactly inside ||X||op<a, integralψ²=1, and 4 integral||Dψ||²≤C*p*d/a².

Interface: `Paper26.GraphPrior.NZSmoothLocalPriorInput.local_prior`. The witness remains external.

Sources: [NZ2026](https://arxiv.org/html/2609.10514v1).

Missing formalization: The known NZ smooth-root existence theorem has no locally constructed Lean witness. Its raw bound is retained exactly, with local smooth-to-weak and matrix-coordinate bridges proved separately.

## P26-EXT-HAAR-MOMENTS

For a uniformly distributed complex unit vector u in dimension d≥1, the expectation of (|u><u|)^tensor n equals P_sym/D_n, where D_n=binomial(n+d−1,n). This is the operator identity of Harrow Proposition6 Eq7, hence also an equality of every complex matrix entry.

Interface: `Paper26.PureCovariant.HaarTensorMomentInput.moment`. The witness remains external.

Sources: [HARROW2013](https://arxiv.org/pdf/1308.6595).

Missing formalization: The exact generic Haar tensor moment has no local Lean witness. Its explicit entrywise field is retained; the actual normalized covariant measurement and the listed moment consequences are now locally proved relative to it and the separately named symmetric-space input.

## P26-EXT-OW-FROBENIUS

For every complex dimension d≥1 and n≥1, the single Keyl/Schur–Weyl measurement with normalized output U diag(λ/n) U* satisfies expected squared Frobenius error ≤(4d−3)/n for every input density matrix. The experiment is chosen before the input state.

Interface: `Paper26.FrobeniusLearning.OWFrobeniusInput.experiment`. The witness remains external.

Sources: [OW2016](https://www.cs.utexas.edu/~wright/papers/tomography.pdf).

Missing formalization: No local Lean witness of the original Schur–Weyl/Keyl measurement or its expected Frobenius theorem is constructed. The existing actual Learner-valued supporting theorem input remains explicit; downstream P26 calculations are local.

## P26-EXT-MATRIX-BERNSTEIN

Independent centered complex Hermitian d×d summands with λmax(X_i)≤L a.s. satisfy P{λmax(ΣX_i)≥t}≤d exp(−t²/[2(σ²+Lt/3)]), σ²=‖ΣEX_i²‖₂.

Interface: `Paper26.OneCopySubmatrix.MatrixBernsteinInput.upperTail`. The witness remains external.

Sources: [TROPP2012](https://arxiv.org/pdf/1004.4389v7).

Missing formalization: No local Lean witness of Tropp’s noncommutative concentration theorem or its generic monotone-variance specialization is constructed. The actual named raw upper-tail proposition stays explicit.

## P26-EXT-FO-PRIOR-RATES

Theorem 1.6 transforms a Frobenius-rate f(d,r)/N estimator into a Bures chi-squared estimator with tilde-O(sqrt(rd)*f/epsilon) copies; Corollaries 1.7 and 1.9 give the collective and adaptive one-copy rates cited by P26.

Sources: [FO2024](https://arxiv.org/pdf/2305.18519v2).

Missing formalization: Prior complete tomography construction is not formalized here.

## P26-EXT-EUCLIDEAN-BALL

For a real inner product space of dimension2q>0 with its Euclidean volume, vol(closedBall(0,R))=(ofReal R)^(2q)*ofReal(π^q/q!). For squared radius T≥0 this is ofReal(π^q*T^q/q!).

Interface: `Paper26.ScalarTailBall.EuclideanBallVolumeInput.squared_ball`. The witness remains external.

Sources: [MATHLIB_BALLS](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean).

Missing formalization: The general library theorem is proved; its exact Frobenius-coordinate specialization is retained as an explicit field, without a locally constructed witness.

## P26-EXT-POSITIVE-ROW-SCALING

Lebesgue outer measure of L(E) is |det_R L| times that of E for every real invertible linear map and arbitrary subset E. For Zij↦c_i Zij with c_i>0, det_R=∏i∏j c_i².

Interface: `Paper26.RightTailVolume.PositiveRowScalingInput.image_measure`. The witness remains external.

Sources: [SIMON2018](https://math.stanford.edu/~lms/ntu-gmt-text.pdf), [MATHLIB_LINEAR_VOLUME](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean).

Missing formalization: Real-coordinate determinant specialization and all-set image formula witness remain unformalized; the generic determinant theorem already exists.

## P26-EXT-BURES-METRIC

For all complex density matrices, root fidelity F=Tr sqrt(sqrtρ σ sqrtρ) is in[0,1]. Bures distance b=sqrt(2−2F) is a symmetric metric and b²≤Bures chi-squared divergence.

Interface: `Paper26.TailMass.BuresMetricInput`. The witness remains external.

Sources: [WATROUS2018](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf), [FO2024](https://arxiv.org/pdf/2305.18519v2).

Missing formalization: No local witness of the generic Bures metric/chi-squared comparison structure; the cited standard matrix facts remain explicit external inputs.

## P26-EXT-RAW-COMPRESSION

For a Hermitian PSD operatorσ and a rank-r orthogonal projectorP, an orthonormal eigenbasis U of rangeP gives U*U=I,UU*=P,U*σU=diagλ with λ≥0 decreasing. Cauchy/min-max bounds each sorted compressed eigenvalue by the corresponding leading ambient eigenvalue. Hence λ_i(P)≤λ_i(Q) for every leading-r spectral projectorQ, including degenerate choices.

Interface: `Paper26.TailMassBridges.RawCompressionInput`. The witness remains external.

Sources: [MATHLIB_SPECTRAL](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/InnerProductSpace/Spectrum.lean), [TROPP_MATRIX2022](https://tropp.caltech.edu/notes/Tro22-Matrix-Analysis-LN.pdf).

Missing formalization: The assembled actual compression basis/min-max witness is not constructed locally; the spectral part exists in mathlib, while no local min-max theorem was identified.

## P26-EXT-OPERATOR-RN

Every normalized PSD finite matrix-valued countably additive measure has a measurable PSD-a.e. matrix density E with integrable entries relative to finiteν(S)=ReTrP(S), and P(S)=∫_S E dν entrywise.

Interface: `Paper26.CollectiveModel.OperatorRadonNikodymInput.representation`. The witness remains external.

Sources: [MATHLIB_SCALAR_RN](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/MeasureTheory/VectorMeasure/Decomposition/RadonNikodym.lean), [MPR2020](https://roam.macewan.ca/server/api/core/bitstreams/5c14245e-d141-415a-b141-9d99c3dc56be/content).

Missing formalization: The generic finite matrix RN existence witness remains unformalized. OperatorPOVMTransport and AdaptiveOperatorModelTransport now natively prove actual representing-density Born/output/success law transport, measurable operator sections, ordinary fixed-product-space RN reuse and common-ae repair; none of these native bridges is a new external field.

## P26-EXT-HAAR-PROPER-SUBSPACE-NULL

A Haar unitary obtained by Gram–Schmidt from a complex Ginibre matrix has first column g/||g||. Since g has a Cartesian Gaussian density, every fixed proper complex linear subspace has probability0. The same holds for any fixed column of its Haar-frame truncation.

Interface: `Paper26.HaarTruncation.ProperSubspaceNullInput.null_containment`. The witness remains external.

Sources: [MEZZADRI2007](https://arxiv.org/pdf/math-ph/0609050v2), [FK2006](https://arxiv.org/pdf/math-ph/0610045v2).

Missing formalization: The exact invariant-frame/normalized-Gaussian law and generic subspace-null witness are not constructed locally.

## P26-EXT-WEAK-DERIVATIVE-UNIQUENESS

If h and k are weakly differentiable functions whose roots agree almost everywhere, their weak derivatives agree almost everywhere. This holds on every open Euclidean domain, in particular R^p.

Interface: `Paper26.WeakPosteriorIdentity.WeakDerivativeUniquenessInput`. The witness remains external.

Sources: [HAJLASZ_CORTONA](https://sites.pitt.edu/~hajlasz/Notatki/Cortona%20Lectures.pdf).

Missing formalization: The generic classical theorem has no locally constructed Lean witness. Only the explicitly parameterized local deduction is proved.

## P26-EXT-WEAK-LOCALLY-LIPSCHITZ-PRODUCT

For compactly supported h in H1(R^p) and locally Lipschitz g:R^p→R, hg is compactly supported H1 and D(hg)=gDh+hDg a.e.; Dg equals its classical Frechet derivative a.e. Representatives may be chosen to realize the displayed root and derivative everywhere.

Interface: `Paper26.WeakPosteriorIdentity.WeakLocallyLipschitzProductInput`. The witness remains external.

Sources: [HAJLASZ_CORTONA](https://sites.pitt.edu/~hajlasz/Notatki/Cortona%20Lectures.pdf).

Missing formalization: The generic classical theorem has no locally constructed Lean witness. Only the explicitly parameterized local deduction is proved.

## P26-EXT-SYMMETRIC-SUBSPACE

The average of tensor-copy permutation operators is the orthogonal projector onto all permutation-fixed vectors in (C^d)^tensor n. Its rank is binomial(n+d−1,n), obtained from the orthonormal occupation-number basis.

Interface: `Paper26.SymmetricSupport.SymmetricProjectorInput`. The witness remains external.

Sources: [HARROW2013](https://arxiv.org/pdf/1308.6595).

Missing formalization: No actual projector witness with the stated range/rank is assembled locally; these are exact generic symmetric-tensor-space data.

## P26-EXT-GRAPH-TANGENT

For every complex rectangular X, the graph state is U_X ρ_0 U_X*, and U_X* D_Hρ_X U_X = D_(L_X H)ρ_0, where U_X=[V_X,W_X] is unitary and L_X(H)=(I+XX*)^(-1/2)H(I+X*X)^(-1/2) contracts the Frobenius norm.

Interface: `Paper26.GraphFisherBudget.GraphTangentInput.geometry`. The witness remains external.

Sources: [NZ2026](https://arxiv.org/html/2609.10514v1).

Missing formalization: No Lean witness of the generic graph unitary/derivative/contraction geometry is constructed locally. The explicitly parameterized local Fisher deductions remain relative to this raw geometry.

## P26-EXT-PRINCIPAL-ANGLE-DECOMPOSITION

Two complex orthogonal projectors admit a simultaneous unitary CS decomposition: generic two-dimensional blocks have P=diag(1,0), Q=[[c²,cs],[cs,s²]], c,s>0 and c²+s²=1, together with the four common-range/common-kernel and exclusive-range pieces. Angles may repeat.

Interface: `Paper26.SupportCompression.PrincipalAngleDecompositionInput`. The witness remains external.

Sources: [BENITEZ_RAKOCEVIC2008](https://personales.upv.es/jbenitez/articulos/ben_rak.pdf).

Missing formalization: No Lean witness of the raw classical CS decomposition and its elementary bisector/padding corollary is constructed locally. PropositionB.1 is proved relative to that exact generic matrix input.

## P26-EXT-HAAR-COORDINATE-MOMENTS

For a complex Haar unit vector u in dimension d≥1 and P=|u><u|, E[P_ij]=δ_ij/d and E[P_ab P_ij]=(δ_ab δ_ij+δ_aj δ_ib)/(d(d+1)). These are exactly the n1 and n2 coordinate cases of Harrow Proposition6 Eq7.

Interface: `Paper26.OneCopyObservation.HaarCoordinateMoments`. The witness remains external.

Sources: [HARROW2013](https://arxiv.org/pdf/1308.6595).

Missing formalization: A local Lean witness converting the all-n generic Haar moment into these explicit coordinate identities has not been constructed. They are accepted as a separately named raw standard n1/n2 specialization, not as a weighted-observation theorem.

## P26-EXT-WEYL-HERMITIAN

For complex Hermitian A,B and every same ordered eigenvalue indexi, |λ_i(A)−λ_i(B)|≤‖A−B‖₂.

Interface: `Paper26.OneCopySubmatrix.WeylEigenvalueInput.perturbation`. The witness remains external.

Sources: [HIGHAM2021_WEYL](https://nhigham.com/2021/03/09/eigenvalue-inequalities-for-hermitian-matrices/).

Missing formalization: No local generic Lean witness of Weyl/minmax perturbation is constructed; a targeted search found no such eigenvalues₀ norm theorem in pinned Mathlib matrix modules.

## P26-EXT-COMPACT-FIBER-SELECTION

A Borel relation R⊆X×Y between Polish spaces, with every fiber nonempty and Kσ, has a Borel selector on allX. Compact nonempty fibers give the exact input specialization.

Interface: `Paper26.MeasurableSpectralSelection.CompactFiberSelectionInput.selection`. The witness remains external.

Sources: [KECHRIS_WOLMAN2025](https://michael.wolman.ca/papers/invariant_uniformization.pdf).

Missing formalization: A local Lean witness of generic Arsenin–Kunugui uniformization is not constructed. Only this exact generic compact-fiber special case is an explicit supporting input.

## P26-EXT-PURE-BINARY-TESTING

On every finite complex Hilbert space, binary discrimination of two pure states rho,sigma with equal priors has minimal mean error (1-sqrt(1-ReTr(rho*sigma)))/2. Every two PSD effects E,F with E+F=I has at least this error, measured as (ReTr(rho*F)+ReTr(sigma*E))/2.

Interface: `Paper26.ConfidenceLowerBounds.PureBinaryTestingInput`. The witness remains external.

Sources: [WATROUS2018](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf).

Missing formalization: No local generic Holevo–Helstrom/pure trace-norm witness is constructed. The exact raw matrix-effect lower-error and attaining-effect fields remain an explicit known proposition parameter.

## P26-EXT-HAUSDORFF-MOMENT-UNIQUENESS

A probability measure on [0,1] is uniquely determined by its moments of every nonnegative integer order. Thus real-line probabilities mu,nu supported almost everywhere in[0,1], with equal integrals of x^k for every natural k, are equal.

Interface: `Paper26.PureBetaLaw.HausdorffMomentInput.unique`. The witness remains external.

Sources: [DIACONIS_FREEDMAN2004](https://www.stat.berkeley.edu/~aldous/206-Exch/Papers/diaconis_2004.pdf).

Missing formalization: The exact compact-interval moment uniqueness witness remains an explicit generic supporting proposition; no local polynomial-density/algebra witness is claimed.

## P26-EXT-BETA-MOMENT-RECURRENCE

For every positive real a,b and natural k, the beta(a,b) probability measure satisfies M_(k+1)=M_k*(a+k)/(a+b+k), where M_k=integral x^k. This follows from M_k=B(a+k,b)/B(a,b) and Gamma recurrence.

Interface: `Paper26.PureBetaLaw.BetaMomentsInput.recurrence`. The witness remains external.

Sources: [NIST_DLMF_BETA](https://dlmf.nist.gov/5.12.E1).

Missing formalization: No local witness integrating every polynomial against the actual beta density is assembled; only this precise generic recurrence is external.

## P26-EXT-GAUSSIAN-MASS-MOMENT

For every real Euclidean dimension p and variance v>0, G(x)=(2*pi*v)^(-p/4)*exp(-norm(x)^2/(4v)) has integral G^2=1 and integral norm(x)^2*G^2=p*v, with both integrands integrable.

Interface: `Paper26.NumericGraphPrior.GaussianMassMomentInput`. The witness remains external.

Sources: [VERSHYNIN2018_GAUSSIAN_NETS](https://webapps.math.uci.edu/~rvershyn/papers/HDP-book/HDP-1.pdf).

Missing formalization: No local witness assembling these all-dimensional Gaussian mass/moment identities in the exact Euclidean-volume encoding is constructed; the standard exact analytic proposition remains explicit.

## P26-EXT-GAUSSIAN-MATRIX-TAIL

An s-by-r complex Gaussian matrix with all real/imaginary coordinates independent N(0,v), v>0, satisfies P{operatorNorm X>u}<=9^(2*(r+s))*exp(-u^2/(8v)) for all r,s>=1,u>0.

Interface: `Paper26.NumericGraphPrior.GaussianMatrixTailInput.tail`. The witness remains external.

Sources: [VERSHYNIN2018_GAUSSIAN_NETS](https://webapps.math.uci.edu/~rvershyn/papers/HDP-book/HDP-1.pdf), [MEZZADRI2007](https://arxiv.org/pdf/math-ph/0609050v2).

Missing formalization: The exact generic finite-net/Gaussian-projection/radial-integration witness is not assembled locally; its actual-measure inequality is an explicit standard supporting corollary.

## P26-EXT-COMPACT-LIPSCHITZ-H1

Every globally Lipschitz compactly supported real function on finite-dimensional real Euclidean space belongs to H1; its weak derivative agrees almost everywhere with the classical Frechet derivative. It can use actual f and actual fderiv as representatives, with Lipschitz derivative norm bound.

Interface: `Paper26.NumericGraphPrior.CompactLipschitzH1Input.root`. The witness remains external.

Sources: [HAJLASZ_CORTONA](https://sites.pitt.edu/~hajlasz/Notatki/Cortona%20Lectures.pdf).

Missing formalization: No local generic Lipschitz-to-distributional-Sobolev witness is assembled. Only this exact standard representative theorem is supplied explicitly, separately from the existing generic weak product rule.

