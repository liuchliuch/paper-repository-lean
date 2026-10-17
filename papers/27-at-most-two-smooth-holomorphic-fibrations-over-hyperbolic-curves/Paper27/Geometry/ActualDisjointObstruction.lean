import Paper27.Geometry.NormalAtlasAction
import Paper27.Geometry.RetractionFactorization
import Paper27.Geometry.ThreePairNormalObstruction
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The actual disjoint-component obstruction of Lemma 3.2

The normal atlas supplies both the negative intrinsic normal degree and the
actual finite normal-rotation action. Disjointness from the third pair gives
an actual transverse neighbourhood. We shrink the action inside that
neighbourhood, transfer the actual transversality, and apply the constructed
actual splitting/average/Bott argument.

There is no action, normal eigenvalue, negative normal degree, splitting,
compact-leaf label, or obstruction conclusion among the geometric inputs.
All remaining classical parameters are the separately stated universal
analytic, germ-gluing, frame, degree, and tangential-subbundle theorems.
-/

noncomputable section
open scoped Manifold

namespace Paper27.Geometry.ActualDisjointObstruction

open RetractionCoordinateGerms NormalAtlasAction RetractionFactorization
open NeighbourhoodSplittings NormalDegreeInvariance

variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r₁ r₂ : D.Retraction U} {n : ℕ}

/-- Changing between two retractions factoring the very same unramified
actual curve restriction preserves actual joint transversality. -/
theorem jointTransverse_of_common_factorization {V : D.Neighbourhood}
    (r s : D.Retraction V) (f h : Fibration X) (hf : D.Unramified f)
    (hr : Factorization r f) (hs : Factorization s f)
    (ht : JointTransverse r (CoordinateCalculus.fibrationMap h)) :
    JointTransverse s (CoordinateCalculus.fibrationMap h) := by
  intro p
  apply (joint_bijective_iff s f h hf hs p).mpr
  exact (joint_bijective_iff r f h hf hr p).mp (ht p)

/-- Lemma 3.2 from an actual normal atlas, actual factorization and actual
disjointness. Primitive roots, honest frames, negative normal degree,
transverse action neighbourhood, initial splitting and average are all
chosen or proved in this theorem and its own previously proved components. -/
theorem impossible
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (division : HolomorphicNormalDivision) (gluing : HolomorphicOpenGermGluing)
    (calculus : HolomorphicSplittingCalculus)
    (frames : ThreePairNormalObstruction.NormalFrameExistence)
    (theory : LineBundleDegreeTheory) (invariance : LineBundleDegreeGaugeInvariance theory)
    (bott : BottTangentialSubbundleDegreeZero theory) (openness : NonsingularJointLocusOpen)
    (A : NormalAtlas D U r₁ r₂ n) (hn : 2 ≤ n) (f h : Fibration X)
    (hfactor : Factorization r₁ f) (hf : D.Unramified f)
    (hdisjoint : D.DisjointFromPair f h) (hD : D.curve.Hyperbolic) : False := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨N, T, ⟨F⟩⟩ := frames X D
  have hnegative := A.normal_degree_negative regularity F (by omega) theory invariance hD
  obtain ⟨V, rV, hVU, hfactorV, htV⟩ := exists_transverse_neighbourhood openness
    r₁ f h hf hfactor hdisjoint
  let rV₀ : D.Retraction V := restrictRetraction r₁ V hVU
  have hfactorV₀ : Factorization rV₀ f := fun x hx => hfactor x (hVU hx)
  have htV₀ : JointTransverse rV₀ (CoordinateCalculus.fibrationMap h) :=
    jointTransverse_of_common_factorization rV rV₀ f h hf hfactorV hfactorV₀ htV
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n (NeZero.ne n)
  obtain ⟨W, rW, action, g, hWV, _hWU, hrW, hrotation, hζone, _hs⟩ :=
    finite_normal_action division regularity gluing A hn V F ζ hζ
  have htW : JointTransverse rW (CoordinateCalculus.fibrationMap h) :=
    jointTransverse_on_smaller rV₀ rW hWV hrW (CoordinateCalculus.fibrationMap h) htV₀
  exact transverse_obstruction calculus theory bott action F g ζ hrotation hζone
    hnegative (CoordinateCalculus.fibrationMap h) htW

/-- The same actual atlas rules out the disjoint alternative without exposing
any averaged section or finite action as an input to the application. -/
theorem not_disjoint
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (division : HolomorphicNormalDivision) (gluing : HolomorphicOpenGermGluing)
    (calculus : HolomorphicSplittingCalculus)
    (frames : ThreePairNormalObstruction.NormalFrameExistence)
    (theory : LineBundleDegreeTheory) (invariance : LineBundleDegreeGaugeInvariance theory)
    (bott : BottTangentialSubbundleDegreeZero theory) (openness : NonsingularJointLocusOpen)
    (A : NormalAtlas D U r₁ r₂ n) (hn : 2 ≤ n) (f h : Fibration X)
    (hfactor : Factorization r₁ f) (hf : D.Unramified f) (hD : D.curve.Hyperbolic) :
    ¬ D.DisjointFromPair f h :=
  fun hdisjoint => impossible regularity division gluing calculus frames theory invariance
    bott openness A hn f h hfactor hf hdisjoint hD

end Paper27.Geometry.ActualDisjointObstruction
