import Paper27.Geometry.FormulaSixInvariantExtension
import Paper27.Geometry.ThreePairNormalObstruction
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Formula (6) from actual ramification components and retractions

This wrapper constructs the invariant punctured neighbourhood and actual
finite cyclic action, derives equality of the three normal indices from
intrinsic normal degree, chooses the complex primitive root, and invokes
the original actual-section averaging proof. No punctured transversality,
equal index, scalar order, leading constant, or action is an input.
-/
noncomputable section
open scoped Manifold Topology
open Filter
namespace Paper27.Geometry.FormulaSixGeometry
open RetractionCoordinateGerms RetractionCoefficientHolomorphic MeromorphicSplittingAverage
  PuncturedSplittingSections NormalDegreeInvariance
variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r₁ r₂ r₃ : D.Retraction U} {n m k : ℕ}

/-- The original formula-(6) common-tangency contradiction for three actual
fibrations, their common actual ramification component, and actual pair
normal atlases. All section and action data are constructed inside. -/
theorem impossible
    (J : TaylorGerms.TaylorCalculus) (P : ParametricTaylorCalculus J)
    (L : LaurentCalculus) (extension : LaurentSectionExtension L)
    (calculus : HolomorphicPuncturedCalculus)
    (division : NormalAtlasAction.HolomorphicNormalDivision)
    (gluing : NormalAtlasAction.HolomorphicOpenGermGluing)
    (frames : ThreePairNormalObstruction.NormalFrameExistence)
    (theory : LineBundleDegreeTheory) (invariance : LineBundleDegreeGaugeInvariance theory)
    (bott : NeighbourhoodSplittings.BottTangentialSubbundleDegreeZero theory)
    (f g h : Fibration X) (F : RamificationCurveFamily f g) (E : RamificationCurveFamily f h)
    (j : F.Index) (l : E.Index)
    (hF : D.support = (F.member j).support) (hE : D.support = (E.member l).support)
    (A : NormalAtlas D U r₁ r₂ n) (B : NormalAtlas D U r₁ r₃ m)
    (C : NormalAtlas D U r₂ r₃ k)
    (hn : 2 ≤ n) (hm : 2 ≤ m) (hk : 2 ≤ k)
    (hf : D.Unramified f) (hg : D.Unramified g) (hh : D.Unramified h)
    (hr₁ : RetractionFactorization.Factorization r₁ f)
    (hr₂ : RetractionFactorization.Factorization r₂ g)
    (hr₃ : RetractionFactorization.Factorization r₃ h)
    (hD : D.curve.Hyperbolic) : False := by
  obtain ⟨N, T, ⟨Fr⟩⟩ := frames X D
  obtain ⟨hnm, hnk⟩ := ThreePairNormalObstruction.three_exponents_equal_common_frames
    P.regularity theory invariance A B C Fr hn hm hk hD
  subst m
  subst k
  obtain ⟨W, r, s, t, action, hWU, hr, hs, ht, htrans₂, htrans₃, hgerm, hfixed, _, hpres⟩ :=
    PuncturedNeighbourhoods.cyclic_family_action_with_punctured_transverse division P.regularity
      gluing f g h F E j l hF hE A hn r₃ hf hg hh hr₁ hr₂ hr₃
  let Aw := A.restrict r s hr hs
  let Bw := B.restrict r t hr ht
  let Cw := C.restrict s t hs ht
  have hfix : ∀ z p, action.permutation z (NeighbourhoodSplittings.curvePoint W p) =
      NeighbourhoodSplittings.curvePoint W p := by
    intro z p
    apply Subtype.ext
    exact (action.map_eq z (NeighbourhoodSplittings.curvePoint W p)).symm.trans (hfixed z p)
  let scalar : rootsOfUnity n ℂ →* ℂˣ := (rootsOfUnity n ℂ).subtype
  have hgermw : ∀ z p, action.map z =ᶠ[𝓝 (D.inclusion p)]
      NormalAtlasAction.localRotation (Aw.chart p p).coordinates (scalar z : ℂ) := hgerm
  letI : NeZero n := ⟨by omega⟩
  let ζ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n (by omega)
  let z : rootsOfUnity n ℂ := hζ.toRootsOfUnity
  have hz : (scalar z : ℂ) = ζ := by simp [scalar, z]
  have hroot : IsPrimitiveRoot (scalar z : ℂ) n := hz.symm ▸ hζ
  have htrans₂w : PuncturedSplittingSections.JointTransverse r s := by
    intro q
    exact htrans₂ q.val.val q.val.property q.property
  have htrans₃w : PuncturedSplittingSections.JointTransverse r t := by
    intro q
    exact htrans₃ q.val.val q.val.property q.property
  have hzn : z ^ n = 1 := by
    apply Subtype.ext
    apply Units.ext
    change (z : ℂˣ).val ^ n = 1
    exact (mem_rootsOfUnity' n z.val).mp z.property
  have hpresz : ∀ q : W.domain, s.toFun (action.map z q.val) = s.toFun q.val :=
    fun q => hpres z q.val q.property
  obtain ⟨a, S, _ha0, _ha1, hhol, hsplit, _hres, _hinvariant, hincl⟩ :=
    Aw.actual_formulaSix_invariant_extension J P L extension calculus Bw Cw hn action hfix
      scalar hgermw z hzn hroot hpresz htrans₂w htrans₃w
  have hzero := RetractionCoordinateGerms.NormalAtlas.bott_of_extended_splitting
    (r₁ := r) theory bott Fr S hhol hsplit hincl
  have hnegative := Aw.normal_degree_negative P.regularity Fr (by omega) theory invariance hD
  omega
end Paper27.Geometry.FormulaSixGeometry
