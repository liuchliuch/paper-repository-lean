import Paper27.Geometry.FibrationBound
import Paper27.Geometry.RamificationDivisorOrder

/-!
# The actual components and common indices of Lemma 3.1

The common alternative identifies the embedded supports in both other
ramification families. Its index statement quantifies over every actual
surface cyclic chart on the same embedded curve, rather than asserting an
equality of unrelated numerical labels.
-/
noncomputable section
namespace Paper27.Geometry
open RamificationIndexConstancy RetractionCoordinateGerms

structure CommonComponentIndices {X : CompactComplexSurface} (f g h : Fibration X)
    (hfinite12 : f.FinitePair g) (hsurj12 : f.PairSurjective g)
    (hfinite13 : f.FinitePair h) (hsurj13 : f.PairSurjective h)
    (hfinite23 : g.FinitePair h) (hsurj23 : g.PairSurjective h)
    (D : EmbeddedCurve X) where
  index : ℕ
  index_ge_two : 2 ≤ index
  first : ∀ p : D.curve,
    ∀ A : SurfaceCyclicChart (RamificationSupport.finiteSurjectivePair f g hfinite12 hsurj12)
      (D.inclusion p), A.exponent = index
  second : ∀ p : D.curve,
    ∀ A : SurfaceCyclicChart (RamificationSupport.finiteSurjectivePair f h hfinite13 hsurj13)
      (D.inclusion p), A.exponent = index
  third : ∀ p : D.curve,
    ∀ A : SurfaceCyclicChart (RamificationSupport.finiteSurjectivePair g h hfinite23 hsurj23)
      (D.inclusion p), A.exponent = index

namespace ClassicalInputs
variable {X : CompactComplexSurface} (K : ClassicalInputs)
include K

/-- The three original pairs have the same actual local index along an
actual common component. The index and all three atlases are constructed. -/
theorem common_component_indices (f g h : Fibration X)
    (hf : f.Smooth) (hg : g.Smooth) (hh : h.Smooth)
    (hB : f.Hyperbolic) (hC : g.Hyperbolic) (hH : h.Hyperbolic)
    (hfinite12 : f.FinitePair g) (hsurj12 : f.PairSurjective g)
    (hfinite13 : f.FinitePair h) (hsurj13 : f.PairSurjective h)
    (hfinite23 : g.FinitePair h) (hsurj23 : g.PairSurjective h)
    (D : EmbeddedCurve X) (hD : D.curve.Hyperbolic)
    (hD12 : D.TangentToPair f g) (hD13 : D.TangentToPair f h)
    (hD23 : D.TangentToPair g h) :
    Nonempty (CommonComponentIndices f g h hfinite12 hsurj12 hfinite13 hsurj13
      hfinite23 hsurj23 D) := by
  have hu12 := K.unramified_tangent f g hf hg hB hC hfinite12 hsurj12 D hD12
  have hu13 := K.unramified_tangent f h hf hh hB hH hfinite13 hsurj13 D hD13
  let R := CommonRetractions.triple K.unramifiedCurveCovering K.neighbourhoodLifting
    K.etaleLiftRegularity D f g h hu12.1 hu12.2 hu13.2
  obtain ⟨N12⟩ := K.normalization X (f.base.productSurface g.base)
    (RamificationSupport.finiteSurjectivePair f g hfinite12 hsurj12)
  obtain ⟨N13⟩ := K.normalization X (f.base.productSurface h.base)
    (RamificationSupport.finiteSurjectivePair f h hfinite13 hsurj13)
  obtain ⟨N23⟩ := K.normalization X (g.base.productSurface h.base)
    (RamificationSupport.finiteSurjectivePair g h hfinite23 hsurj23)
  obtain ⟨n, hn, ⟨A⟩, hi12⟩ :=
    RetractionNormalAtlasBridge.normalAtlas_of_original_pair K.toCurveBranchInputs
      K.localDegrees K.dividedDifferences K.localUnitRoots hf hg hB hC hfinite12 hsurj12
      N12 hD12 R.first_factor R.second_factor
  obtain ⟨m, hm, ⟨B⟩, hi13⟩ :=
    RetractionNormalAtlasBridge.normalAtlas_of_original_pair K.toCurveBranchInputs
      K.localDegrees K.dividedDifferences K.localUnitRoots hf hh hB hH hfinite13 hsurj13
      N13 hD13 R.first_factor R.third_factor
  obtain ⟨k, hk, ⟨C⟩, hi23⟩ :=
    RetractionNormalAtlasBridge.normalAtlas_of_original_pair K.toCurveBranchInputs
      K.localDegrees K.dividedDifferences K.localUnitRoots hg hh hC hH hfinite23 hsurj23
      N23 hD23 R.second_factor R.third_factor
  obtain ⟨N, T, ⟨F⟩⟩ := K.normalFrames X D
  obtain ⟨hnm, hnk⟩ := ThreePairNormalObstruction.three_exponents_equal_common_frames
    K.regularity K.degreeTheory K.degreeGaugeInvariance A B C F hn hm hk hD
  exact ⟨⟨n, hn, hi12, fun p a => (hi13 p a).trans hnm.symm,
    fun p a => (hi23 p a).trans hnk.symm⟩⟩

/-- Lemma 3.1 on an actual component, with the general embedded-submanifold
factorization theorem as the one supplementary classical input. -/
theorem component_alternatives (factor : HolomorphicEmbeddedFactorization)
    (f g h : Fibration X) (hf : f.Smooth) (hg : g.Smooth) (hh : h.Smooth)
    (hB : f.Hyperbolic) (hC : g.Hyperbolic) (hH : h.Hyperbolic)
    (hfinite12 : f.FinitePair g) (hsurj12 : f.PairSurjective g)
    (hfinite13 : f.FinitePair h) (hsurj13 : f.PairSurjective h)
    (hfinite23 : g.FinitePair h) (hsurj23 : g.PairSurjective h)
    (D : EmbeddedCurve X) (hD : D.curve.Hyperbolic)
    (hD12 : D.TangentToPair f g)
    (F13 : RamificationCurveFamily f h) (F23 : RamificationCurveFamily g h) :
    (D.DisjointFromPair f h ∧ D.DisjointFromPair g h) ∨
      (D.TangentToPair f h ∧ D.TangentToPair g h ∧
        (∃ i j, D.support = (F13.member i).support ∧ D.support = (F23.member j).support) ∧
        Nonempty (CommonComponentIndices f g h hfinite12 hsurj12 hfinite13 hsurj13
          hfinite23 hsurj23 D)) := by
  have hu := K.unramified_tangent f g hf hg hB hC hfinite12 hsurj12 D hD12
  let R := CommonRetractions.pair K.unramifiedCurveCovering K.neighbourhoodLifting
    K.etaleLiftRegularity D f g hu.1 hu.2
  obtain ⟨n, hn, ⟨A⟩⟩ := K.normal_atlas f g hf hg hB hC hfinite12 hsurj12 hD12
    R.first_factor R.second_factor
  obtain ⟨N, T, ⟨F⟩⟩ := K.normalFrames X D
  let tensor := A.componentNormalTensorData K.regularity F hn
  rcases intrinsic_ramification_component_dichotomy K.metrics K.frameCalculus K.degreeTheory
    K.degreeGaugeInvariance K.homDegree f g h hf hg hh hB hC hH D tensor hD
    hu.1 hu.2 hD12 F13 F23 with hd | hc
  · exact Or.inl hd
  · refine Or.inr ⟨hc.1, hc.2, ?_, ?_⟩
    · exact common_components_of_tangency factor (FibreGeometry.compactCurveMapTheorem K.curveMaps)
        f g h D F13 F23 hc.1 hc.2
    · exact K.common_component_indices f g h hf hg hh hB hC hH
        hfinite12 hsurj12 hfinite13 hsurj13 hfinite23 hsurj23 D hD hD12 hc.1 hc.2

/-- Lemma 3.1 directly from the original three pairwise inequivalent smooth
hyperbolic fibrations. Finite pair maps, critical-curve families and the
hyperbolicity of every component are all derived inside the proof. -/
theorem three_fibration_component_alternatives (factor : HolomorphicEmbeddedFactorization)
    (f g h : Fibration X) (hf : f.Smooth) (hg : g.Smooth) (hh : h.Smooth)
    (hB : f.Hyperbolic) (hC : g.Hyperbolic) (hH : h.Hyperbolic)
    (hnefg : ¬ Fibration.Equivalent f g) (hnefh : ¬ Fibration.Equivalent f h)
    (hnegh : ¬ Fibration.Equivalent g h) :
    ∃ (hfinite12 : f.FinitePair g) (hsurj12 : f.PairSurjective g)
      (hfinite13 : f.FinitePair h) (hsurj13 : f.PairSurjective h)
      (hfinite23 : g.FinitePair h) (hsurj23 : g.PairSurjective h)
      (F12 : RamificationCurveFamily f g) (F13 : RamificationCurveFamily f h)
      (F23 : RamificationCurveFamily g h), ∀ i : F12.Index,
      let D := F12.member i
      (D.DisjointFromPair f h ∧ D.DisjointFromPair g h) ∨
        (D.TangentToPair f h ∧ D.TangentToPair g h ∧
          (∃ j k, D.support = (F13.member j).support ∧ D.support = (F23.member k).support) ∧
          Nonempty (CommonComponentIndices f g h hfinite12 hsurj12 hfinite13 hsurj13
            hfinite23 hsurj23 D)) := by
  obtain ⟨hfinite12, hsurj12⟩ := K.finite_pair f g hf hg hnefg
  obtain ⟨hfinite13, hsurj13⟩ := K.finite_pair f h hf hh hnefh
  obtain ⟨hfinite23, hsurj23⟩ := K.finite_pair g h hg hh hnegh
  obtain ⟨F12⟩ := RamificationFamilies.ramification_family_exists K.toCurveBranchInputs
    K.submanifolds K.nonsingularOpen f g hf hg hB hC hfinite12 hsurj12
  obtain ⟨F13⟩ := RamificationFamilies.ramification_family_exists K.toCurveBranchInputs
    K.submanifolds K.nonsingularOpen f h hf hh hB hH hfinite13 hsurj13
  obtain ⟨F23⟩ := RamificationFamilies.ramification_family_exists K.toCurveBranchInputs
    K.submanifolds K.nonsingularOpen g h hg hh hC hH hfinite23 hsurj23
  refine ⟨hfinite12, hsurj12, hfinite13, hsurj13, hfinite23, hsurj23, F12, F13, F23, ?_⟩
  intro i
  have ht : (F12.member i).TangentToPair f g := by
    intro x hx
    rw [← F12.support_eq]
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  exact K.component_alternatives factor f g h hf hg hh hB hC hH
    hfinite12 hsurj12 hfinite13 hsurj13 hfinite23 hsurj23 (F12.member i)
    (F12.hyperbolic i) ht F13 F23

end ClassicalInputs
end Paper27.Geometry
