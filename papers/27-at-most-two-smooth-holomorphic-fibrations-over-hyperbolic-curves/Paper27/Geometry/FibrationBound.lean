import Paper27.Geometry.ClassicalInputs
import Paper27.Geometry.RetractionNormalAtlasBridge

/-!
# The at-most-two theorem for actual compact complex surfaces

The universal classical parameters are explicit. Every pair-specific object
used below, including finite pair maps, critical curves, unramified
restrictions, common retractions, normal atlases, tensor gauges and the two
third-fibration obstructions, is constructed by the own proof chain.

The equivalence relation changes only the base by a biholomorphism. The
empty-critical-set branch permits a third fibration that need not be smooth.
The final theorem counts actual smooth holomorphic fibrations with connected
fibres over actual compact curves of genus at least two.
-/
noncomputable section
namespace Paper27.Geometry

namespace ClassicalInputs
open RetractionCoordinateGerms RetractionFactorization
variable {X : CompactComplexSurface} (K : ClassicalInputs)
include K

/-- Actual unramified restrictions from original maps, with the general
normalization chosen internally. -/
theorem unramified_tangent (f g : Fibration X) (hf : f.Smooth) (hg : g.Smooth)
    (hB : f.Hyperbolic) (hC : g.Hyperbolic)
    (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g)
    (D : EmbeddedCurve X) (hD : D.TangentToPair f g) :
    D.Unramified f ∧ D.Unramified g := by
  obtain ⟨N⟩ := K.normalization X (f.base.productSurface g.base)
    (RamificationSupport.finiteSurjectivePair f g hfinite hsurj)
  exact K.toCurveBranchInputs.unramified_of_tangency f g hf hg hB hC
    hfinite hsurj N D hD

/-- The original pair supplies an actual normal atlas for any already chosen
factored retractions on their common actual neighbourhood. -/
theorem normal_atlas (f g : Fibration X) (hf : f.Smooth) (hg : g.Smooth)
    (hB : f.Hyperbolic) (hC : g.Hyperbolic)
    (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g)
    {D : EmbeddedCurve X} {U : D.Neighbourhood} {r s : D.Retraction U}
    (hD : D.TangentToPair f g) (hr : Factorization r f) (hs : Factorization s g) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty (NormalAtlas D U r s n) := by
  obtain ⟨N⟩ := K.normalization X (f.base.productSurface g.base)
    (RamificationSupport.finiteSurjectivePair f g hfinite hsurj)
  obtain ⟨n, hn, hA, _hindex⟩ :=
    RetractionNormalAtlasBridge.normalAtlas_of_original_pair K.toCurveBranchInputs
      K.localDegrees K.dividedDifferences K.localUnitRoots hf hg hB hC
      hfinite hsurj N hD hr hs
  exact ⟨n, hn, hA⟩

/-- The two actual component alternatives of Lemma 3.1 both contradict a
third inequivalent smooth hyperbolic fibration. -/
theorem no_three_inequivalent (f g h : Fibration X)
    (hf : f.Smooth) (hg : g.Smooth) (hh : h.Smooth)
    (hB : f.Hyperbolic) (hC : g.Hyperbolic) (hH : h.Hyperbolic)
    (hnefg : ¬ Fibration.Equivalent f g) (hnefh : ¬ Fibration.Equivalent f h)
    (hnegh : ¬ Fibration.Equivalent g h) : False := by
  classical
  obtain ⟨hfinite, hsurj⟩ := K.finite_pair f g hf hg hnefg
  by_cases hempty : RamificationSupport.ramificationSet f g = ∅
  · rcases K.third_equivalent_of_empty f g hf hg hB hC hnefg hempty h hH with he | he
    · exact hnefh (Fibration.equivalent_symm he)
    · exact hnegh (Fibration.equivalent_symm he)
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨F⟩ := RamificationFamilies.ramification_family_exists K.toCurveBranchInputs
    K.submanifolds K.nonsingularOpen f g hf hg hB hC hfinite hsurj
  rw [← F.support_eq] at hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  let D := F.member i
  have hDfg : D.TangentToPair f g := by
    intro p hp
    rw [← F.support_eq]
    exact Set.mem_iUnion.mpr ⟨i, hp⟩
  have hD : D.curve.Hyperbolic := F.hyperbolic i
  have hDf : D.Unramified f := F.first_unramified i
  have hDg : D.Unramified g := F.second_unramified i
  let R := CommonRetractions.pair K.unramifiedCurveCovering K.neighbourhoodLifting
    K.etaleLiftRegularity D f g hDf hDg
  obtain ⟨n, hn, ⟨A⟩⟩ := K.normal_atlas f g hf hg hB hC hfinite hsurj hDfg
    R.first_factor R.second_factor
  obtain ⟨N, T, ⟨frames⟩⟩ := K.normalFrames X D
  let tensor := A.componentNormalTensorData K.regularity frames hn
  obtain ⟨hfinite13, hsurj13⟩ := K.finite_pair f h hf hh hnefh
  obtain ⟨hfinite23, hsurj23⟩ := K.finite_pair g h hg hh hnegh
  obtain ⟨F13⟩ := RamificationFamilies.ramification_family_exists K.toCurveBranchInputs
    K.submanifolds K.nonsingularOpen f h hf hh hB hH hfinite13 hsurj13
  obtain ⟨F23⟩ := RamificationFamilies.ramification_family_exists K.toCurveBranchInputs
    K.submanifolds K.nonsingularOpen g h hg hh hC hH hfinite23 hsurj23
  rcases intrinsic_ramification_component_dichotomy K.metrics K.frameCalculus K.degreeTheory
    K.degreeGaugeInvariance K.homDegree f g h hf hg hh hB hC hH D tensor hD
    hDf hDg hDfg F13 F23 with hdisjoint | hcommon
  · exact ActualDisjointObstruction.impossible K.regularity K.normalDivision K.mapGermGluing
      K.splittingCalculus K.normalFrames K.degreeTheory K.degreeGaugeInvariance K.bott
      K.nonsingularOpen A hn f h R.first_factor hDf hdisjoint.1 hD
  · have hDh := (K.unramified_tangent f h hf hh hB hH hfinite13 hsurj13 D hcommon.1).2
    let S := CommonRetractions.triple K.unramifiedCurveCovering K.neighbourhoodLifting
      K.etaleLiftRegularity D f g h hDf hDg hDh
    obtain ⟨n₁, hn₁, ⟨A₁⟩⟩ := K.normal_atlas f g hf hg hB hC hfinite hsurj hDfg
      S.first_factor S.second_factor
    obtain ⟨n₂, hn₂, ⟨A₂⟩⟩ := K.normal_atlas f h hf hh hB hH hfinite13 hsurj13 hcommon.1
      S.first_factor S.third_factor
    obtain ⟨n₃, hn₃, ⟨A₃⟩⟩ := K.normal_atlas g h hg hh hC hH hfinite23 hsurj23 hcommon.2
      S.second_factor S.third_factor
    exact ThreePairNormalObstruction.impossible K.taylor K.parameterTaylor K.normalFrames
      K.degreeTheory K.degreeGaugeInvariance A₁ A₂ A₃ hn₁ hn₂ hn₃ hD

/-- Theorem 1.1 relative only to the precise universal classical inputs. -/
theorem at_most_two (X : CompactComplexSurface) : AtMostTwoSmoothHyperbolicFibrations X := by
  classical
  intro f g h
  by_cases hfg : Fibration.Equivalent f.val g.val
  · exact Or.inl hfg
  by_cases hfh : Fibration.Equivalent f.val h.val
  · exact Or.inr (Or.inl hfh)
  by_cases hgh : Fibration.Equivalent g.val h.val
  · exact Or.inr (Or.inr hgh)
  exact False.elim (K.no_three_inequivalent f.val g.val h.val f.property.1 g.property.1
    h.property.1 f.property.2 g.property.2 h.property.2 hfg hfh hgh)

/-- The same theorem directly on the actual equivalence classes. -/
theorem at_most_two_classes (X : CompactComplexSurface) : AtMostTwoFibrationClasses X :=
  (atMostTwoSmoothHyperbolicFibrations_iff_classes X).mp (K.at_most_two X)

end ClassicalInputs
end Paper27.Geometry
