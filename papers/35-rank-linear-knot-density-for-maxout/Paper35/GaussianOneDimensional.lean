import Paper35.GaussianUpperEnvelope
import Mathlib.Topology.Separation.Connected
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace Paper35.GaussianMarked

theorem unit_one_dimensional_image_finite (L : ℝ) (ψ : ℝ → Source.Space 1)
    (hunit : ∀ s ∈ Icc 0 L, ‖ψ s‖ = 1) : (ψ '' Icc 0 L).Finite := by
  let ep : Source.Space 1 := WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ))
  let em : Source.Space 1 := WithLp.toLp 2 (fun _ : Fin 1 => (-1 : ℝ))
  apply ((Set.finite_singleton em).insert ep).subset
  rintro x ⟨s,hs,rfl⟩
  have hx : (ψ s 0) ^ 2 = 1 := by
    have h := EuclideanSpace.norm_sq_eq (ψ s)
    rw [hunit s hs, one_pow] at h
    simpa only [Fin.sum_univ_one, Real.norm_eq_abs, sq_abs] using h.symm
  have hprod : (ψ s 0 - 1) * (ψ s 0 + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hprod with hp | hm
  · have hplus : ψ s 0 = 1 := by linarith
    apply Or.inl
    ext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact hplus
  · have hminus : ψ s 0 = -1 := by linarith
    apply Or.inr
    ext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact hminus

theorem one_dimensional_sphere_constant (L : ℝ) (hL : 0 < L)
    (ψ : ℝ → Source.Space 1) (hac : AbsolutelyContinuousOnInterval ψ 0 L)
    (hunit : ∀ s ∈ Icc 0 L, ‖ψ s‖ = 1) :
    ∀ s ∈ Icc 0 L, ψ s = ψ 0 := by
  have hc : ContinuousOn ψ (Icc 0 L) := by
    simpa only [uIcc_of_le hL.le] using hac.continuousOn
  have hpre := isPreconnected_Icc.image ψ hc
  have hfin := unit_one_dimensional_image_finite L ψ hunit
  have hsub : (ψ '' Icc 0 L).Subsingleton := by
    by_contra h
    exact hfin.not_infinite (hpre.infinite_of_nontrivial (Set.not_subsingleton_iff.mp h))
  intro s hs
  exact hsub ⟨s,hs,rfl⟩ ⟨0,⟨le_rfl,hL.le⟩,rfl⟩

theorem switchCount_of_constant_on_interval {K : ℕ} (f : Fin K → ℝ → ℝ)
    (v : Fin K → ℝ) (L : ℝ) (hf : ∀ j s, s ∈ Icc 0 L → f j s = v j) :
    switchCount f L = 0 := by
  have hnone (s : ℝ) : ¬ ActiveSwitch f L s := by
    rintro ⟨hs0,hsL,i,j,hij,heq,hbelow,δ,hδ,hsign⟩
    have heqv : v i = v j := by
      simpa only [hf i s ⟨hs0.le,hsL.le⟩, hf j s ⟨hs0.le,hsL.le⟩] using heq
    let t := s - min δ s / 2
    have hm : 0 < min δ s := lt_min hδ hs0
    have htleft : t ∈ Ioo (s-δ) s := by
      have := min_le_left δ s
      constructor <;> dsimp [t] <;> linarith
    have ht : t ∈ Icc 0 L := by
      have := min_le_right δ s
      constructor <;> dsimp [t] <;> linarith
    have hz : f i t - f j t = 0 := by rw [hf i t ht,hf j t ht,heqv,sub_self]
    rcases hsign with ⟨hleft,_⟩ | ⟨hleft,_⟩
    · have h := hleft t htleft
      change f i t - f j t < 0 at h
      rw [hz] at h
      exact lt_irrefl _ h
    · have h := hleft t htleft
      change 0 < f i t - f j t at h
      rw [hz] at h
      exact lt_irrefl _ h
  have hempty : switchSet f L = ∅ := Set.eq_empty_iff_forall_notMem.mpr hnone
  simp [switchCount,hempty]

theorem gaussian_one_dimensional_envelope_length (n : ℕ) (L : ℝ) (hL : 0 < L)
    (ψ : ℝ → Source.Space 1) (hac : AbsolutelyContinuousOnInterval ψ 0 L)
    (hunit : ∀ s ∈ Icc 0 L, ‖ψ s‖ = 1) :
    expectedSwitchCount (gaussianIid 1 (n+2)) (gaussianScores ψ) L =
      ENNReal.ofReal (Paper35.gaussianRankCoefficient (n+2)) * eVariationOn ψ (Icc 0 L) := by
  have hc := one_dimensional_sphere_constant L hL ψ hac hunit
  have hvar : eVariationOn ψ (Icc 0 L) = 0 := by
    apply eVariationOn.constant_on
    rintro a ⟨s,hs,rfl⟩ b ⟨t,ht,rfl⟩
    rw [hc s hs,hc t ht]
  have hcount (Z : Fin (n+2) → Source.Space 1) : switchCount (gaussianScores ψ Z) L = 0 := by
    apply switchCount_of_constant_on_interval _ (fun j => inner ℝ (Z j) (ψ 0)) L
    intro j s hs
    simp only [gaussianScores,hc s hs]
  simp only [expectedSwitchCount,hcount,lintegral_zero,hvar,mul_zero]

/-- Full original m≥1 dimension range of Lemma 6.2, including the degenerate sphere S⁰. -/
theorem gaussian_upper_envelope_all_dimensions (hcrofton : ClassicalCroftonLaw)
    (hregular : ClassicalCroftonRegularityLaw) (hproj : GaussianUnitProjectionLaw)
    (hrot : GaussianPairReconstructionLaw) (hmax : GaussianMaxIntegralLaw)
    (hlength : ACCurveLengthLaw) (m n : ℕ) (hm : 1 ≤ m) (L : ℝ) (hL : 0 < L)
    (ψ : ℝ → Source.Space m) (hac : AbsolutelyContinuousOnInterval ψ 0 L)
    (hunit : ∀ s ∈ Icc 0 L, ‖ψ s‖ = 1)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample m n) (CurveParameter L)) :
    expectedSwitchCount (gaussianIid m (n+2)) (gaussianScores ψ) L =
      ENNReal.ofReal (Paper35.gaussianRankCoefficient (n+2)) * eVariationOn ψ (Icc 0 L) := by
  by_cases h1 : m = 1
  · subst m
    exact gaussian_one_dimensional_envelope_length n L hL ψ hac hunit
  · have hm2 : 2 ≤ m := by omega
    exact gaussian_upper_envelope_length hcrofton hregular hproj hrot hmax hlength
      m n hm2 L hL ψ hac hunit hLN

theorem aemeasurable_iid_switchCount_all_dimensions (hrot : GaussianPairReconstructionLaw)
    (hregular : ClassicalCroftonRegularityLaw) (m n : ℕ) (hm : 1 ≤ m) (L : ℝ)
    (hL : 0 < L) (ψ : ℝ → Source.Space m)
    (hac : AbsolutelyContinuousOnInterval ψ 0 L)
    (hunit : ∀ s ∈ Icc 0 L, ‖ψ s‖ = 1)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample m n) (CurveParameter L)) :
    AEMeasurable (fun Z => switchCount (gaussianScores ψ Z) L) (gaussianIid m (n+2)) := by
  by_cases h1 : m = 1
  · subst m
    have hc := one_dimensional_sphere_constant L hL ψ hac hunit
    have hcount (Z : Fin (n+2) → Source.Space 1) : switchCount (gaussianScores ψ Z) L = 0 := by
      apply switchCount_of_constant_on_interval _ (fun j => inner ℝ (Z j) (ψ 0)) L
      intro j s hs
      simp only [gaussianScores,hc s hs]
    simp only [hcount]
    exact aemeasurable_const
  · exact aemeasurable_iid_switchCount hrot hregular m n (by omega) L hL ψ hac hunit hLN
end Paper35.GaussianMarked
