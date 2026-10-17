import Paper38.GradientGeometry
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-! Uniform positive mobility constants are derived on actual compact sets. -/
noncomputable section
namespace Paper38.CompactEllipticity
open Set Metric
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A continuous, pointwise strictly positive mobility has a uniform positive
quadratic lower bound on every compact set. Zero-dimensional spaces are included. -/
theorem exists_uniform_lower {P : E → E →L[ℝ] E} {K : Set E}
    (hK : IsCompact K) (hP : ContinuousOn P K)
    (hpositive : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < ⟪v, P x v⟫_ℝ) :
    ∃ p > 0, ∀ x ∈ K, ∀ v : E, p * ‖v‖^2 ≤ ⟪v, P x v⟫_ℝ := by
  classical
  rcases subsingleton_or_nontrivial E with hE | hE
  · letI := hE
    refine ⟨1, zero_lt_one, ?_⟩
    intro x hx v
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv]
  · letI := hE
    by_cases hne : K.Nonempty
    · obtain ⟨x₀, hx₀⟩ := hne
      obtain ⟨w, hw⟩ := exists_norm_eq E (by norm_num : 0 ≤ (1:ℝ))
      let S : Set (E × E) := K ×ˢ sphere (0:E) 1
      let φ : E × E → ℝ := fun z => ⟪z.2, P z.1 z.2⟫_ℝ
      have hS : IsCompact S := hK.prod (isCompact_sphere (0:E) 1)
      have hSne : S.Nonempty := ⟨(x₀,w), hx₀, by simpa using hw⟩
      have hφ : ContinuousOn φ S :=
        continuousOn_snd.inner
          ((hP.comp continuousOn_fst (fun z hz => hz.1)).clm_apply continuousOn_snd)
      obtain ⟨z, hz, hzmin⟩ := hS.exists_isMinOn hSne hφ
      have hzunit : ‖z.2‖ = 1 := by simpa using hz.2
      have hznonzero : z.2 ≠ 0 := by intro hz0; simpa [hz0] using hzunit
      have hp : 0 < φ z := hpositive z.1 hz.1 z.2 hznonzero
      refine ⟨φ z, hp, ?_⟩
      intro x hx v
      by_cases hv : v = 0
      · simp [hv]
      · let u := (‖v‖⁻¹ : ℝ) • v
        have hu : u ∈ sphere (0:E) 1 := by
          simpa only [mem_sphere, dist_zero_right] using norm_smul_inv_norm (𝕜 := ℝ) hv
        have hunit : φ z ≤ φ (x,u) := hzmin ⟨hx,hu⟩
        have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
        calc
          φ z * ‖v‖^2 ≤ φ (x,u) * ‖v‖^2 := mul_le_mul_of_nonneg_right hunit (sq_nonneg _)
          _ = ⟪v, P x v⟫_ℝ := by
            dsimp [φ,u]
            rw [map_smul, inner_smul_left, inner_smul_right]
            simp only [conj_trivial]
            field_simp
    · refine ⟨1, zero_lt_one, ?_⟩
      intro x hx
      exact False.elim (hne ⟨x,hx⟩)

end Paper38.CompactEllipticity
