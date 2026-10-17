import Paper28.L2Reindex
import Paper28.FiniteTranslates

/-! Matrix coefficients of the actual left regular l2 representation vanish
at infinity. Finite-support cancellation and the approximation error estimate
are both proved here; the decay is not an external action/properness input. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter
open scoped InnerProductSpace Topology
variable {G : Type*} [Group G] [DecidableEq G]

theorem regular_inner_error (γ : G) (u u' v v' : CoordinateHilbert G) :
    |⟪u,leftRegular γ v⟫_ℝ - ⟪u',leftRegular γ v'⟫_ℝ| ≤
      ‖u-u'‖*‖v‖ + ‖u'‖*‖v-v'‖ := by
  have he : ⟪u,leftRegular γ v⟫_ℝ - ⟪u',leftRegular γ v'⟫_ℝ =
      ⟪u-u',leftRegular γ v⟫_ℝ + ⟪u',leftRegular γ (v-v')⟫_ℝ := by
    rw [inner_sub_left, map_sub, inner_sub_right]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add
    (by simpa only [(leftRegular γ).norm_map] using abs_real_inner_le_norm (u-u') (leftRegular γ v))
    (by simpa only [(leftRegular γ).norm_map] using abs_real_inner_le_norm u' (leftRegular γ (v-v'))))

/-- All finite-coordinate coefficients vanish outside the exact finite
translation-overlap set F * E^{-1}, uniformly in the vector values. -/
theorem regular_projected_inner_zero (F E : Finset G) (γ : G)
    (hγ : γ ∉ overlapTranslations F E) (u v : CoordinateHilbert G) :
    ⟪l2CoordinateProjection F u, leftRegular γ (l2CoordinateProjection E v)⟫_ℝ = 0 := by
  rw [lp.inner_eq_tsum]
  trans ∑' _g : G, (0 : ℝ)
  · apply tsum_congr
    intro g
    by_cases hg : g ∈ F
    · have hge : γ⁻¹*g ∉ E := by
        intro he
        apply hγ
        apply (mem_overlapTranslations F E γ).mpr
        exact ⟨g,hg,γ⁻¹*g,he,by simp [mul_assoc]⟩
      simp [leftRegular_apply, l2CoordinateProjection_apply, hge]
    · simp [l2CoordinateProjection_apply, hg]
  · exact tsum_zero

theorem regular_inner_eventually_small (u v : CoordinateHilbert G) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ γ in Filter.cofinite, |⟪u,leftRegular γ v⟫_ℝ| < ε := by
  let δ := ε / (‖u‖+‖v‖+1)
  have hden : 0 < ‖u‖+‖v‖+1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨F,hF⟩ := exists_l2CoordinateProjection_close u δ hδ
  obtain ⟨E,hE⟩ := exists_l2CoordinateProjection_close v δ hδ
  have hstrict : δ*(‖u‖+‖v‖) < ε := by
    have he : δ*(‖u‖+‖v‖+1) = ε := div_mul_cancel₀ ε (ne_of_gt hden)
    nlinarith
  apply Filter.mem_of_superset (Finset.finite_toSet (overlapTranslations F E)).compl_mem_cofinite
  intro γ hγ
  have hzero := regular_projected_inner_zero F E γ hγ u v
  have he := regular_inner_error γ u (l2CoordinateProjection F u) v (l2CoordinateProjection E v)
  rw [hzero, sub_zero] at he
  have hu : ‖u-l2CoordinateProjection F u‖ ≤ δ := by rw [norm_sub_rev]; exact hF.le
  have hv : ‖v-l2CoordinateProjection E v‖ ≤ δ := by rw [norm_sub_rev]; exact hE.le
  calc
    _ ≤ ‖u-l2CoordinateProjection F u‖*‖v‖ + ‖l2CoordinateProjection F u‖*‖v-l2CoordinateProjection E v‖ := he
    _ ≤ δ*‖v‖ + ‖u‖*δ := add_le_add
      (mul_le_mul_of_nonneg_right hu (norm_nonneg v))
      (mul_le_mul (l2CoordinateProjection_norm_le F u) hv (norm_nonneg _) (norm_nonneg u))
    _ = δ*(‖u‖+‖v‖) := by ring
    _ < ε := hstrict

/-- The matrix-coefficient decay used to construct finite-isotropy charts. -/
theorem regular_inner_tendsto_zero (u v : CoordinateHilbert G) :
    Tendsto (fun γ : G => ⟪u,leftRegular γ v⟫_ℝ) Filter.cofinite (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  simpa only [Real.dist_eq, sub_zero] using regular_inner_eventually_small u v ε hε

end Paper28
