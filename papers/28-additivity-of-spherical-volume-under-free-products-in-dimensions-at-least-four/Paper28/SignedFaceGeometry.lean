import Paper28.SignedBarycentricStabilizers

/-! Unit norms, finite coordinate support and a common hemisphere for
actual signed face barycenters. All computations are in the native l2
Hilbert space and its actual coordinate support subspaces. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped Classical InnerProductSpace
variable {G : Type*} [Group G] [DecidableEq G]

theorem signedFaceCenter_unit (A F : Finset G) (hF : F.Nonempty) : ‖signedFaceCenter A F‖ = 1 :=
  sphericalNormalize_norm _ (signedFaceVector_ne_zero A F hF)

theorem signedFaceVector_mem_coordinates (A F E : Finset G) (hFE : F ⊆ E) :
    signedFaceVector A F ∈ coordinateSupportSubspace E := by
  intro g hg
  rw [signedFaceVector_apply,if_neg (fun h => hg (hFE h))]

theorem signedFaceCenter_mem_coordinates (A F E : Finset G) (hFE : F ⊆ E) :
    signedFaceCenter A F ∈ coordinateSupportSubspace E :=
  (coordinateSupportSubspace E).smul_mem _ (signedFaceVector_mem_coordinates A F E hFE)

theorem signedFaceVector_inner (A E F : Finset G) (hFE : F ⊆ E) :
    inner ℝ (signedFaceVector A E) (signedFaceVector A F) = (F.card : ℝ) := by
  change inner ℝ (signedFaceVector A E) (∑ g ∈ F, lp.single 2 g (coordinateSign A g)) = _
  rw [inner_sum]
  calc
    _ = ∑ g ∈ F, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [lp.inner_single_right,signedFaceVector_apply,if_pos (hFE hg)]
      unfold coordinateSign
      split_ifs <;> norm_num
    _ = _ := by simp

theorem signedFaceCenter_hemisphere (A E F : Finset G) (hFE : F ⊆ E) (hF : F.Nonempty) :
    0 < inner ℝ (signedFaceVector A E) (signedFaceCenter A F) := by
  change 0 < inner ℝ (signedFaceVector A E) (‖signedFaceVector A F‖⁻¹ • signedFaceVector A F)
  rw [real_inner_smul_right,signedFaceVector_inner A E F hFE]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr (signedFaceVector_ne_zero A F hF)))
    (by exact_mod_cast Finset.card_pos.mpr hF)

end Paper28
