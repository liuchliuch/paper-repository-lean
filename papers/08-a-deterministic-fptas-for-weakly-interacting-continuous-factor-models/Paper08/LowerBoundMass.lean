import Paper08.LowerBoundGrid
import Paper08.Integral
import Mathlib.MeasureTheory.Integral.Pi

/-! # Actual Lebesgue masses of the grid fooling functions in Proposition B.1 -/
noncomputable section
open scoped Real BigOperators ENNReal
open MeasureTheory Set
namespace Paper08.LowerBound

lemma compactBump_support : Function.support compactBump ⊆ Ioo (0 : ℝ) 1 := by
  intro t ht
  by_contra hn
  exact ht (compactBump_eq_zero_of_not_mem_Ioo hn)

lemma compactBump_intervalIntegral : ∫ t in (0 : ℝ)..1, compactBump t = 8 / 15 := by
  calc
    _ = ∫ t in (0 : ℝ)..1, Appendix.bump t := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact compactBump_of_mem (by simpa using ht)
    _ = _ := bump_integral_eq

/-- A shifted, scaled bump has its genuine one-dimensional Lebesgue mass. -/
lemma compactBump_scaled_integral {L : ℕ} (hL : 0 < L) (z : Fin L) :
    (∫ t in Icc (0 : ℝ) 1, compactBump ((L : ℝ) * t - (z : ℝ))) =
      (8 / 15 : ℝ) / L := by
  have hL0 : (L : ℝ) ≠ 0 := by positivity
  have hz0 : 0 ≤ (z : ℝ) := by positivity
  have hz1 : (z : ℝ) + 1 ≤ L := by exact_mod_cast z.isLt
  have hs : Function.support compactBump ⊆ Ioc (-(z : ℝ)) ((L : ℝ) - z) := by
    intro t ht
    have ht := compactBump_support ht
    constructor <;> linarith [ht.1, ht.2]
  have hs0 : Function.support compactBump ⊆ Ioc (0 : ℝ) 1 :=
    fun t ht => ⟨(compactBump_support ht).1, (compactBump_support ht).2.le⟩
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [intervalIntegral.integral_comp_mul_sub compactBump hL0]
  simp only [mul_zero, zero_sub, mul_one, smul_eq_mul]
  rw [intervalIntegral.integral_eq_integral_of_support_subset hs,
    ← intervalIntegral.integral_eq_integral_of_support_subset hs0, compactBump_intervalIntegral]
  ring

/-- Fubini for all independent one-dimensional coordinates on the actual cube. -/
lemma cubeIntegral_coordinate_prod {r : ℕ} (f : Fin r → ℝ → ℝ) :
    Integral.cubeIntegral (fun x => ∏ j, f j (x j)) =
      ∏ j, ∫ t in Icc (0 : ℝ) 1, f j t := by
  unfold Integral.cubeIntegral Integral.cube
  change (∫ x, ∏ j, f j (x j) ∂((Measure.pi fun _ : Fin r => (volume : Measure ℝ)).restrict _)) = _
  rw [Measure.restrict_pi_pi]
  exact integral_fintype_prod_eq_prod f

/-- The mass assigned to `cellMass` is the actual `r`-dimensional cube integral. -/
theorem cubeIntegral_gridBump {r L : ℕ} (hL : 0 < L) (a : ℝ) (z : GridCell r L) :
    Integral.cubeIntegral (gridBump a z) = a * J r / (L : ℝ) ^ (r + 1) := by
  unfold gridBump Integral.cubeIntegral
  rw [integral_const_mul]
  change (a / L) * Integral.cubeIntegral
    (fun x : Fin r → ℝ => ∏ j, compactBump ((L : ℝ) * x j - (z j : ℝ))) = _
  rw [cubeIntegral_coordinate_prod (fun j t => compactBump ((L : ℝ) * t - (z j : ℝ)))]
  simp_rw [compactBump_scaled_integral hL]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow, J, pow_succ]
  ring

lemma abs_gridBump {r L : ℕ} (a : ℝ) (z : GridCell r L) (x : Fin r → ℝ) :
    |gridBump a z x| = gridBump |a| z x := by
  unfold gridBump
  have hp : 0 ≤ ∏ j, compactBump ((L : ℝ) * x j - (z j : ℝ)) :=
    Finset.prod_nonneg fun _ _ => compactBump_nonneg _
  rw [abs_mul, abs_div, abs_of_nonneg (show 0 ≤ (L : ℝ) from Nat.cast_nonneg L), abs_of_nonneg hp]

lemma integrableOn_gridBump {r L : ℕ} (a : ℝ) (z : GridCell r L) :
    IntegrableOn (gridBump a z) (Integral.cube r) := by
  apply Integral.integrableOn_cube_of_bound (contDiff_gridBump a z).continuous.measurable
  intro x _
  rw [abs_gridBump]
  exact gridBump_le (abs_nonneg a) z x

/-- The finite sum in the actual fooling function has the sum of the cell masses. -/
theorem cubeIntegral_foolingBump {r L : ℕ} (hL : 0 < L) (a : ℝ)
    (queries : Finset (Fin r → ℝ)) :
    Integral.cubeIntegral (foolingBump (L := L) a queries) =
      ((activeGridCells (L := L) queries).card : ℝ) *
        (a * J r / (L : ℝ) ^ (r + 1)) := by
  classical
  unfold foolingBump
  rw [Integral.cubeIntegral_sum _ (fun z _ => integrableOn_gridBump a z)]
  simp_rw [cubeIntegral_gridBump hL]
  simp

/-- At least half the grid cells are active, so the actual integral has (B.2)'s mass. -/
theorem cubeIntegral_foolingBump_ge {r L : ℕ} {a : ℝ} (hL : 0 < L) (ha : 0 ≤ a)
    (queries : Finset (Fin r → ℝ)) (hcount : 2 * queries.card ≤ L ^ r) :
    a * J r / (2 * L) ≤ Integral.cubeIntegral (foolingBump (L := L) a queries) := by
  have hcard := activeGridCells_card_ge (L := L) queries
  have hcard' : ((L ^ r - queries.card : ℕ) : ℝ) ≤
      ((activeGridCells (L := L) queries).card : ℝ) := by exact_mod_cast hcard
  have hmass := mass_from_unmarked a (J r) L queries.card r ha (J_pos r).le hL hcount
  rw [cubeIntegral_foolingBump hL]
  apply hmass.trans
  exact mul_le_mul_of_nonneg_right hcard' (cellMass_nonneg ha (J_pos r).le)

end Paper08.LowerBound
