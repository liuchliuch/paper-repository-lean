import BoundaryReduction.NinePoint
noncomputable section
open scoped BigOperators
namespace BoundaryReduction.NinePoint
noncomputable def baseProb : BoundaryReduction.FinProb (Fin 9) where
  w := p0
  nonneg := p0_nonneg
  sum_eq_one := p0_sum
noncomputable def mixtureProb (t : ℝ) : BoundaryReduction.FinProb (Fin 9) where
  w := Qt t
  nonneg := Qt_nonneg t
  sum_eq_one := Qt_sum t
lemma chiSq_eq_pieces (t : ℝ) :
    BoundaryReduction.FinProb.chiSq (mixtureProb t) baseProb =
    (Qt t 0 - ε)^2 / p0 0 +
      ∑ y : Fin 9, if y = 0 then 0 else (Qt t y - w)^2 / p0 y := by
  unfold BoundaryReduction.FinProb.chiSq mixtureProb baseProb
  rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ)
    (f := fun y => (Qt t y - p0 y)^2 / p0 y)
    (i := (0 : Fin 9)) (h := Finset.mem_univ _), sum_diff_eq_ite]
  congr 1
lemma chiSq_Q200_lt :
    BoundaryReduction.FinProb.chiSq (mixtureProb 200) baseProb <
      1.001 * 10 ^ (-15 : ℤ) := by
  rw [chiSq_eq_pieces]
  have htv : tvFin (Qt 200) U8 ≤ beta 200 := by
    simpa [beta] using Qt_U8_tv_le 200 (by norm_num)
  exact lt_of_le_of_lt (chiSq_upper_pieces 200 (by norm_num) htv) A4_numeric
lemma kl_Q200_lt :
    BoundaryReduction.FinProb.klPos (mixtureProb 200) baseProb <
      1.001 * 10 ^ (-15 : ℤ) := by
  have hkl : BoundaryReduction.FinProb.klPos (mixtureProb 200) baseProb ≤
      BoundaryReduction.FinProb.chiSq (mixtureProb 200) baseProb :=
    BoundaryReduction.FinProb.klPos_le_chiSq (fun y => p0_pos y)
  exact lt_of_le_of_lt hkl chiSq_Q200_lt
/-- Lemma A.1: the actual eight tilts at t=200 are exterior and their
uniform mixture has divergence below the stated explicit constant. -/
theorem lemma_A_1 :
    (∀ k : Fin 8, r₀ < ‖esMean (compPt 200 k)‖) ∧
    BoundaryReduction.FinProb.klPos (mixtureProb 200) baseProb <
      1.001 * 10 ^ (-15 : ℤ) := by
  exact ⟨exterior_200, kl_Q200_lt⟩
end BoundaryReduction.NinePoint
