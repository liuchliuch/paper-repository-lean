import Paper18.Category.RelativeTensorDimensionBasic

/-! # The regular vector under an actual dominant fusion-rule map -/
noncomputable section
open Classical
open scoped BigOperators
universe u v
namespace Paper18.Category
namespace DominantDimension
variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
  {U : FusionBasis ι} {V : FusionBasis κ} (F : FusionMap U V)

/-- The actual transpose multiplicity vector weighted by source FP dimensions. -/
def transposeDimension (j : κ) : ℝ := ∑ i, (F.imageCoeff i j : ℝ) * U.fpdim i

lemma transposeDimension_pos (j : κ) : 0 < transposeDimension F j := by
  obtain ⟨i, hi⟩ := F.dominant j
  exact Finset.sum_pos' (fun i _ =>
    mul_nonneg (Nat.cast_nonneg _) (U.fpdim_pos i).le)
    ⟨i, Finset.mem_univ _, mul_pos (by exact_mod_cast hi) (U.fpdim_pos i)⟩

lemma transposeDimension_action
    (hdual : ∀ i j, F.imageCoeff (U.dual i) j = F.imageCoeff i (V.dual j))
    (i : ι) (j : κ) :
    ∑ a, (F.imageCoeff i a : ℝ) *
      (∑ k, (V.N j a k : ℝ) * transposeDimension F k) =
        U.fpdim i * transposeDimension F j := by
  have hd (k : κ) :
      ∑ a, (F.imageCoeff i a : ℝ) * (V.N j a k : ℝ) =
        ∑ a, (F.imageCoeff (U.dual i) a : ℝ) * (V.N k a j : ℝ) := by
    calc
      _ = ∑ a, (F.imageCoeff i (V.dual a) : ℝ) * (V.N j (V.dual a) k : ℝ) :=
        (Equiv.sum_comp (Equiv.ofBijective V.dual V.dual_bijective) _).symm
      _ = _ := by simp only [← hdual, V.N_right j, V.dual_involutive]
  calc
    _ = ∑ l, U.fpdim l * (∑ k, (F.imageCoeff l k : ℝ) *
        (∑ a, (F.imageCoeff i a : ℝ) * (V.N j a k : ℝ))) := by
      simp only [transposeDimension, Finset.mul_sum]
      conv_lhs =>
        rw [Finset.sum_comm]
        arg 2
        ext k
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ l, U.fpdim l * (∑ k, (F.imageCoeff l k : ℝ) *
        (∑ a, (F.imageCoeff (U.dual i) a : ℝ) * (V.N k a j : ℝ))) := by
      simp_rw [hd]
    _ = ∑ l, U.fpdim l *
        (∑ z, (U.N l (U.dual i) z : ℝ) * (F.imageCoeff z j : ℝ)) := by
      apply Finset.sum_congr rfl
      intro l _
      congr 1
      simp only [Finset.mul_sum, ← mul_assoc]
      exact (F.toFusionRuleMap.tensor_coeff_real l (U.dual i) j).symm
    _ = ∑ z, (F.imageCoeff z j : ℝ) *
        (∑ l, (U.N z i l : ℝ) * U.fpdim l) := by
      have hn (l z : ι) : U.N l (U.dual i) z = U.N z i l := by
        rw [U.N_right, U.dual_involutive]
      simp only [Finset.mul_sum, hn]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by
      simp_rw [U.fpdim_mul]
      simp only [transposeDimension, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring

/-- Dominance and the actual tensor/dual multiplicities force the image of
the regular vector to be the target regular vector with one scalar. -/
lemma transposeDimension_eq
    (hdual : ∀ i j, F.imageCoeff (U.dual i) j = F.imageCoeff i (V.dual j)) (j : κ) :
    transposeDimension F j = transposeDimension F V.one * V.fpdim j :=
  RelativeTensor.dominant_action_dimension_unique F (transposeDimension F)
    (transposeDimension_pos F) (transposeDimension_action F hdual) j

/-- The dimension quotient of an actual dominant tensor multiplicity map is
derived from its unit multiplicities, without a dimension-law field. -/
lemma totalFPdim_eq
    (hdual : ∀ i j, F.imageCoeff (U.dual i) j = F.imageCoeff i (V.dual j)) :
    U.totalFPdim = transposeDimension F V.one * V.totalFPdim := by
  calc
    _ = ∑ j, transposeDimension F j * V.fpdim j := by
      simp only [transposeDimension, Finset.sum_mul]
      rw [Finset.sum_comm]
      change (∑ i, U.fpdim i ^ 2) = _
      apply Finset.sum_congr rfl
      intro i _
      change U.fpdim i ^ 2 = _
      calc
        _ = U.fpdim i * (∑ j, (F.imageCoeff i j : ℝ) * V.fpdim j) := by
          rw [F.fpdim_preserved]
          ring
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = _ := by
      change _ = transposeDimension F V.one * ∑ j, V.fpdim j ^ 2
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [transposeDimension_eq F hdual j]
      ring

end DominantDimension
end Paper18.Category
