import Paper18.Fusion.TensorFunctor

/-! # Dimension uniqueness for actual dominant module actions

This finite-matrix lemma uses the already proved positive eigenspace
theorem. Dominance and fusion reciprocity make the action matrix strictly
positive; no proportionality or dimension formula is assumed.
-/
noncomputable section
open Classical
open scoped BigOperators
universe u v
namespace Paper18.Category.RelativeTensor

/-- A positive dimension vector for a dominant right fusion action is
uniquely determined by its value on the target unit. -/
theorem dominant_action_dimension_unique
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    {U : FusionBasis ι} {V : FusionBasis κ} (F : FusionMap U V)
    (r : κ → ℝ) (hr : ∀ j, 0 < r j)
    (hact : ∀ i j, ∑ a, (F.imageCoeff i a : ℝ) *
      (∑ k, (V.N j a k : ℝ) * r k) = U.fpdim i * r j) :
    ∀ j, r j = r V.one * V.fpdim j := by
  letI : Nonempty κ := ⟨V.one⟩
  let B : Matrix κ κ ℝ := fun j k =>
    ∑ i, ∑ a, (F.imageCoeff i a : ℝ) * (V.N j a k : ℝ)
  have hB (j k : κ) : 0 < B j k := by
    obtain ⟨a, ha⟩ := V.exists_constituent (V.dual j) k
    have hn : 0 < V.N j a k := by rwa [V.N_dual]
    obtain ⟨i, hi⟩ := F.dominant a
    apply Finset.sum_pos' (fun i _ => Finset.sum_nonneg (fun a _ =>
      mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    exact ⟨i, Finset.mem_univ _, Finset.sum_pos'
      (fun a _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      ⟨a, Finset.mem_univ _, mul_pos (by exact_mod_cast hi) (by exact_mod_cast hn)⟩⟩
  have rearrange (s : κ → ℝ) (j : κ) :
      ∑ k, B j k * s k = ∑ i, ∑ a, (F.imageCoeff i a : ℝ) *
        (∑ k, (V.N j a k : ℝ) * s k) := by
    simp only [B, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  have hR (j : κ) : ∑ k, B j k * r k = (∑ i, U.fpdim i) * r j := by
    rw [rearrange]
    simp_rw [hact]
    exact (Finset.sum_mul _ _ _).symm
  have hE (j : κ) : ∑ k, B j k * V.fpdim k =
      (∑ i, U.fpdim i) * V.fpdim j := by
    rw [rearrange]
    simp_rw [V.fpdim_mul]
    calc
      _ = ∑ i, (∑ a, (F.imageCoeff i a : ℝ) * V.fpdim a) * V.fpdim j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = _ := by simp_rw [F.fpdim_preserved]; exact (Finset.sum_mul _ _ _).symm
  obtain ⟨c, _, hc⟩ := posMatrix_positive_eigenspace_one_dim B _ hB r V.fpdim
    hr V.fpdim_pos hR hE
  have hu := hc V.one
  simp only [V.fpdim_one, mul_one] at hu
  intro j
  rw [hc j, ← hu]

end Paper18.Category.RelativeTensor
