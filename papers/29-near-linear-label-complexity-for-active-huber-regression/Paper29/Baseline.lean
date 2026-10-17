import Paper29.Geometry

/-! The proper-subset baseline obstruction discussed in Remark 3.7/Section 5. -/
noncomputable section
namespace Paper29

/-- An omitted label can contribute a positive affine baseline while the
fixed weighted sampled objective is zero. This holds for every design A. -/
theorem omitted_label_baseline {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w : Fin n → ℝ) (i : Fin n) (hi : w i = 0) :
    ∃ b : Fin n → ℝ,
      weightedHuber w (A.mulVec 0 - b) = 0 ∧ objective A b 0 = 3 / 2 := by
  classical
  let b : Fin n → ℝ := fun j => if j = i then 2 else 0
  refine ⟨b, ?_, ?_⟩
  · unfold weightedHuber
    apply Finset.sum_eq_zero
    intro j _
    by_cases hji : j = i
    · subst j
      simp [hi]
    · simp [b, hji]
  · unfold objective
    rw [Finset.sum_eq_single i]
    · norm_num [b, huber, Matrix.mulVec_zero]
    · intro j _ hji
      simp [b, hji]
    · simp

/-- In particular, no multiplicative lower preservation with error <1 can
hold for all responses for any such fixed proper-subset weighted objective. -/
theorem omitted_label_not_strong_affine {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (i : Fin n) (hi : w i = 0) {ε : ℝ} (hε : ε < 1) :
    ∃ b : Fin n → ℝ,
      ¬ ((1 - ε) * objective A b 0 ≤ weightedHuber w (A.mulVec 0 - b)) := by
  obtain ⟨b, hsample, hfull⟩ := omitted_label_baseline A w i hi
  refine ⟨b, ?_⟩
  rw [hsample, hfull]
  linarith

end Paper29
