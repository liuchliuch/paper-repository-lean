import Paper10.Symm

noncomputable section
open Matrix
namespace Paper10
abbrev Upper (q : ℕ) := {p : Fin q × Fin q // p.1 < p.2}

/-- Standard Frobenius coordinates, with off-diagonal normalization 1/√2. -/
def standardF (q : ℕ) : (Fin q ⊕ Upper q) → Matrix (Fin q) (Fin q) ℝ
  | Sum.inl i => eii i
  | Sum.inr p => eijSymm p.1.1 p.1.2

theorem frob_eii {q : ℕ} (U : Matrix (Fin q) (Fin q) ℝ) (i : Fin q) :
    frob U (eii i) = U i i := by rw [eii_eq_single, frob_single, one_mul]

theorem frob_eijSymm {q : ℕ} (U : Matrix (Fin q) (Fin q) ℝ) (hU : U.IsSymm)
    (i j : Fin q) (hij : i ≠ j) : frob U (eijSymm i j) = Real.sqrt 2 * U i j := by
  rw [eijSymm_eq_single i j hij]
  unfold frob
  rw [Matrix.mul_add, Matrix.trace_add]
  change frob U (Matrix.single i j (1 / Real.sqrt 2)) +
    frob U (Matrix.single j i (1 / Real.sqrt 2)) = _
  rw [frob_single, frob_single, ← hU.apply i j, ← add_mul]
  have hs : (1 / Real.sqrt 2 : ℝ) + 1 / Real.sqrt 2 = Real.sqrt 2 := by
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hs]

/-- The standard coordinate family is orthonormal. -/
theorem standardF_inner (q : ℕ) (a b : Fin q ⊕ Upper q) :
    frob (standardF q a) (standardF q b) = if a = b then 1 else 0 := by
  rcases a with i | p <;> rcases b with j | r
  · simp [standardF, frob_eii, eii, eq_comm]
  · rw [standardF, standardF, frob_eijSymm _ (eii_isymm i) _ _ (ne_of_lt r.2)]
    have hh : ¬(r.1.1 = i ∧ r.1.2 = i) := by have := r.2; grind
    simp [eii, hh]
  · rw [standardF, standardF, frob_eii]
    have hh : ¬((j = p.1.1 ∧ j = p.1.2) ∨ (j = p.1.2 ∧ j = p.1.1)) := by
      have := p.2; grind
    simp [eijSymm, hh]
  · rw [standardF, standardF, frob_eijSymm _ (eijSymm_isymm _ _) _ _ (ne_of_lt r.2)]
    by_cases hpr : p = r
    · subst r
      simp [eijSymm, mul_div_cancel₀, Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]
    · have hh : ¬((r.1.1 = p.1.1 ∧ r.1.2 = p.1.2) ∨
          (r.1.1 = p.1.2 ∧ r.1.2 = p.1.1)) := by
        have hp := p.2
        have hr := r.2
        intro hc
        rcases hc with hc | hc
        · apply hpr
          apply Subtype.ext
          exact Prod.ext hc.1.symm hc.2.symm
        · grind
      simp [eijSymm, hh, hpr]

/-- Off-diagonal reconstruction in the standard symmetric coordinates. -/
theorem sum_off_reconstruct {q : ℕ} (U : Matrix (Fin q) (Fin q) ℝ) (hU : U.IsSymm)
    (a b : Fin q) :
    (∑ p : Upper q, (Real.sqrt 2 * U p.1.1 p.1.2) • eijSymm p.1.1 p.1.2) a b =
      if a = b then 0 else U a b := by
  classical
  rw [Matrix.sum_apply]
  have hterm : ∀ p : Upper q, ((Real.sqrt 2 * U p.1.1 p.1.2) • eijSymm p.1.1 p.1.2) a b =
      if (a = p.1.1 ∧ b = p.1.2) ∨ (a = p.1.2 ∧ b = p.1.1) then U p.1.1 p.1.2 else 0 := by
    intro p
    simp only [Matrix.smul_apply, smul_eq_mul, eijSymm]
    split_ifs <;> field_simp <;> ring
  simp_rw [hterm]
  by_cases hab : a = b
  · subst b
    have hh : ∀ p : Upper q, ¬((a = p.1.1 ∧ a = p.1.2) ∨ (a = p.1.2 ∧ a = p.1.1)) := by
      intro p
      have := p.2
      grind
    simp [hh]
  · rw [if_neg hab]
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · let p0 : Upper q := ⟨(a, b), hlt⟩
      rw [Finset.sum_eq_single p0]
      · simp [p0]
      · intro p _ hp
        have hh : ¬((a = p.1.1 ∧ b = p.1.2) ∨ (a = p.1.2 ∧ b = p.1.1)) := by
          intro hc
          rcases hc with hc | hc
          · apply hp
            apply Subtype.ext
            exact Prod.ext hc.1.symm hc.2.symm
          · have := p.2; grind
        simp [hh]
      · intro hh
        exact False.elim (hh (Finset.mem_univ p0))
    · let p0 : Upper q := ⟨(b, a), hgt⟩
      rw [Finset.sum_eq_single p0]
      · simp [p0, show U b a = U a b from hU.apply a b]
      · intro p _ hp
        have hh : ¬((a = p.1.1 ∧ b = p.1.2) ∨ (a = p.1.2 ∧ b = p.1.1)) := by
          intro hc
          rcases hc with hc | hc
          · have := p.2; grind
          · apply hp
            apply Subtype.ext
            exact Prod.ext hc.2.symm hc.1.symm
        simp [hh]
      · intro hh
        exact False.elim (hh (Finset.mem_univ p0))

/-- A concrete complete orthonormal basis exists at every matrix order. -/
theorem standardF_orthonormal (q : ℕ) : OrthonormalFrob (standardF q) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rcases a with i | p
    · exact eii_isymm i
    · exact eijSymm_isymm _ _
  · intro a b
    by_cases hab : a = b <;> simpa [hab] using standardF_inner q a b
  · intro U hU
    refine ⟨Sum.elim (fun i => U i i) (fun p => Real.sqrt 2 * U p.1.1 p.1.2), ?_⟩
    rw [Fintype.sum_sum_type]
    ext a b
    simp only [standardF, Sum.elim_inl, Sum.elim_inr, Matrix.add_apply]
    rw [sum_off_reconstruct U hU a b, Matrix.sum_apply]
    by_cases hab : a = b
    · subst b
      simp [Matrix.smul_apply, eii, eq_comm]
    · have hh : ∀ i, ¬(a = i ∧ b = i) := by grind
      simp [Matrix.smul_apply, eii, hab, hh]

end Paper10
