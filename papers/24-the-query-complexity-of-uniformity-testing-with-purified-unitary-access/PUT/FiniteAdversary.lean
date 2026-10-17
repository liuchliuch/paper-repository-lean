import PUT.Adversary
import PUT.FiniteRankOperator

noncomputable section

namespace PUT.FiniteAdversary

/-- The Fourier indices on which the paper's quadratic cutoff is nonzero. -/
def support (d M : ℕ) (A : ℝ) : Set (PhaseIndex d M) :=
  {n | gammaWeight A n ≠ 0}

/-- Every individual frequency is bounded by the squared label degree sum. -/
theorem frequency_le_degree {d M : ℕ} (n : PhaseIndex d M)
    (i : Fin d) (j : Fin M) : (n i j).natAbs ≤ degR (degreeOf n) := by
  have h₁ : (n i j).natAbs ≤ labelDegree n i := by
    unfold labelDegree
    exact Finset.single_le_sum (fun t _ => Nat.zero_le ((n i t).natAbs)) (Finset.mem_univ j)
  have h₂ : labelDegree n i ≤ (labelDegree n i) ^ 2 := by
    simpa [pow_two] using Nat.le_mul_self (labelDegree n i)
  have h₃ : (labelDegree n i) ^ 2 ≤ degR (degreeOf n) :=
    Finset.single_le_sum (fun t _ => Nat.zero_le ((labelDegree n t) ^ 2)) (Finset.mem_univ i)
  exact h₁.trans (h₂.trans h₃)

/-- Unlike a mere cutoff-vanishing assertion, this proves that the actual set
of nonzero Fourier coefficients is finite. -/
theorem support_finite (d M : ℕ) (A : ℝ) : (support d M A).Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt A
  have hb : ({n : PhaseIndex d M | ∀ i j, n i j ∈
      Set.Icc (-(N : ℤ)) (N : ℤ)} : Set (PhaseIndex d M)).Finite := by
    exact Set.Finite.pi' (fun _ => Set.Finite.pi' (fun _ => Set.finite_Icc _ _))
  apply hb.subset
  intro n hn i j
  have hR : (degR (degreeOf n) : ℝ) < A := by
    by_contra h
    exact hn (gamma_finite_rank A n (le_of_not_gt h))
  have hrN : degR (degreeOf n) ≤ N := by exact_mod_cast (hR.trans hN).le
  have hij : (n i j).natAbs ≤ N := (frequency_le_degree n i j).trans hrN
  exact ⟨by omega, by omega⟩

/-- The actual finite-rank Fourier-weighted map, given the two required
orthonormal families. Their L² construction is a separate source obligation. -/
def gamma {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {d M : ℕ} (A : ℝ) (e : PhaseIndex d M → E) (f : PhaseIndex d M → F) : F →L[ℂ] E :=
  operator (support_finite d M A).toFinset (gammaWeight A) e f

theorem gamma_on_zero {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {d M : ℕ} (A : ℝ) (hA : 0 < A) (e : PhaseIndex d M → E) (f : PhaseIndex d M → F)
    (hf : Orthonormal ℂ f) :
    gamma A e f (f zeroPhase) = (A : ℂ) • e zeroPhase := by
  have hz : zeroPhase (d := d) (M := M) ∈ (support_finite d M A).toFinset := by
    simp only [Set.Finite.mem_toFinset, support, Set.mem_setOf_eq,
      gammaWeight_zero A hA.le, ne_eq]
    exact hA.ne'
  rw [gamma, operator_on_family _ _ _ _ hf hz, gammaWeight_zero A hA.le]

theorem gamma_norm {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {d M : ℕ} (A : ℝ) (hA : 0 < A) (e : PhaseIndex d M → E) (f : PhaseIndex d M → F)
    (he : Orthonormal ℂ e) (hf : Orthonormal ℂ f) : ‖gamma A e f‖ = A := by
  have hz : zeroPhase (d := d) (M := M) ∈ (support_finite d M A).toFinset := by
    simp only [Set.Finite.mem_toFinset, support, Set.mem_setOf_eq,
      gammaWeight_zero A hA.le, ne_eq]
    exact hA.ne'
  apply norm_operator_eq _ _ _ _ he hf A hA.le ?_ hz (gammaWeight_zero A hA.le)
  intro n _
  change |cutoff A (degreeOf n)| ≤ A
  rw [abs_of_nonneg (cutoff_nonneg _ _)]
  exact gammaWeight_le A n hA.le

end PUT.FiniteAdversary
