import PUT.Basic

/-!
# Fourier–Dirichlet adversary operator

Paper 24, (7): `Γ = ∑_n α(k(n)) |e_n⟩⟨f_n|` with `α(k) = (A - ∑ k_i²)₊`.

The weight `α` is the quadratic cutoff of `PUT.Basic`.  On the orthonormal
families `{e_n}` and `{f_n}` the operator `Γ` has norm `A` and satisfies
`Γ 1 = A · 1`: the constant latent function sits in the zero Fourier sector,
where `α(0) = A`, and every other weight is at most `A`.  Finite rank is the
statement `α(k) = 0` whenever `R(k) ≥ A`.
-/

noncomputable section
set_option linter.unusedVariables false
namespace PUT

/-- The quadratic cutoff weight of a Fourier index. -/
def gammaWeight {d M : ℕ} (A : ℝ) (n : PhaseIndex d M) : ℝ :=
  cutoff A (degreeOf n)

/-- The zero Fourier index `n = 0`, whose degree vector vanishes. -/
def zeroPhase {d M : ℕ} : PhaseIndex d M := fun _ _ => 0

@[simp] theorem zeroPhase_apply {d M : ℕ} (i : Fin d) (j : Fin M) :
    zeroPhase (d := d) (M := M) i j = 0 := rfl

theorem labelDegree_zero {d M : ℕ} (i : Fin d) :
    labelDegree (zeroPhase (d := d) (M := M)) i = 0 := by
  unfold labelDegree
  simp [zeroPhase]

theorem degreeOf_zero {d M : ℕ} :
    degreeOf (zeroPhase (d := d) (M := M)) = fun _ => 0 := by
  funext i
  exact labelDegree_zero i

/-! ### Cutoff support and upper bound -/

/-- Finite support: `α(k) = 0` whenever `R(k) ≥ A`. -/
theorem cutoff_finite_support {d : ℕ} (A : ℝ) (k : Fin d → ℕ)
    (h : A ≤ ∑ i, (k i : ℝ) ^ 2) : cutoff A k = 0 := by
  unfold cutoff
  have : A - ∑ i, (k i : ℝ) ^ 2 ≤ 0 := by linarith
  exact max_eq_right this

/-- The same statement phrased with `R(k) = ∑ k_i²`. -/
theorem cutoff_finite_support_degR {d : ℕ} (A : ℝ) (k : Fin d → ℕ)
    (h : A ≤ (degR k : ℝ)) : cutoff A k = 0 := by
  apply cutoff_finite_support
  rwa [degR_coe] at h

/-- `α` is always at most `max A 0`. -/
theorem cutoff_le_max (A : ℝ) {d : ℕ} (k : Fin d → ℕ) :
    cutoff A k ≤ max A 0 := by
  unfold cutoff
  have h : (0:ℝ) ≤ ∑ i, (k i : ℝ) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h2 : A - ∑ i, (k i : ℝ) ^ 2 ≤ A := by linarith
  exact max_le_max h2 le_rfl

/-- When `A ≥ 0` the weight is at most `A`. -/
theorem cutoff_le_of_nonneg' {d : ℕ} {A : ℝ} (hA : 0 ≤ A) (k : Fin d → ℕ) :
    cutoff A k ≤ A := by
  have := cutoff_le_max A k
  rwa [max_eq_left hA] at this

/-! ### The weight on Fourier indices -/

theorem gammaWeight_eq (A : ℝ) {d M : ℕ} (n : PhaseIndex d M) :
    gammaWeight A n = cutoff A (degreeOf n) := rfl

/-- Every weight is at most `A` when `A ≥ 0`. -/
theorem gammaWeight_le {d M : ℕ} (A : ℝ) (n : PhaseIndex d M) (hA : 0 ≤ A) :
    gammaWeight A n ≤ A :=
  cutoff_le_of_nonneg' hA (degreeOf n)

/-- On the zero Fourier index the weight is exactly `A` (for `A ≥ 0`). -/
theorem gammaWeight_zero {d M : ℕ} (A : ℝ) (hA : 0 ≤ A) :
    gammaWeight A (zeroPhase (d := d) (M := M)) = A := by
  have hsum : (∑ i : Fin d, (((fun _ : Fin d => (0 : ℕ)) i : ℕ) : ℝ) ^ (2 : ℕ)) = 0 := by
    simp
  unfold gammaWeight
  rw [degreeOf_zero]
  show cutoff A (fun _ : Fin d => (0 : ℕ)) = _
  unfold cutoff
  rw [hsum, sub_zero]
  exact max_eq_left hA

/-- `Γ 1 = A · 1` at the level of the orthonormal family: the constant latent
function is the zero Fourier mode `e_0`, and `Γ` acts on it by `α(0) = A`. -/
theorem gamma_on_constant {d M : ℕ} (A : ℝ) (hA : 0 ≤ A) :
    gammaWeight A (zeroPhase (d := d) (M := M)) = A :=
  gammaWeight_zero A hA

/-- `‖Γ‖ = A` on the orthonormal family `{e_n}`, `{f_n}`: the weights lie in
`[0,A]` and attain `A` at the zero mode, so `sup_n α(k(n)) = A`. -/
theorem gammaWeight_sup_eq {d M : ℕ} (A : ℝ) (hA : 0 ≤ A) :
    sSup (Set.range (gammaWeight (d := d) (M := M) A)) = A := by
  have hne : (Set.range (gammaWeight (d := d) (M := M) A)).Nonempty :=
    ⟨gammaWeight A zeroPhase, ⟨zeroPhase, rfl⟩⟩
  have hbdd : BddAbove (Set.range (gammaWeight (d := d) (M := M) A)) :=
    ⟨A, fun x hx => by
      obtain ⟨n, rfl⟩ := hx
      exact gammaWeight_le A n hA⟩
  apply le_antisymm
  · refine csSup_le hne ?_
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact gammaWeight_le A n hA
  · exact le_csSup hbdd ⟨zeroPhase, gammaWeight_zero A hA⟩

/-- Combined norm characterization of (7): `sup α = A` and `α(0) = A`. -/
theorem gamma_norm_eq {d M : ℕ} (A : ℝ) (hA : 0 ≤ A) :
    gammaWeight A (zeroPhase (d := d) (M := M)) = A
      ∧ (∀ n : PhaseIndex d M, gammaWeight A n ≤ A)
      ∧ sSup (Set.range (gammaWeight (d := d) (M := M) A)) = A :=
  ⟨gammaWeight_zero A hA, fun n => gammaWeight_le A n hA, gammaWeight_sup_eq A hA⟩

/-- Finite rank of `Γ`: only degrees with `R(k) < A` carry nonzero weight.
Since `R(k)` is a natural number, at most finitely many degree vectors in
`Fin d` contribute. -/
theorem gamma_finite_rank {d M : ℕ} (A : ℝ) (n : PhaseIndex d M)
    (h : A ≤ (degR (degreeOf n) : ℝ)) : gammaWeight A n = 0 :=
  cutoff_finite_support_degR A (degreeOf n) h

end PUT
