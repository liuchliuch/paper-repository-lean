import PsgEst.Basic
import PsgEst.LaplacianOrder

/-!
# Normalized bipartite Laplacian (Section 3)

`H = [[I, -L], [-Lᵀ, I]]`, second-smallest eigenvalue `h = 1 - σ_2(L)`.
Empirical counterpart from counts, and the deterministic Rayleigh / min-max
comparison used in Proposition 1.

This module isolates the *deterministic* core of Proposition 1:
* the block structure of `H` and the identity of its quadratic form;
* eigenvectors of `H` arising from singular pairs of `L` (eigenvalues `1 ± σ`);
* the real-analysis implication `|ĥ - h| ≤ η(3h+τ)/(1-η)`;
* the Rayleigh-quotient min-max comparison under a scaling `T` with
  `(1-η)I ≼ T ≼ (1+η)I`;
* degree-normalization identities relating `Ĥ` to `H̄` via `T`.

We encode the bipartite index set as `Fin d ⊕ Fin d` so that `Matrix.fromBlocks`
gives the exact block shape `[[I, -L], [-Lᵀ, I]]`.
-/

open Matrix BigOperators Real

namespace PsgEst

variable {d : ℕ}

/-! ## 1. Block structure of `H = [[I, -L], [-Lᵀ, I]]` -/

/-- Bipartite Laplacian of a linear operator `L` on `Fin d`:
`H = [[I, -L], [-Lᵀ, I]]` acting on `Fin d ⊕ Fin d`. -/
def bipH (L : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ :=
  fromBlocks 1 (-L) (-Lᵀ) 1

@[simp]
theorem bipH_apply_inl_inl (L : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    bipH L (Sum.inl i) (Sum.inl j) = if i = j then (1 : ℝ) else 0 :=
  one_apply

@[simp]
theorem bipH_apply_inl_inr (L : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    bipH L (Sum.inl i) (Sum.inr j) = - L i j :=
  rfl

@[simp]
theorem bipH_apply_inr_inl (L : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    bipH L (Sum.inr i) (Sum.inl j) = - L j i :=
  rfl

@[simp]
theorem bipH_apply_inr_inr (L : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    bipH L (Sum.inr i) (Sum.inr j) = if i = j then (1 : ℝ) else 0 :=
  one_apply

/-- `H` is symmetric, hence self-adjoint for the real inner product. -/
theorem bipH_isHermitian (L : Matrix (Fin d) (Fin d) ℝ) : (bipH L).IsHermitian := by
  have h1 : (1 : Matrix (Fin d) (Fin d) ℝ).IsHermitian := by
    rw [IsHermitian]
    simp
  have hBC : ((-L : Matrix (Fin d) (Fin d) ℝ))ᴴ = -Lᵀ := by
    ext i j
    simp [conjTranspose, transpose]
  exact IsHermitian.fromBlocks h1 hBC h1

/-- Helper: `Sum.elim (c • u) (c • v) = c • Sum.elim u v` for vectors on `Fin d`. -/
theorem sumElim_smul (c : ℝ) (u v : Fin d → ℝ) :
    Sum.elim (c • u) (c • v) = c • Sum.elim u v := by
  funext i
  cases i with
  | inl j => simp [Sum.elim, Pi.smul_apply]
  | inr j => simp [Sum.elim, Pi.smul_apply]

/-- Action of `H` on a paired vector `(x, y)`:
`H (x, y) = (x - L y, y - Lᵀ x)`. -/
theorem bipH_mulVec (L : Matrix (Fin d) (Fin d) ℝ) (x y : Fin d → ℝ) :
    bipH L *ᵥ Sum.elim x y
      = Sum.elim (x - L *ᵥ y) (y - Lᵀ *ᵥ x) := by
  rw [bipH, fromBlocks_mulVec]
  have h1 : (Sum.elim x y) ∘ Sum.inl = x := rfl
  have h2 : (Sum.elim x y) ∘ Sum.inr = y := rfl
  rw [h1, h2]
  simp only [one_mulVec, neg_mulVec]
  have e1 : x + - (L *ᵥ y) = x - L *ᵥ y := (sub_eq_add_neg _ _).symm
  have e2 : - (Lᵀ *ᵥ x) + y = y - Lᵀ *ᵥ x := by
    rw [add_comm]; exact (sub_eq_add_neg _ _).symm
  rw [e1, e2]

/-- Helper: `x ⬝ᵥ (L *ᵥ y) = ∑ i, ∑ j, x i * L i j * y j`. -/
theorem dotProduct_mulVec_eq_sum (L : Matrix (Fin d) (Fin d) ℝ) (x y : Fin d → ℝ) :
    x ⬝ᵥ (L *ᵥ y) = ∑ i, ∑ j, x i * L i j * y j := by
  simp only [dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (L *ᵥ y) i = ∑ j, L i j * y j := by
    simp [mulVec, dotProduct]
  rw [hi, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Helper: `y ⬝ᵥ (Lᵀ *ᵥ x) = ∑ i, ∑ j, x i * L i j * y j`. -/
theorem dotProduct_transpose_mulVec_eq_sum (L : Matrix (Fin d) (Fin d) ℝ) (x y : Fin d → ℝ) :
    y ⬝ᵥ (Lᵀ *ᵥ x) = ∑ i, ∑ j, x i * L i j * y j := by
  have h : y ⬝ᵥ (Lᵀ *ᵥ x) = (Lᵀ *ᵥ x) ⬝ᵥ y := dotProduct_comm _ _
  rw [h]
  have hL : ∀ j, (Lᵀ *ᵥ x) j = ∑ i, L i j * x i := by
    intro j
    simp [mulVec, dotProduct, transpose]
  simp only [dotProduct]
  have key : ∑ j, (Lᵀ *ᵥ x) j * y j = ∑ j, (∑ i, L i j * x i) * y j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hL]
  rw [key]
  have key2 : ∑ j, (∑ i, L i j * x i) * y j
      = ∑ j, ∑ i, x i * L i j * y j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [key2, Finset.sum_comm]

/-- Helper: `x ⬝ᵥ x = ∑ i, x i ^ 2`. -/
theorem dotProduct_self_eq_sum_sq (x : Fin d → ℝ) : x ⬝ᵥ x = ∑ i, x i ^ 2 := by
  simp only [dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Quadratic form of `H` at `(x, y)`:
`⟨(x,y), H(x,y)⟩ = ‖x‖² + ‖y‖² - 2 xᵀ L y`. -/
theorem bipH_dotProduct (L : Matrix (Fin d) (Fin d) ℝ) (x y : Fin d → ℝ) :
    (Sum.elim x y) ⬝ᵥ (bipH L *ᵥ Sum.elim x y)
      = (∑ i, x i ^ 2) + (∑ i, y i ^ 2) - 2 * ∑ i, ∑ j, x i * L i j * y j := by
  rw [bipH_mulVec, sumElim_dotProduct_sumElim]
  have hA : x ⬝ᵥ (x - L *ᵥ y) = x ⬝ᵥ x - x ⬝ᵥ (L *ᵥ y) := dotProduct_sub _ _ _
  have hB : y ⬝ᵥ (y - Lᵀ *ᵥ x) = y ⬝ᵥ y - y ⬝ᵥ (Lᵀ *ᵥ x) := dotProduct_sub _ _ _
  rw [hA, hB, dotProduct_self_eq_sum_sq, dotProduct_self_eq_sum_sq,
    dotProduct_mulVec_eq_sum, dotProduct_transpose_mulVec_eq_sum]
  ring

/-- Special case `L = 0`: `H` is the identity on `Fin d ⊕ Fin d`. -/
theorem bipH_zero : bipH (0 : Matrix (Fin d) (Fin d) ℝ) = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [bipH, fromBlocks, one_apply]

/-- If `(u, v)` is a singular pair of `L` with singular value `σ`
(`L v = σ u`, `Lᵀ u = σ v`), then `(u, v)` is an eigenvector of `H` with eigenvalue `1 - σ`,
and `(u, -v)` is an eigenvector with eigenvalue `1 + σ`.

This is the structural source of the identity "eigenvalues of `H` are `1 ± σ_j(L)`",
hence the second-smallest eigenvalue is `h = 1 - σ_2(L)` (when `σ_1 = 1`). -/
theorem bipH_eigenvector_of_singPair (L : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (σ : ℝ)
    (hLu : L *ᵥ v = σ • u) (hLTu : Lᵀ *ᵥ u = σ • v) :
    bipH L *ᵥ Sum.elim u v = (1 - σ) • Sum.elim u v
    ∧ bipH L *ᵥ Sum.elim u (- v) = (1 + σ) • Sum.elim u (- v) := by
  constructor
  · rw [bipH_mulVec, hLu, hLTu]
    have h1 : u - σ • u = (1 - σ) • u := by
      rw [sub_smul, one_smul]
    have h2 : v - σ • v = (1 - σ) • v := by
      rw [sub_smul, one_smul]
    rw [h1, h2, sumElim_smul]
  · have hLv' : L *ᵥ (- v) = - (σ • u) := by
      rw [mulVec_neg, hLu]
    have hLT' : Lᵀ *ᵥ u = σ • v := hLTu
    rw [bipH_mulVec, hLv', hLT']
    have h1 : u - - (σ • u) = (1 + σ) • u := by
      rw [sub_neg_eq_add, add_smul, one_smul]
    have h2 : - v - σ • v = (1 + σ) • (- v) := by
      ext i
      simp [smul_eq_mul, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply]
      ring
    rw [h1, h2, sumElim_smul]

/-- Rayleigh identity: the Rayleigh numerator of `H` at `(x, y)` equals
`‖x‖² + ‖y‖² - 2 xᵀ L y`. In particular, on the unit sphere this is `1 - 2 xᵀ L y`. -/
theorem bipH_rayleigh (L : Matrix (Fin d) (Fin d) ℝ) (x y : Fin d → ℝ)
    (hnorm : (∑ i, x i ^ 2) + (∑ i, y i ^ 2) = 1) :
    (Sum.elim x y) ⬝ᵥ (bipH L *ᵥ Sum.elim x y)
      = 1 - 2 * ∑ i, ∑ j, x i * L i j * y j := by
  rw [bipH_dotProduct, hnorm]

/-- Unnormalized Rayleigh numerator at a singular pair: if `L v = σ • v` and `‖v‖ = 1`,
then `(v, v)` has Rayleigh numerator `2(1 - σ)` and `(v, -v)` has numerator `2(1 + σ)`;
the corresponding Rayleigh quotients (dividing by `‖(v,±v)‖² = 2`) are `1 ∓ σ`. -/
theorem bipH_rayleigh_singPair (L : Matrix (Fin d) (Fin d) ℝ)
    (v : Fin d → ℝ) (σ : ℝ)
    (hLv : L *ᵥ v = σ • v) (hnorm : ∑ i, v i ^ 2 = 1) :
    (Sum.elim v v) ⬝ᵥ (bipH L *ᵥ Sum.elim v v) = 2 * (1 - σ)
    ∧ (Sum.elim v (- v)) ⬝ᵥ (bipH L *ᵥ Sum.elim v (- v)) = 2 * (1 + σ) := by
  have hcross : ∑ i, ∑ j, v i * L i j * v j = σ := by
    have key : v ⬝ᵥ (L *ᵥ v) = σ := by
      rw [hLv, dotProduct_smul, dotProduct_self_eq_sum_sq, hnorm, smul_eq_mul]
      ring
    rw [← dotProduct_mulVec_eq_sum]
    exact key
  have hcross_neg : ∑ i, ∑ j, v i * L i j * (- v) j = - σ := by
    have h : ∑ i, ∑ j, v i * L i j * (- v) j
        = - ∑ i, ∑ j, v i * L i j * v j := by
      simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    rw [h, hcross]
  have hnorm2 : (∑ i, v i ^ 2) + (∑ i, v i ^ 2) = 2 := by
    rw [hnorm]; ring
  have hnorm3 : (∑ i, v i ^ 2) + (∑ i, (- v) i ^ 2) = 2 := by
    have : (fun i => (- v) i ^ 2) = fun i => v i ^ 2 := by
      funext i
      simp only [Pi.neg_apply]
      ring
    rw [this, hnorm]; ring
  constructor
  · rw [bipH_dotProduct, hnorm2, hcross]
    ring
  · rw [bipH_dotProduct, hnorm3, hcross_neg]
    ring

/-! ## 2. Deterministic core of Proposition 1 -/

/-- From the two-sided bound `(1-2η)H - ητ I ≼ H̄ ≼ (1+2η)H + ητ I` and the min-max
comparison under `T`, the empirical second-smallest eigenvalue `ĥ` satisfies
`((1-2η)h - ητ)/(1+η) ≤ ĥ ≤ ((1+2η)h + ητ)/(1-η)`.

This is the real-analysis packaging of the paper's display after (19): the eigenvalue
of `H̄` sits in `[(1-2η)h - ητ, (1+2η)h + ητ]`, and the min-max comparison divides
by `1+η` / `1-η` respectively. -/
theorem bounds_of_eig_interval (h hbar hhat τ η : ℝ)
    (hη : 0 < η) (hη' : η < 1) (_hτ : 0 < τ) (_hh : 0 ≤ h)
    (hbar_lo : (1 - 2 * η) * h - η * τ ≤ hbar)
    (hbar_hi : hbar ≤ (1 + 2 * η) * h + η * τ)
    (hminmax_lo : hbar / (1 + η) ≤ hhat)
    (hminmax_hi : hhat ≤ hbar / (1 - η)) :
    ((1 - 2 * η) * h - η * τ) / (1 + η) ≤ hhat
    ∧ hhat ≤ ((1 + 2 * η) * h + η * τ) / (1 - η) := by
  have hden1 : 0 < 1 - η := by linarith
  have hden2 : 0 < 1 + η := by linarith
  constructor
  · have step1 : ((1 - 2 * η) * h - η * τ) / (1 + η) ≤ hbar / (1 + η) :=
      div_le_div_of_nonneg_right hbar_lo (le_of_lt hden2)
    exact le_trans step1 hminmax_lo
  · have step1 : hbar / (1 - η) ≤ ((1 + 2 * η) * h + η * τ) / (1 - η) :=
      div_le_div_of_nonneg_right hbar_hi (le_of_lt hden1)
    exact le_trans hminmax_hi step1

/-- **Deterministic core of Proposition 1.**
Given
`((1-2η)h - ητ)/(1+η) ≤ ĥ ≤ ((1+2η)h + ητ)/(1-η)`,
conclude `|ĥ - h| ≤ η(3h+τ)/(1-η)`.

This is pure real analysis: subtract `h` from both sides. The upper deficit is exactly
`(3η h + ητ)/(1-η)`; the lower deficit is `(3η h + ητ)/(1+η)`, which is smaller.
No upper bound `h ≤ 1` is required. -/
theorem prop1_deterministic (h τ η hhat : ℝ)
    (hη : 0 < η) (hη' : η ≤ 1 / 4) (hτ : 0 < τ) (hh : 0 ≤ h)
    (hlo : ((1 - 2 * η) * h - η * τ) / (1 + η) ≤ hhat)
    (hhi : hhat ≤ ((1 + 2 * η) * h + η * τ) / (1 - η)) :
    |hhat - h| ≤ η * (3 * h + τ) / (1 - η) := by
  have hη1 : η < 1 := by linarith
  have hden1 : 0 < 1 - η := by linarith
  have hden2 : 0 < 1 + η := by linarith
  have h3 : 0 ≤ 3 * h + τ := by linarith
  have hηn : 0 ≤ η := le_of_lt hη
  rw [abs_le]
  constructor
  · -- lower side: h - hhat ≤ η(3h+τ)/(1-η)
    have A : (1 - 2 * η) * h - η * τ ≤ hhat * (1 + η) := by
      have := hlo
      rwa [div_le_iff₀ hden2] at this
    have B : (h - hhat) * (1 + η) ≤ η * (3 * h + τ) := by
      nlinarith
    have C : h - hhat ≤ η * (3 * h + τ) / (1 + η) :=
      (le_div_iff₀ hden2).mpr B
    have D : η * (3 * h + τ) / (1 + η) ≤ η * (3 * h + τ) / (1 - η) :=
      div_le_div_of_nonneg_left (by nlinarith) hden1 (by linarith)
    linarith [le_trans C D]
  · -- upper side: hhat - h ≤ η(3h+τ)/(1-η)
    have A : hhat * (1 - η) ≤ (1 + 2 * η) * h + η * τ :=
      (le_div_iff₀ hden1).mp hhi
    have B : (hhat - h) * (1 - η) ≤ η * (3 * h + τ) := by
      nlinarith
    exact (le_div_iff₀ hden1).mpr B

/-- Same conclusion under the parameter range `0 < η < 1`, `τ > 0`, `h ≥ 0`
(the proof only uses `η < 1`, not `η ≤ 1/4`). -/
theorem prop1_deterministic' (h τ η hhat : ℝ)
    (hη : 0 < η) (hη' : η < 1) (hτ : 0 < τ) (hh : 0 ≤ h)
    (hlo : ((1 - 2 * η) * h - η * τ) / (1 + η) ≤ hhat)
    (hhi : hhat ≤ ((1 + 2 * η) * h + η * τ) / (1 - η)) :
    |hhat - h| ≤ η * (3 * h + τ) / (1 - η) := by
  have hden1 : 0 < 1 - η := by linarith
  have hden2 : 0 < 1 + η := by linarith
  have h3 : 0 ≤ 3 * h + τ := by linarith
  have hηn : 0 ≤ η := le_of_lt hη
  rw [abs_le]
  constructor
  · have A : (1 - 2 * η) * h - η * τ ≤ hhat * (1 + η) := by
      have := hlo
      rwa [div_le_iff₀ hden2] at this
    have B : (h - hhat) * (1 + η) ≤ η * (3 * h + τ) := by
      nlinarith
    have C : h - hhat ≤ η * (3 * h + τ) / (1 + η) :=
      (le_div_iff₀ hden2).mpr B
    have D : η * (3 * h + τ) / (1 + η) ≤ η * (3 * h + τ) / (1 - η) :=
      div_le_div_of_nonneg_left (by nlinarith) hden1 (by linarith)
    linarith [le_trans C D]
  · have A : hhat * (1 - η) ≤ (1 + 2 * η) * h + η * τ :=
      (le_div_iff₀ hden1).mp hhi
    have B : (hhat - h) * (1 - η) ≤ η * (3 * h + τ) := by
      nlinarith
    exact (le_div_iff₀ hden1).mpr B

/-- The full deterministic pipeline of Proposition 1, assembled from
(1) the eigenvalue interval produced by `(1-2η)H - ητ I ≼ H̄ ≼ (1+2η)H + ητ I`;
(2) the min-max comparison under `T`;
(3) the real-analysis implication.

This is the statement whose probabilistic hypotheses (degree event + martingale bound)
are external to this module. -/
theorem prop1_deterministic_pipeline (h τ η hhat hbar : ℝ)
    (hη : 0 < η) (hη' : η ≤ 1 / 4) (hτ : 0 < τ) (hh : 0 ≤ h)
    (hbar_lo : (1 - 2 * η) * h - η * τ ≤ hbar)
    (hbar_hi : hbar ≤ (1 + 2 * η) * h + η * τ)
    (hminmax_lo : hbar / (1 + η) ≤ hhat)
    (hminmax_hi : hhat ≤ hbar / (1 - η)) :
    |hhat - h| ≤ η * (3 * h + τ) / (1 - η) := by
  have hη1 : η < 1 := by linarith
  obtain ⟨hlo, hhi⟩ := bounds_of_eig_interval h hbar hhat τ η hη hη1 hτ hh
    hbar_lo hbar_hi hminmax_lo hminmax_hi
  exact prop1_deterministic h τ η hhat hη hη' hτ hh hlo hhi

/-! ## 3. Min-max comparison under a scaling `T` -/

/-- Rayleigh-quotient form of the min-max comparison (the analytic core of the paper's
argument after (19)).

If `(1-η) ‖x‖² ≤ xᵀ T x ≤ (1+η) ‖x‖²` and `xᵀ H̄ x ≥ 0`, then for every nonzero `x`
the generalized Rayleigh quotient `xᵀ H̄ x / xᵀ T x` is sandwiched between the ordinary
Rayleigh quotients of `H̄` scaled by `1/(1+η)` and `1/(1-η)`. -/
theorem rayleigh_scale (n : ℕ) (Hbar T : Matrix (Fin n) (Fin n) ℝ)
    (η : ℝ) (_hη : 0 ≤ η) (hη' : η < 1)
    (hT : ∀ x : Fin n → ℝ,
      (1 - η) * ∑ i, x i ^ 2 ≤ ∑ i, (T *ᵥ x) i * x i
        ∧ ∑ i, (T *ᵥ x) i * x i ≤ (1 + η) * ∑ i, x i ^ 2)
    (hpsd : ∀ x : Fin n → ℝ, 0 ≤ ∑ i, (Hbar *ᵥ x) i * x i)
    (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 ≠ 0) :
    (∑ i, (Hbar *ᵥ x) i * x i) / ((1 + η) * ∑ i, x i ^ 2)
      ≤ (∑ i, (Hbar *ᵥ x) i * x i) / (∑ i, (T *ᵥ x) i * x i)
    ∧ (∑ i, (Hbar *ᵥ x) i * x i) / (∑ i, (T *ᵥ x) i * x i)
      ≤ (∑ i, (Hbar *ᵥ x) i * x i) / ((1 - η) * ∑ i, x i ^ 2) := by
  have hTlo := (hT x).1
  have hThi := (hT x).2
  have hnorm' : 0 < ∑ i, x i ^ 2 := by
    by_contra h
    push_neg at h
    have : ∑ i, x i ^ 2 = 0 := le_antisymm h (Finset.sum_nonneg fun i _ => sq_nonneg (x i))
    exact hx this
  have hTpos : 0 < ∑ i, (T *ᵥ x) i * x i :=
    lt_of_lt_of_le (mul_pos (by linarith : (0:ℝ) < 1 - η) hnorm') hTlo
  have hq : 0 ≤ ∑ i, (Hbar *ᵥ x) i * x i := hpsd x
  constructor
  · -- q / ((1+η)‖x‖²) ≤ q / (xᵀ T x)
    by_cases hq0 : ∑ i, (Hbar *ᵥ x) i * x i = 0
    · rw [hq0, zero_div, zero_div]
    · exact div_le_div_of_nonneg_left hq hTpos hThi
  · -- q / (xᵀ T x) ≤ q / ((1-η)‖x‖²)
    by_cases hq0 : ∑ i, (Hbar *ᵥ x) i * x i = 0
    · rw [hq0, zero_div, zero_div]
    · have den_le : 0 < (1 - η) * ∑ i, x i ^ 2 := mul_pos (by linarith) hnorm'
      exact div_le_div_of_nonneg_left hq den_le hTlo

/-- **Min-max under `T`, Rayleigh form** (alias). -/
theorem minmax_rayleigh (n : ℕ) (Hbar T : Matrix (Fin n) (Fin n) ℝ)
    (η : ℝ) (hη : 0 ≤ η) (hη' : η < 1)
    (hT : ∀ x : Fin n → ℝ,
      (1 - η) * ∑ i, x i ^ 2 ≤ ∑ i, (T *ᵥ x) i * x i
        ∧ ∑ i, (T *ᵥ x) i * x i ≤ (1 + η) * ∑ i, x i ^ 2)
    (hpsd : ∀ x : Fin n → ℝ, 0 ≤ ∑ i, (Hbar *ᵥ x) i * x i)
    (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 ≠ 0) :
    (∑ i, (Hbar *ᵥ x) i * x i) / ((1 + η) * ∑ i, x i ^ 2)
      ≤ (∑ i, (Hbar *ᵥ x) i * x i) / (∑ i, (T *ᵥ x) i * x i)
    ∧ (∑ i, (Hbar *ᵥ x) i * x i) / (∑ i, (T *ᵥ x) i * x i)
      ≤ (∑ i, (Hbar *ᵥ x) i * x i) / ((1 - η) * ∑ i, x i ^ 2) :=
  rayleigh_scale n Hbar T η hη hη' hT hpsd x hx

/-- Eigenvalue-level min-max comparison, in the form used in Proposition 1:
`λ_j(H̄)/(1+η) ≤ λ_j(Ĥ) ≤ λ_j(H̄)/(1-η)`.

Stated for abstract scalars representing the relevant eigenvalues of `H̄` and
`Ĥ = T^{-1/2} H̄ T^{-1/2}`; the real content is the Rayleigh sandwich `minmax_rayleigh`
plus the Courant–Fischer min-max principle. We package the numerical inequality
that the paper carries forward, with the comparison hypotheses explicit. -/
theorem minmax_scale (eigHbar eigHHat : ℝ) (η : ℝ)
    (_hη : 0 < η) (_hη' : η < 1)
    (hcmp_lo : eigHbar / (1 + η) ≤ eigHHat)
    (hcmp_hi : eigHHat ≤ eigHbar / (1 - η)) :
    eigHbar / (1 + η) ≤ eigHHat ∧ eigHHat ≤ eigHbar / (1 - η) :=
  ⟨hcmp_lo, hcmp_hi⟩

/-- Pointwise Rayleigh sandwich (the content transferred by the Courant–Fischer
min-max principle to each eigenvalue). -/
theorem rayleigh_scale_pointwise (n : ℕ) (Hbar T : Matrix (Fin n) (Fin n) ℝ)
    (η : ℝ) (hη : 0 ≤ η) (hη' : η < 1)
    (hT : ∀ x : Fin n → ℝ,
      (1 - η) * ∑ i, x i ^ 2 ≤ ∑ i, (T *ᵥ x) i * x i
        ∧ ∑ i, (T *ᵥ x) i * x i ≤ (1 + η) * ∑ i, x i ^ 2)
    (hpsd : ∀ x : Fin n → ℝ, 0 ≤ ∑ i, (Hbar *ᵥ x) i * x i)
    (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 ≠ 0) :
    (∑ i, (Hbar *ᵥ x) i * x i) / ((1 + η) * ∑ i, x i ^ 2)
      ≤ (∑ i, (Hbar *ᵥ x) i * x i) / (∑ i, (T *ᵥ x) i * x i)
    ∧ (∑ i, (Hbar *ᵥ x) i * x i) / (∑ i, (T *ᵥ x) i * x i)
      ≤ (∑ i, (Hbar *ᵥ x) i * x i) / ((1 - η) * ∑ i, x i ^ 2) :=
  rayleigh_scale n Hbar T η hη hη' hT hpsd x hx

/-! ## 4. Degree normalization and weighted Cauchy -/

/-- Scaling matrix `T = diag(t_i)` associated to degree normalization. -/
def scaleT (n : ℕ) (t : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal t

/-- Degree event `E`: every normalized degree lies within `(1±η)` of its stationary mass. -/
def degEvent {n : ℕ} (w : Fin n → ℝ) (μ : Fin n → ℝ) (η : ℝ) : Prop :=
  ∀ i, (1 - η) * μ i ≤ w i ∧ w i ≤ (1 + η) * μ i

/-- On the degree event, the diagonal scaling `T = diag(w_i / μ_i)` satisfies
`(1-η)I ≼ T ≼ (1+η)I` in the quadratic-form sense. -/
theorem scaleT_bounds_of_degEvent {n : ℕ} (w μ : Fin n → ℝ) (η : ℝ)
    (hμ : ∀ i, 0 < μ i)
    (hE : degEvent w μ η) (_hη : 0 ≤ η) (_hη' : η < 1) :
    ∀ x : Fin n → ℝ,
      (1 - η) * ∑ i, x i ^ 2
        ≤ ∑ i, ((scaleT n (fun i => w i / μ i)) *ᵥ x) i * x i
      ∧ ∑ i, ((scaleT n (fun i => w i / μ i)) *ᵥ x) i * x i
        ≤ (1 + η) * ∑ i, x i ^ 2 := by
  intro x
  have hdiag : ∀ i, ((scaleT n (fun i => w i / μ i)) *ᵥ x) i = (w i / μ i) * x i := by
    intro i
    simp [scaleT, mulVec_diagonal]
  constructor
  · have : ∀ i, (1 - η) * x i ^ 2 ≤ (w i / μ i) * x i ^ 2 := by
      intro i
      have hdiv := (hE i).1
      have hp := hμ i
      have hdiv' : (1 - η) ≤ w i / μ i := (le_div_iff₀ hp).mpr hdiv
      exact mul_le_mul_of_nonneg_right hdiv' (sq_nonneg _)
    calc (1 - η) * ∑ i, x i ^ 2
        = ∑ i, (1 - η) * x i ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ∑ i, (w i / μ i) * x i ^ 2 := Finset.sum_le_sum fun i _ => this i
      _ = ∑ i, ((scaleT n (fun i => w i / μ i)) *ᵥ x) i * x i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hdiag]
          ring
  · have : ∀ i, (w i / μ i) * x i ^ 2 ≤ (1 + η) * x i ^ 2 := by
      intro i
      have hdiv := (hE i).2
      have hp := hμ i
      have hdiv' : w i / μ i ≤ (1 + η) := (div_le_iff₀ hp).mpr hdiv
      exact mul_le_mul_of_nonneg_right hdiv' (sq_nonneg _)
    calc ∑ i, ((scaleT n (fun i => w i / μ i)) *ᵥ x) i * x i
        = ∑ i, (w i / μ i) * x i ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hdiag]
          ring
      _ ≤ ∑ i, (1 + η) * x i ^ 2 := Finset.sum_le_sum fun i _ => this i
      _ = (1 + η) * ∑ i, x i ^ 2 := by rw [Finset.mul_sum]

/-- Unweighted Cauchy–Schwarz for sums (special case of `Finset.sum_mul_sq_le_sq_mul_sq`). -/
theorem sum_cauchy_schwarz (n : ℕ) (x y : Fin n → ℝ) :
    (∑ i, x i * y i) ^ 2 ≤ (∑ i, x i ^ 2) * (∑ i, y i ^ 2) :=
  Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y

/-- Weighted Cauchy–Schwarz in the form used for the degree normalization:
for positive weights `t_i` and any vectors `x, y`,
`|∑ x_i y_i| ≤ √(∑ t_i x_i²) · √(∑ y_i² / t_i)`. -/
theorem weighted_cauchy_sqrt (n : ℕ) (t x y : Fin n → ℝ)
    (ht : ∀ i, 0 < t i) :
    |∑ i, x i * y i| ≤
      (Real.sqrt (∑ i, t i * x i ^ 2)) * (Real.sqrt (∑ i, y i ^ 2 / t i)) := by
  -- u_i = √t_i x_i, v_i = y_i/√t_i; then u_i v_i = x_i y_i, u_i² = t_i x_i², v_i² = y_i²/t_i
  have hA : (∑ i, (Real.sqrt (t i) * x i) ^ 2) = ∑ i, t i * x i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    have hp := ht i
    rw [mul_pow, Real.sq_sqrt (le_of_lt hp)]
  have hB : (∑ i, (y i / Real.sqrt (t i)) ^ 2) = ∑ i, y i ^ 2 / t i := by
    apply Finset.sum_congr rfl
    intro i _
    have hp := ht i
    rw [div_pow, Real.sq_sqrt (le_of_lt hp)]
  have hC : (∑ i, (Real.sqrt (t i) * x i) * (y i / Real.sqrt (t i))) = ∑ i, x i * y i := by
    apply Finset.sum_congr rfl
    intro i _
    have hp := ht i
    have hs : 0 < Real.sqrt (t i) := Real.sqrt_pos.mpr hp
    have hs0 : Real.sqrt (t i) ≠ 0 := ne_of_gt hs
    field_simp [hs0]
  have hpos1 : 0 ≤ ∑ i, t i * x i ^ 2 := Finset.sum_nonneg fun i _ =>
    mul_nonneg (le_of_lt (ht i)) (sq_nonneg _)
  have hcs : (∑ i, (Real.sqrt (t i) * x i) * (y i / Real.sqrt (t i))) ^ 2
      ≤ (∑ i, (Real.sqrt (t i) * x i) ^ 2) * (∑ i, (y i / Real.sqrt (t i)) ^ 2) :=
    sum_cauchy_schwarz n (fun i => Real.sqrt (t i) * x i) (fun i => y i / Real.sqrt (t i))
  rw [hA, hB, hC] at hcs
  have hsqrt : Real.sqrt ((∑ i, t i * x i ^ 2) * (∑ i, y i ^ 2 / t i))
      = Real.sqrt (∑ i, t i * x i ^ 2) * Real.sqrt (∑ i, y i ^ 2 / t i) :=
    Real.sqrt_mul hpos1 _
  rw [← hsqrt]
  exact Real.abs_le_sqrt hcs

/-- The deterministic matrix step of Proposition 1, with no eigenvalue
comparison in its hypotheses. The quadratic Loewner bounds (19), positivity,
and the degree bounds imply the perturbation estimate for every ordered
eigenvalue of the actual normalized matrix. At the second-smallest index this
is the comparison used in the paper. -/
theorem prop1_deterministic_of_matrix_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H Hbar : Matrix ι ι ℝ) (hH : H.IsHermitian) (hHbar : Hbar.IsHermitian)
    (τ η : ℝ) (hη : 0 < η) (hη' : η ≤ 1 / 4) (hτ : 0 < τ)
    (hHpsd : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (H *ᵥ x))
    (hbarpsd : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (Hbar *ᵥ x))
    (hlo : ∀ x : ι → ℝ,
      (1 - 2 * η) * (x ⬝ᵥ (H *ᵥ x)) - η * τ * (x ⬝ᵥ x) ≤
        x ⬝ᵥ (Hbar *ᵥ x))
    (hhi : ∀ x : ι → ℝ,
      x ⬝ᵥ (Hbar *ᵥ x) ≤
        (1 + 2 * η) * (x ⬝ᵥ (H *ᵥ x)) + η * τ * (x ⬝ᵥ x))
    (t : ι → ℝ) (hT : ∀ i, 1 - η ≤ t i ∧ t i ≤ 1 + η)
    (j : Fin (Fintype.card ι)) :
    |(diagonalNormalize_isHermitian Hbar hHbar t).eigenvalues₀ j - hH.eigenvalues₀ j| ≤
      η * (3 * hH.eigenvalues₀ j + τ) / (1 - η) := by
  have hη1 : η < 1 := by linarith
  have ht : ∀ i, 0 < t i := fun i => lt_of_lt_of_le (by linarith) (hT i).1
  have hbar_lo : (1 - 2 * η) * hH.eigenvalues₀ j - η * τ ≤ hHbar.eigenvalues₀ j := by
    have hcmp := matrix_ordered_affine_comparison H Hbar hH hHbar
      (1 - 2 * η) (-(η * τ)) 1 0 (by linarith) zero_le_one
      (by intro x; simpa only [one_mul, zero_mul, add_zero, neg_mul,
        ← sub_eq_add_neg] using hlo x) j
    simpa only [one_mul, add_zero, ← sub_eq_add_neg] using hcmp
  have hbar_hi : hHbar.eigenvalues₀ j ≤ (1 + 2 * η) * hH.eigenvalues₀ j + η * τ := by
    simpa only [one_mul, add_zero] using
      matrix_ordered_affine_comparison Hbar H hHbar hH 1 0
        (1 + 2 * η) (η * τ) zero_le_one (by linarith)
        (by intro x; simpa only [one_mul, zero_mul, add_zero] using hhi x) j
  have hscale := matrix_ordered_diagonal_scaling Hbar hHbar t ht η hη.le hη1
    hbarpsd hT j
  exact prop1_deterministic_pipeline (hH.eigenvalues₀ j) τ η
    ((diagonalNormalize_isHermitian Hbar hHbar t).eigenvalues₀ j)
    (hHbar.eigenvalues₀ j) hη hη' hτ (matrix_ordered_nonneg H hH hHpsd j)
    hbar_lo hbar_hi hscale.1 hscale.2

end PsgEst
