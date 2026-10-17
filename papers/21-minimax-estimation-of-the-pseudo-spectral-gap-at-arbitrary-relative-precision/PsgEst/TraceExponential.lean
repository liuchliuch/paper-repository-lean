import PsgEst.LaplacianOrder
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog
import Mathlib.Data.Real.StarOrdered

/-! Actual finite real matrix exponentials and the deterministic trace-Laplace
foundations. This module does not assume Lieb concavity or a matrix martingale
inequality. All functional-calculus expressions below are tied to the actual
power-series matrix exponential. -/

open Matrix BigOperators Real

namespace PsgEst

section SpectralFunctions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {A : Matrix ι ι ℝ}

/-- Functional calculus in an actual orthogonal diagonalization. -/
noncomputable def spectralMap (hA : A.IsHermitian) (f : ℝ → ℝ) : Matrix ι ι ℝ :=
  (hA.eigenvectorUnitary : Matrix ι ι ℝ) * Matrix.diagonal (fun i => f (hA.eigenvalues i)) *
    star (hA.eigenvectorUnitary : Matrix ι ι ℝ)

theorem spectralMap_congr (hA : A.IsHermitian) (f g : ℝ → ℝ)
    (hfg : ∀ i, f (hA.eigenvalues i) = g (hA.eigenvalues i)) :
    spectralMap hA f = spectralMap hA g := by
  exact congrArg (fun d : ι → ℝ => (hA.eigenvectorUnitary : Matrix ι ι ℝ) *
    Matrix.diagonal d * star (hA.eigenvectorUnitary : Matrix ι ι ℝ)) (funext hfg)

private theorem spectralUnitary_inv (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix ι ι ℝ)⁻¹ = star (hA.eigenvectorUnitary : Matrix ι ι ℝ) :=
  Matrix.inv_eq_left_inv (unitary.coe_star_mul_self _)

theorem spectralMap_id (hA : A.IsHermitian) : spectralMap hA id = A := by
  simpa only [spectralMap, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using hA.spectral_theorem.symm

theorem spectralMap_one (hA : A.IsHermitian) : spectralMap hA (fun _ => 1) = 1 := by
  simp [spectralMap, Matrix.diagonal_one]

theorem spectralMap_add (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    spectralMap hA (fun x => f x + g x) = spectralMap hA f + spectralMap hA g := by
  have hd : Matrix.diagonal (fun i => f (hA.eigenvalues i) + g (hA.eigenvalues i)) =
      (Matrix.diagonal (fun i => f (hA.eigenvalues i)) +
        Matrix.diagonal (fun i => g (hA.eigenvalues i)) : Matrix ι ι ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  unfold spectralMap
  rw [hd, Matrix.mul_add, Matrix.add_mul]

theorem spectralMap_smul (hA : A.IsHermitian) (c : ℝ) (f : ℝ → ℝ) :
    spectralMap hA (fun x => c * f x) = c • spectralMap hA f := by
  change (hA.eigenvectorUnitary : Matrix ι ι ℝ) *
    Matrix.diagonal (c • (fun i => f (hA.eigenvalues i))) * _ = _
  rw [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
  rfl

theorem spectralMap_mul (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    spectralMap hA f * spectralMap hA g = spectralMap hA (fun x => f x * g x) := by
  unfold spectralMap
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star (hA.eigenvectorUnitary : Matrix ι ι ℝ)),
    unitary.coe_star_mul_self, Matrix.one_mul]
  rw [← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]

/-- Spectral functional calculus commutes with the actual matrix inverse
whenever its finite diagonal entries are nonzero. -/
theorem spectralMap_inv (hA : A.IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ i, f (hA.eigenvalues i) ≠ 0) :
    (spectralMap hA f)⁻¹ = spectralMap hA (fun x => (f x)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [spectralMap_mul]
  rw [spectralMap_congr hA _ (fun _ => 1) (fun i => inv_mul_cancel₀ (hf i))]
  exact spectralMap_one hA

theorem spectralMap_isHermitian (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (spectralMap hA f).IsHermitian := by
  apply Matrix.isHermitian_mul_mul_conjTranspose
  exact Matrix.isHermitian_diagonal_of_self_adjoint _ (IsSelfAdjoint.all _)

theorem spectralMap_nonneg (hA : A.IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ i, 0 ≤ f (hA.eigenvalues i)) : (spectralMap hA f).PosSemidef := by
  exact (Matrix.PosSemidef.diagonal hf).mul_mul_conjTranspose_same _

theorem spectralMap_posDef (hA : A.IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ i, 0 < f (hA.eigenvalues i)) : (spectralMap hA f).PosDef := by
  apply (Matrix.PosDef.diagonal hf).mul_mul_conjTranspose_same
  exact Matrix.vecMul_injective_iff_isUnit.mpr (unitary.toUnits hA.eigenvectorUnitary).isUnit

theorem spectralMap_sub (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    spectralMap hA (fun x => f x - g x) = spectralMap hA f - spectralMap hA g := by
  have hd : Matrix.diagonal (fun i => f (hA.eigenvalues i) - g (hA.eigenvalues i)) =
      (Matrix.diagonal (fun i => f (hA.eigenvalues i)) -
        Matrix.diagonal (fun i => g (hA.eigenvalues i)) : Matrix ι ι ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  unfold spectralMap
  rw [hd, Matrix.mul_sub, Matrix.sub_mul]

/-- Scalar order on the actual eigenvalues lifts to quadratic matrix order. -/
theorem spectralMap_mono (hA : A.IsHermitian) (f g : ℝ → ℝ)
    (hfg : ∀ i, f (hA.eigenvalues i) ≤ g (hA.eigenvalues i)) :
    (spectralMap hA g - spectralMap hA f).PosSemidef := by
  rw [← spectralMap_sub]
  exact spectralMap_nonneg hA _ (fun i => sub_nonneg.mpr (hfg i))

/-- Spectral functional calculus of the actual power-series exponential. -/
theorem exp_spectralMap (hA : A.IsHermitian) (f : ℝ → ℝ) :
    NormedSpace.exp ℝ (spectralMap hA f) = spectralMap hA (fun x => Real.exp (f x)) := by
  have hu : IsUnit (hA.eigenvectorUnitary : Matrix ι ι ℝ) :=
    (unitary.toUnits hA.eigenvectorUnitary).isUnit
  have he := Matrix.exp_conj ℝ (hA.eigenvectorUnitary : Matrix ι ι ℝ)
    (Matrix.diagonal (fun i => f (hA.eigenvalues i))) hu
  simpa only [spectralUnitary_inv, Matrix.exp_diagonal, Pi.exp_def,
    ← Real.exp_eq_exp_ℝ, spectralMap] using he

theorem matrixExp_eq_spectralMap (hA : A.IsHermitian) :
    NormedSpace.exp ℝ A = spectralMap hA Real.exp := by
  simpa only [spectralMap_id, id_eq] using exp_spectralMap hA id

/-- The exponential of a finite real self-adjoint matrix is positive definite. -/
theorem matrixExp_posDef (hA : A.IsHermitian) : (NormedSpace.exp ℝ A).PosDef := by
  rw [matrixExp_eq_spectralMap hA]
  exact spectralMap_posDef hA _ (fun i => Real.exp_pos _)

/-- The true trace of a spectral function. -/
theorem trace_spectralMap (hA : A.IsHermitian) (f : ℝ → ℝ) :
    Matrix.trace (spectralMap hA f) = ∑ i, f (hA.eigenvalues i) := by
  unfold spectralMap
  rw [Matrix.trace_mul_cycle, unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]

end SpectralFunctions

/-- The trace of the actual power-series matrix exponential. -/
noncomputable def traceExp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : ℝ := Matrix.trace (NormedSpace.exp ℝ A)

section TraceLaplace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {A B : Matrix ι ι ℝ}

theorem traceExp_eq_sum_eigenvalues (hA : A.IsHermitian) :
    traceExp A = ∑ i, Real.exp (hA.eigenvalues i) := by
  rw [traceExp, matrixExp_eq_spectralMap hA, trace_spectralMap]

theorem traceExp_eq_sum_eigenvalues₀ (hA : A.IsHermitian) :
    traceExp A = ∑ i, Real.exp (hA.eigenvalues₀ i) := by
  rw [traceExp_eq_sum_eigenvalues hA]
  exact Fintype.sum_equiv (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm
    _ _ (fun i => rfl)

theorem traceExp_nonneg (hA : A.IsHermitian) : 0 ≤ traceExp A := by
  rw [traceExp_eq_sum_eigenvalues hA]
  exact Finset.sum_nonneg fun i _ => (Real.exp_pos _).le

@[simp] theorem traceExp_zero : traceExp (0 : Matrix ι ι ℝ) = Fintype.card ι := by
  simp [traceExp]

/-- Trace-exponential monotonicity under quadratic (Loewner) order. No
operator-monotonicity of the exponential is asserted or used. -/
theorem traceExp_mono_quadratic (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : ∀ x : ι → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x)) :
    traceExp A ≤ traceExp B := by
  rw [traceExp_eq_sum_eigenvalues₀ hA, traceExp_eq_sum_eigenvalues₀ hB]
  apply Finset.sum_le_sum
  intro j _
  exact Real.exp_le_exp.mpr (matrix_ordered_comparison A B hA hB hAB j)

theorem traceExp_mono (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : (B - A).PosSemidef) : traceExp A ≤ traceExp B := by
  apply traceExp_mono_quadratic hA hB
  intro x
  have hx := hAB.2 x
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at hx
  linarith

/-- An exact trace formula for any scalar transform of one self-adjoint matrix. -/
theorem traceExp_spectralMap (hA : A.IsHermitian) (f : ℝ → ℝ) :
    traceExp (spectralMap hA f) = ∑ i, Real.exp (f (hA.eigenvalues i)) := by
  rw [traceExp, exp_spectralMap, trace_spectralMap]

/-- Scalar affine transforms need no eigenvalue reindexing. -/
theorem spectralMap_affine (hA : A.IsHermitian) (θ b : ℝ) :
    spectralMap hA (fun x => θ * x + b) = θ • A + b • (1 : Matrix ι ι ℝ) := by
  rw [spectralMap_add, spectralMap_smul]
  change θ • spectralMap hA id + spectralMap hA (fun _ => b) = _
  rw [spectralMap_id]
  congr 1
  have hb := spectralMap_smul hA b (fun _ => 1)
  simpa only [mul_one, spectralMap_one] using hb

/-- Trace-Laplace threshold at an individual, actual matrix eigenvalue. -/
theorem traceExp_eigenvalue_threshold (hA : A.IsHermitian) (θ b u : ℝ)
    (hθ : 0 ≤ θ) (i : ι) (hi : u ≤ hA.eigenvalues i) :
    Real.exp (θ * u + b) ≤ traceExp (θ • A + b • (1 : Matrix ι ι ℝ)) := by
  rw [← spectralMap_affine hA θ b, traceExp_spectralMap]
  have hc : θ * u + b ≤ θ * hA.eigenvalues i + b :=
    add_le_add_right (mul_le_mul_of_nonneg_left hi hθ) b
  exact (Real.exp_le_exp.mpr hc).trans
    (Finset.single_le_sum (fun j _ => (Real.exp_pos (θ * hA.eigenvalues j + b)).le) (Finset.mem_univ i))

/-- The joint trace-Laplace threshold used with predictable variation. Only
quadratic order of the variation is needed, so it applies without commuting
`S` and `V`. -/
theorem traceExp_joint_threshold {S V : Matrix ι ι ℝ}
    (hS : S.IsHermitian) (hV : V.IsHermitian)
    (θ g u v : ℝ) (hθ : 0 ≤ θ) (hg : 0 ≤ g)
    (hbound : ∀ x : ι → ℝ, x ⬝ᵥ (V *ᵥ x) ≤ v * (x ⬝ᵥ x))
    (i : ι) (hi : u ≤ hS.eigenvalues i) :
    Real.exp (θ*u-g*v) ≤ traceExp (θ • S - g • V) := by
  have hH : (θ • S - g • V).IsHermitian := by
    change (θ • S - g • V)ᴴ = θ • S - g • V
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, star_trivial, hS.eq, hV.eq]
  have hL : (θ • S + (-g*v) • (1 : Matrix ι ι ℝ)).IsHermitian := by
    rw [← spectralMap_affine hS θ (-g*v)]
    exact spectralMap_isHermitian hS _
  have htrace := traceExp_mono_quadratic hL hH (by
    intro x
    simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    nlinarith only [mul_le_mul_of_nonneg_left (hbound x) hg])
  have hthreshold := traceExp_eigenvalue_threshold hS θ (-g*v) u hθ i hi
  have hh : Real.exp (θ*u-g*v) ≤ traceExp (θ • S + (-g*v) • (1 : Matrix ι ι ℝ)) := by
    simpa only [neg_mul, sub_eq_add_neg] using hthreshold
  exact hh.trans htrace

end TraceLaplace

/-- Bennett's scalar exponential quadratic bound, proved by termwise comparison
of the absolutely convergent exponential series. -/
theorem exp_quadratic_bennett (θ R x : ℝ) (hθ : 0 ≤ θ) (hR : 0 < R)
    (hx : |x| ≤ R) :
    Real.exp (θ * x) ≤ 1 + θ * x +
      ((Real.exp (θ * R) - θ * R - 1) / R ^ 2) * x ^ 2 := by
  have hs (z : ℝ) : Summable (fun n : ℕ => z ^ n / (n.factorial : ℝ)) :=
    NormedSpace.expSeries_div_summable ℝ z
  have he (z : ℝ) : (∑' n : ℕ, z ^ (n + 2) / ((n + 2).factorial : ℝ)) =
      Real.exp z - 1 - z := by
    have hh := (hs z).sum_add_tsum_nat_add 2
    have hfull : (∑' n : ℕ, z ^ n / (n.factorial : ℝ)) = Real.exp z := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    rw [hfull] at hh
    norm_num [Finset.sum_range_succ] at hh
    linarith
  have hterm (n : ℕ) : (θ * x) ^ (n+2) / ((n+2).factorial : ℝ) ≤
      (x ^ 2 / R ^ 2) * ((θ * R) ^ (n+2) / ((n+2).factorial : ℝ)) := by
    have hp : x ^ n ≤ R ^ n := (le_abs_self _).trans (by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg x) hx n)
    have hp' := mul_le_mul_of_nonneg_left hp
      (mul_nonneg (pow_nonneg hθ (n+2)) (sq_nonneg x))
    have hp'' : (θ * x) ^ (n+2) ≤ (x ^ 2 / R ^ 2) * (θ * R) ^ (n+2) := by
      have heq : (x ^ 2 / R ^ 2) * (θ * R) ^ (n+2) = θ ^ (n+2) * x^2 * R^n := by
        rw [mul_pow, pow_add R n 2]
        field_simp [hR.ne']
      rw [heq, mul_pow, pow_add x n 2]
      nlinarith only [hp']
    calc (θ * x) ^ (n+2) / ((n+2).factorial : ℝ)
        ≤ ((x ^ 2 / R ^ 2) * (θ * R) ^ (n+2)) / ((n+2).factorial : ℝ) :=
          div_le_div_of_nonneg_right hp'' (Nat.cast_nonneg _)
      _ = _ := by ring
  have hsx : Summable (fun n : ℕ => (θ*x)^(n+2) / ((n+2).factorial : ℝ)) :=
    (hs (θ*x)).comp_injective (fun a b hab => by omega)
  have hsR : Summable (fun n : ℕ => (θ*R)^(n+2) / ((n+2).factorial : ℝ)) :=
    (hs (θ*R)).comp_injective (fun a b hab => by omega)
  have ht := hsx.tsum_le_tsum hterm (hsR.mul_left (x^2/R^2))
  rw [tsum_mul_left, he (θ*x), he (θ*R)] at ht
  have heq : x ^ 2 / R ^ 2 * (Real.exp (θ * R) - 1 - θ * R) =
      ((Real.exp (θ * R) - θ * R - 1) / R ^ 2) * x ^ 2 := by ring
  rw [heq] at ht
  linarith

/-- Lifting any scalar exponential quadratic majorant to the actual exponential
of a self-adjoint matrix, with no matrix-exponential inequality as a premise. -/
theorem matrix_exp_quadratic_lift {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (θ g : ℝ)
    (hscalar : ∀ i, Real.exp (θ * hA.eigenvalues i) ≤
      1 + θ * hA.eigenvalues i + g * (hA.eigenvalues i) ^ 2) :
    ((1 : Matrix ι ι ℝ) + θ • A + g • (A * A) - NormedSpace.exp ℝ (θ • A)).PosSemidef := by
  have hid : spectralMap hA (fun x => x) = A := spectralMap_id hA
  have hsquare : spectralMap hA (fun x => x^2) = A*A := by
    simpa only [pow_two, id_eq, spectralMap_id] using (spectralMap_mul hA id id).symm
  have hlin : spectralMap hA (fun x => θ*x) = θ • A := by
    rw [spectralMap_smul, hid]
  have hpoly : spectralMap hA (fun x => 1 + θ*x + g*x^2) =
      (1 : Matrix ι ι ℝ) + θ • A + g • (A*A) := by
    rw [spectralMap_add, spectralMap_add, spectralMap_one, spectralMap_smul, hid,
      spectralMap_smul, hsquare]
  have hexp : spectralMap hA (fun x => Real.exp (θ*x)) = NormedSpace.exp ℝ (θ • A) := by
    rw [← exp_spectralMap, hlin]
  rw [← hpoly, ← hexp]
  exact spectralMap_mono hA _ _ hscalar

/-- The exact Bennett coefficient yields the matrix one-step mgf majorant. -/
theorem matrix_exp_bennett {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (θ R : ℝ) (hθ : 0 ≤ θ) (hR : 0 < R)
    (hbound : ∀ i, |hA.eigenvalues i| ≤ R) :
    ((1 : Matrix ι ι ℝ) + θ • A +
      ((Real.exp (θ*R)-θ*R-1)/R^2) • (A*A) - NormedSpace.exp ℝ (θ • A)).PosSemidef := by
  exact matrix_exp_quadratic_lift hA θ _
    (fun i => exp_quadratic_bennett θ R _ hθ hR (hbound i))

section InverseJensen

variable {ι α : Type*} [Fintype ι] [Fintype α]

/-- A finite nonnegative weighted sum of positive semidefinite matrices. -/
theorem weighted_sum_posSemidef (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (M : α → Matrix ι ι ℝ) (hM : ∀ a, (M a).PosSemidef) :
    (∑ a, p a • M a).PosSemidef := by
  have hh : (∑ a, p a • M a).IsHermitian := by
    change (∑ a, p a • M a)ᴴ = ∑ a, p a • M a
    rw [Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Matrix.conjTranspose_smul, star_trivial, (hM a).isHermitian.eq]
  refine ⟨hh, ?_⟩
  intro x
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul, smul_eq_mul]
  exact Finset.sum_nonneg fun a _ => mul_nonneg (hp a) ((hM a).2 x)

/-- A probability mixture of positive definite matrices is positive definite. -/
theorem weighted_sum_posDef (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (M : α → Matrix ι ι ℝ) (hM : ∀ a, (M a).PosDef) :
    (∑ a, p a • M a).PosDef := by
  have hpos : ∃ a, 0 < p a := by
    by_contra hn
    push_neg at hn
    have hz : ∀ a, p a = 0 := fun a => le_antisymm (hn a) (hp a)
    simp only [hz, Finset.sum_const_zero] at hsum
    norm_num at hsum
  obtain ⟨a, ha⟩ := hpos
  refine ⟨(weighted_sum_posSemidef p hp M (fun b => (hM b).posSemidef)).isHermitian, ?_⟩
  intro x hx
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul, smul_eq_mul]
  exact (mul_pos ha ((hM a).2 x hx)).trans_le
    (Finset.single_le_sum (fun b _ => mul_nonneg (hp b) ((hM b).posSemidef.2 x)) (Finset.mem_univ a))

variable [DecidableEq ι]

/-- Inverse Jensen for positive definite matrices. The mean is the actual
weighted matrix sum. The proof is the noncommutative sum-of-squares identity,
not a commutativity assumption or an assumed operator-convexity theorem. -/
theorem matrix_inverse_jensen (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (M : α → Matrix ι ι ℝ)
    (hM : ∀ a, (M a).PosDef) (B : Matrix ι ι ℝ) (hB : B.PosDef)
    (hmean : ∑ a, p a • M a = B) :
    (∑ a, p a • (M a)⁻¹ - B⁻¹).PosSemidef := by
  let C (a : α) := (M a)⁻¹ - B⁻¹
  have hL (a : α) : (M a)⁻¹ * M a = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (hM a).isUnit)
  have hR (a : α) : M a * (M a)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hM a).isUnit)
  have hBL : B⁻¹ * B = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hB.isUnit)
  have hC (a : α) : (C a).IsHermitian :=
    (hM a).inv.isHermitian.sub hB.inv.isHermitian
  have hQ (a : α) : (C a * M a * C a).PosSemidef := by
    simpa only [(hC a).eq] using (hM a).posSemidef.conjTranspose_mul_mul_same (C a)
  have he (a : α) : C a * M a * C a =
      (M a)⁻¹ - B⁻¹ - B⁻¹ + B⁻¹ * M a * B⁻¹ := by
    dsimp [C]
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    rw [hL a, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_assoc B⁻¹ (M a) (M a)⁻¹, hR a, Matrix.mul_one]
    abel
  have hlast : (∑ a, p a • (B⁻¹ * M a * B⁻¹)) = B⁻¹ * B * B⁻¹ := by
    rw [← hmean]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hid : (∑ a, p a • (C a * M a * C a)) = ∑ a, p a • (M a)⁻¹ - B⁻¹ := by
    simp_rw [he, smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, hsum, one_smul, hlast, hBL, Matrix.one_mul]
    abel
  rw [← hid]
  exact weighted_sum_posSemidef p hp _ hQ

/-- Actual eigenvalues are controlled by the Euclidean operator norm. -/
theorem eigenvalue_abs_le_matrix_opNorm {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (i : ι) :
    |hA.eigenvalues i| ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := by
  let v := hA.eigenvectorBasis i
  have he : Matrix.toEuclideanCLM (𝕜 := ℝ) A v = (hA.eigenvalues i) • v := by
    ext j
    exact congrFun (hA.mulVec_eigenvectorBasis i) j
  have hn : ‖v‖ = 1 := hA.eigenvectorBasis.norm_eq_one i
  have hh := (Matrix.toEuclideanCLM (𝕜 := ℝ) A).le_opNorm v
  rw [he, norm_smul, Real.norm_eq_abs, hn, mul_one, mul_one] at hh
  exact hh

/-- Bennett's matrix majorant with precisely the Euclidean operator-norm
hypothesis used by the source martingale theorem. -/
theorem matrix_exp_bennett_opNorm {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (θ R : ℝ) (hθ : 0 ≤ θ) (hR : 0 < R)
    (hbound : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ R) :
    ((1 : Matrix ι ι ℝ) + θ • A +
      ((Real.exp (θ*R)-θ*R-1)/R^2) • (A*A) - NormedSpace.exp ℝ (θ • A)).PosSemidef := by
  exact matrix_exp_bennett hA θ R hθ hR
    (fun i => (eigenvalue_abs_le_matrix_opNorm hA i).trans hbound)

/-- Finite-distribution matrix mgf bound. The centered mean and quadratic
variation are the actual weighted sums of the same increments. -/
theorem matrix_mgf_bennett (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (X : α → Matrix ι ι ℝ) (hX : ∀ a, (X a).IsHermitian)
    (θ R : ℝ) (hθ : 0 ≤ θ) (hR : 0 < R)
    (hbound : ∀ a, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (X a)‖ ≤ R)
    (hcenter : ∑ a, p a • X a = 0) :
    ((1 : Matrix ι ι ℝ) + ((Real.exp (θ*R)-θ*R-1)/R^2) •
      (∑ a, p a • (X a * X a)) - ∑ a, p a • NormedSpace.exp ℝ (θ • X a)).PosSemidef := by
  let g := (Real.exp (θ*R)-θ*R-1)/R^2
  have hh := weighted_sum_posSemidef p hp
    (fun a => (1 : Matrix ι ι ℝ) + θ • X a + g • (X a * X a) - NormedSpace.exp ℝ (θ • X a))
    (fun a => matrix_exp_bennett_opNorm (hX a) θ R hθ hR (hbound a))
  have hlin : (∑ a, p a • (θ • X a)) = θ • (∑ a, p a • X a) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact smul_comm (p a) θ (X a)
  have hquad : (∑ a, p a • (g • (X a * X a))) = g • (∑ a, p a • (X a * X a)) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact smul_comm (p a) g (X a * X a)
  simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hh
  rw [← Finset.sum_smul, hsum, one_smul, hlin, hcenter, smul_zero, add_zero, hquad] at hh
  exact hh

end InverseJensen

end PsgEst
