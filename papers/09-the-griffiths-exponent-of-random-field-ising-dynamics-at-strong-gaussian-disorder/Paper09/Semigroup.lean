/-
Copyright (c) 2026. The actual finite continuous-time heat-bath semigroup.
The transition matrices are matrix exponentials of the rate-one generator.
-/
import Paper09.Markov
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Prod

open Finset BigOperators Classical Matrix
open scoped Matrix.Norms.Operator

noncomputable section
namespace Paper09

section MatrixTools
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The absolutely convergent exponential series, evaluated at one entry. -/
theorem matrix_exp_hasSum (A : Matrix α α ℝ) (i j : α) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) * (A ^ n) i j)
      (NormedSpace.exp ℝ A i j) := by
  let e : Matrix α α ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj j : (α → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : (α → α → ℝ) →L[ℝ] (α → ℝ))
  simpa [e, Function.comp_def] using
    (NormedSpace.exp_series_hasSum_exp' A).map e e.continuous

/-- Entrywise positivity of the exponential of an entrywise nonnegative matrix. -/
theorem matrix_exp_nonneg (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j) (i j : α) :
    0 ≤ NormedSpace.exp ℝ A i j := by
  have hp (n : ℕ) : ∀ i j, 0 ≤ (A ^ n) i j := by
    induction n with
    | zero => intro i j; simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    | succ n ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      exact sum_nonneg fun k _ => mul_nonneg (ih i k) (hA k j)
  exact hasSum_le (fun n => mul_nonneg (by positivity) (hp n i j))
    hasSum_zero (matrix_exp_hasSum A i j)

/-- A zero-row-sum matrix exponentiates to a matrix with row sums one. -/
theorem matrix_exp_rows (A : Matrix α α ℝ) (hA : ∀ i, ∑ j, A i j = 0) (i : α) :
    ∑ j, NormedSpace.exp ℝ A i j = 1 := by
  have hp (n : ℕ) : ∀ i, ∑ j, (A ^ n) i j = if n = 0 then 1 else 0 := by
    induction n with
    | zero => intro i; simp [Matrix.one_apply]
    | succ n ih =>
      intro i
      rw [pow_succ, if_neg (Nat.succ_ne_zero n)]
      simp only [Matrix.mul_apply]
      rw [sum_comm]
      simp_rw [← mul_sum, hA, mul_zero, sum_const_zero]
  have hs := hasSum_sum (fun j (_ : j ∈ (univ : Finset α)) => matrix_exp_hasSum A i j)
  have hz : HasSum (fun n : ℕ => ∑ j, (n.factorial : ℝ)⁻¹ * (A ^ n) i j) 1 := by
    have ht (n : ℕ) : (∑ j, (n.factorial : ℝ)⁻¹ * (A ^ n) i j) =
        if n = 0 then 1 else 0 := by
      rw [← mul_sum, hp]
      split_ifs with h
      · subst n; norm_num
      · simp
    simp_rw [ht]
    simpa using (hasSum_single 0 (fun n hn => by simp [hn]) :
      HasSum (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) 1)
  exact hs.unique hz

/-- Adding a scalar identity allows positivity to be proved from a nonnegative
matrix, without imposing a false sign condition on generator diagonals. -/
theorem matrix_exp_nonneg_of_shift (A : Matrix α α ℝ) (R : ℝ)
    (hA : ∀ i j, 0 ≤ (A + R • (1 : Matrix α α ℝ)) i j) (i j : α) :
    0 ≤ NormedSpace.exp ℝ A i j := by
  have hc : Commute A (R • (1 : Matrix α α ℝ)) := by
    change A * (R • (1 : Matrix α α ℝ)) = (R • (1 : Matrix α α ℝ)) * A
    simp only [Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]
  have he := Matrix.exp_add_of_commute ℝ A (R • (1 : Matrix α α ℝ)) hc
  have hscalar : NormedSpace.exp ℝ (R • (1 : Matrix α α ℝ)) =
      Real.exp R • (1 : Matrix α α ℝ) := by
    rw [← Algebra.algebraMap_eq_smul_one, ← NormedSpace.algebraMap_exp_comm,
      ← Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one]
  rw [hscalar, Matrix.mul_smul, mul_one] at he
  have hi := congrArg (fun M : Matrix α α ℝ => M i j) he
  have hn := matrix_exp_nonneg (A + R • (1 : Matrix α α ℝ)) hA i j
  change NormedSpace.exp ℝ (A + R • (1 : Matrix α α ℝ)) i j =
    Real.exp R * NormedSpace.exp ℝ A i j at hi
  rw [hi] at hn
  exact (mul_nonneg_iff_of_pos_left (Real.exp_pos R)).mp hn

/-- Detailed balance is preserved by every matrix power. -/
theorem matrix_pow_reversible (p : α → ℝ) (A : Matrix α α ℝ)
    (hA : ∀ i j, p i * A i j = p j * A j i) (n : ℕ) :
    ∀ i j, p i * (A ^ n) i j = p j * (A ^ n) j i := by
  induction n with
  | zero =>
    intro i j
    by_cases h : i = j
    · subst j; rfl
    · simp [h, Ne.symm h]
  | succ n ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply, mul_sum]
    calc
      ∑ k, p i * ((A ^ n) i k * A k j) =
          ∑ k, p j * (A j k * (A ^ n) k i) := by
        apply sum_congr rfl
        intro k _
        calc
          p i * ((A ^ n) i k * A k j) = (p i * (A ^ n) i k) * A k j := by ring
          _ = (p k * (A ^ n) k i) * A k j := by rw [ih]
          _ = (p k * A k j) * (A ^ n) k i := by ring
          _ = (p j * A j k) * (A ^ n) k i := by rw [hA]
          _ = p j * (A j k * (A ^ n) k i) := by ring
      _ = p j * (A * A ^ n) j i := by rw [Matrix.mul_apply, mul_sum]
      _ = p j * (A ^ n * A) j i := by rw [← pow_succ', pow_succ]

/-- Detailed balance is preserved by the absolutely convergent exponential. -/
theorem matrix_exp_reversible (p : α → ℝ) (A : Matrix α α ℝ)
    (hA : ∀ i j, p i * A i j = p j * A j i) (i j : α) :
    p i * NormedSpace.exp ℝ A i j = p j * NormedSpace.exp ℝ A j i := by
  have h1 := (matrix_exp_hasSum A i j).mul_left (p i)
  have h2 := (matrix_exp_hasSum A j i).mul_left (p j)
  have ht (n : ℕ) : p i * ((n.factorial : ℝ)⁻¹ * (A ^ n) i j) =
      p j * ((n.factorial : ℝ)⁻¹ * (A ^ n) j i) := by
    calc
      _ = (n.factorial : ℝ)⁻¹ * (p i * (A ^ n) i j) := by ring
      _ = (n.factorial : ℝ)⁻¹ * (p j * (A ^ n) j i) := by
        rw [matrix_pow_reversible p A hA n i j]
      _ = _ := by ring
  exact h1.unique (h2.congr_fun fun n => ht n)

/-- The actual derivative of the exponential, evaluated entry by entry. -/
theorem matrix_semigroup_hasDerivAt (A : Matrix α α ℝ) (t : ℝ) (i j : α) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ℝ (s • A) i j)
      ((A * NormedSpace.exp ℝ (t • A)) i j) t := by
  let e : Matrix α α ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj j : (α → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : (α → α → ℝ) →L[ℝ] (α → ℝ))
  simpa [e, Function.comp_def] using
    e.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const' A t)

/-- Matrix exponentiation evolves an actual eigenvector by the scalar exponential. -/
theorem matrix_exp_mulVec_eigen (A : Matrix α α ℝ) (f : α → ℝ) (r : ℝ)
    (hf : A *ᵥ f = r • f) :
    NormedSpace.exp ℝ A *ᵥ f = Real.exp r • f := by
  have hp (n : ℕ) : A ^ n *ᵥ f = r ^ n • f := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hf, smul_smul,
        pow_succ', mul_comm]
  funext i
  have hs := hasSum_sum (fun j (_ : j ∈ (univ : Finset α)) =>
    (matrix_exp_hasSum A i j).mul_right (f j))
  have ht (n : ℕ) : (∑ j, (n.factorial : ℝ)⁻¹ * (A ^ n) i j * f j) =
      ((n.factorial : ℝ)⁻¹ * r ^ n) * f i := by
    calc
      _ = (n.factorial : ℝ)⁻¹ * (A ^ n *ᵥ f) i := by
        simp only [Matrix.mulVec, dotProduct, mul_sum]
        apply sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hp]; simp only [Pi.smul_apply, smul_eq_mul]; ring
  have he : HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ * r ^ n * f i)
      (Real.exp r * f i) := by
    simpa only [smul_eq_mul, ← Real.exp_eq_exp_ℝ] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) r).mul_right (f i)
  change (∑ j, NormedSpace.exp ℝ A i j * f j) = Real.exp r * f i
  exact (hs.congr_fun fun n => (ht n).symm).unique he

end MatrixTools

section HeatBath
variable {V : Type*} [Fintype V]

/-- The generator matrix, including its negative exit-rate diagonal. -/
def heatBathMatrix (p : FinProb (Config V)) : Matrix (Config V) (Config V) ℝ :=
  fun η η' => heatBathRate p η η' -
    if η = η' then ∑ ξ, heatBathRate p η ξ else 0

theorem heatBathMatrix_mulVec (p : FinProb (Config V)) (f : Config V → ℝ) :
    (heatBathMatrix p) *ᵥ f = heatBathGenerator p f := by
  funext η
  classical
  simp only [Matrix.mulVec, dotProduct, heatBathMatrix, sub_mul, sum_sub_distrib]
  simp only [ite_mul, zero_mul]
  simp only [sum_ite_eq, mem_univ, if_true]
  unfold heatBathGenerator
  simp only [mul_sub, sum_sub_distrib, sum_mul]

theorem heatBathMatrix_rows (p : FinProb (Config V)) (η : Config V) :
    ∑ η', heatBathMatrix p η η' = 0 := by
  classical
  simp [heatBathMatrix, sum_sub_distrib]

theorem heatBathMatrix_reversible (p : FinProb (Config V)) (η η' : Config V) :
    p.w η * heatBathMatrix p η η' = p.w η' * heatBathMatrix p η' η := by
  classical
  by_cases h : η = η'
  · subst η'; rfl
  · simp only [heatBathMatrix, if_neg h, if_neg (Ne.symm h), sub_zero]
    exact heatBathRate_reversible p η η'

/-- The true continuous-time heat-bath evolution, with its original time normalization. -/
def heatBathSemigroup (p : FinProb (Config V)) (t : ℝ) : Matrix (Config V) (Config V) ℝ :=
  NormedSpace.exp ℝ (t • heatBathMatrix p)

theorem heatBathSemigroup_zero (p : FinProb (Config V)) : heatBathSemigroup p 0 = 1 := by
  simp [heatBathSemigroup]

theorem heatBathSemigroup_add (p : FinProb (Config V)) (s t : ℝ) :
    heatBathSemigroup p (s + t) = heatBathSemigroup p s * heatBathSemigroup p t := by
  classical
  unfold heatBathSemigroup
  rw [add_smul]
  apply Matrix.exp_add_of_commute
  change (s • heatBathMatrix p) * (t • heatBathMatrix p) =
    (t • heatBathMatrix p) * (s • heatBathMatrix p)
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm s t]

theorem heatBathSemigroup_rows (p : FinProb (Config V)) (t : ℝ) (η : Config V) :
    ∑ η', heatBathSemigroup p t η η' = 1 := by
  classical
  apply matrix_exp_rows
  intro η
  simp only [Matrix.smul_apply, smul_eq_mul, ← mul_sum, heatBathMatrix_rows, mul_zero]

theorem heatBathSemigroup_nonneg (p : FinProb (Config V)) (t : ℝ) (ht : 0 ≤ t)
    (η η' : Config V) : 0 ≤ heatBathSemigroup p t η η' := by
  classical
  let R : ℝ := ∑ a : Config V, ∑ b : Config V, heatBathRate p a b
  apply matrix_exp_nonneg_of_shift (t • heatBathMatrix p) (t * R)
  intro a b
  have hrow : (∑ ξ, heatBathRate p a ξ) ≤ R := by
    exact single_le_sum (fun c _ => sum_nonneg fun ξ _ => heatBathRate_nonneg p c ξ) (mem_univ a)
  by_cases h : a = b
  · subst b
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      heatBathMatrix, Matrix.one_apply_eq, ite_true, mul_one]
    have hr := heatBathRate_nonneg p a a
    nlinarith
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      heatBathMatrix, if_neg h, sub_zero, Matrix.one_apply_ne h, mul_zero, add_zero]
    exact mul_nonneg ht (heatBathRate_nonneg p a b)

theorem heatBathSemigroup_reversible (p : FinProb (Config V)) (t : ℝ) (η η' : Config V) :
    p.w η * heatBathSemigroup p t η η' = p.w η' * heatBathSemigroup p t η' η := by
  classical
  apply matrix_exp_reversible
  intro a b
  simp only [Matrix.smul_apply, smul_eq_mul]
  calc
    _ = t * (p.w a * heatBathMatrix p a b) := by ring
    _ = t * (p.w b * heatBathMatrix p b a) := by rw [heatBathMatrix_reversible]
    _ = _ := by ring

/-- Probability transitions at nonnegative time. Extending by time zero on
negative inputs keeps the public kernel total without changing any chain time. -/
def heatBathTransition (p : FinProb (Config V)) (t : ℝ) (η : Config V) : FinProb (Config V) where
  w η' := heatBathSemigroup p (max t 0) η η'
  nonneg η' := heatBathSemigroup_nonneg p (max t 0) (le_max_right _ _) η η'
  sum_one := heatBathSemigroup_rows p (max t 0) η

theorem heatBathTransition_w (p : FinProb (Config V)) (t : ℝ) (ht : 0 ≤ t)
    (η η' : Config V) : (heatBathTransition p t η).w η' = heatBathSemigroup p t η η' := by
  simp [heatBathTransition, max_eq_left ht]

theorem heatBathTransition_reversible (p : FinProb (Config V)) (t : ℝ) :
    MarkovKernel.Reversible (heatBathTransition p t) p := by
  intro a b
  exact heatBathSemigroup_reversible p (max t 0) a b

theorem heatBathTransition_stationary (p : FinProb (Config V)) (t : ℝ) :
    MarkovKernel.Stationary (heatBathTransition p t) p :=
  MarkovKernel.stationary_of_reversible _ _ (heatBathTransition_reversible p t)

/-- The backward equation for the actual matrix-exponential evolution. -/
theorem heatBathSemigroup_hasDerivAt (p : FinProb (Config V)) (f : Config V → ℝ)
    (t : ℝ) (η : Config V) :
    HasDerivAt (fun s : ℝ => (heatBathSemigroup p s *ᵥ f) η)
      (heatBathGenerator p (heatBathSemigroup p t *ᵥ f) η) t := by
  classical
  have h (η' : Config V) :
      HasDerivAt (fun s : ℝ => heatBathSemigroup p s η η' * f η')
        ((heatBathMatrix p * heatBathSemigroup p t) η η' * f η') t :=
    (matrix_semigroup_hasDerivAt (heatBathMatrix p) t η η').mul_const _
  have hh := HasDerivAt.fun_sum (u := univ) (fun η' _ => h η')
  have he : (∑ η', (heatBathMatrix p * heatBathSemigroup p t) η η' * f η') =
      heatBathGenerator p (heatBathSemigroup p t *ᵥ f) η := by
    change ((heatBathMatrix p * heatBathSemigroup p t) *ᵥ f) η = _
    rw [← Matrix.mulVec_mulVec, heatBathMatrix_mulVec]
  simpa only [Matrix.mulVec, dotProduct, he] using hh

/-- The matrix-exponential evolution of a generator eigenfunction. -/
theorem heatBathSemigroup_eigenfunction (p : FinProb (Config V))
    (f : Config V → ℝ) (r t : ℝ)
    (hf : ∀ η, heatBathGenerator p f η = r * f η) :
    heatBathSemigroup p t *ᵥ f = fun η => Real.exp (t * r) * f η := by
  classical
  apply matrix_exp_mulVec_eigen
  rw [Matrix.smul_mulVec, heatBathMatrix_mulVec]
  funext η
  simp only [Pi.smul_apply, smul_eq_mul, hf]
  ring

/-- Chapman–Kolmogorov for the actual probability transitions at nonnegative times. -/
theorem heatBathTransition_add (p : FinProb (Config V)) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (η η' : Config V) :
    (heatBathTransition p (s + t) η).w η' =
      (MarkovKernel.push (heatBathTransition p t) (heatBathTransition p s η)).w η' := by
  rw [heatBathTransition_w p (s + t) (add_nonneg hs ht), heatBathSemigroup_add]
  simp only [Matrix.mul_apply, MarkovKernel.push,
    heatBathTransition_w p s hs, heatBathTransition_w p t ht]

end HeatBath
end Paper09
