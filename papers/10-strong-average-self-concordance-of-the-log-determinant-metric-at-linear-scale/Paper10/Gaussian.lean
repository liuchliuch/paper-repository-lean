import Paper10.Basic
import Paper10.PairedTraces
import Paper10.Symm
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Matrix.Order

/-!
# Proposition 2.4 (Gaussian trace bounds)

Let `A` be a centered Gaussian in `S^q` with covariance `0 ≼ Q ≼ I`.  Then
  `E Tr(A⁴) ≤ 3 n c_q ≤ 3q³`,
  `E (Tr(A³))² ≤ 27 n c_q ≤ 27q³`.

We model `A = ∑_a σ_a ξ_a F_a` with `ξ_a` i.i.d. standard Gaussian and
`0 ≤ σ_a ≤ 1`, where `{F_a}` is a Frobenius-orthonormal basis of `S^q`.
-/

noncomputable section

open Matrix MeasureTheory ProbabilityTheory Real
open scoped MatrixOrder

namespace Paper10

variable {q : ℕ}

/-! ## Single-coordinate moments of `gaussianReal 0 1` -/

theorem gauss_int_id : ∫ x, x ∂gaussianReal 0 1 = 0 := by
  rw [integral_id_gaussianReal]

theorem gauss_int_sq : ∫ x, x ^ 2 ∂gaussianReal 0 1 = 1 := by
  have hvar : Var[fun x ↦ x; gaussianReal 0 1] = 1 := variance_fun_id_gaussianReal
  have hmean : ∫ x, x ∂gaussianReal 0 1 = 0 := gauss_int_id
  rw [variance_of_integral_eq_zero (by fun_prop) (by simp [hmean])] at hvar
  simpa using hvar

/-- MGF of the standard real Gaussian. -/
theorem mgf_std_gauss : mgf (fun x : ℝ ↦ x) (gaussianReal 0 1)
    = fun t ↦ rexp (t ^ 2 / 2) := by
  have := mgf_fun_id_gaussianReal (μ := 0) (v := 1)
  simpa using this

/-- f(t) = exp(t²/2). -/
private abbrev fexp : ℝ → ℝ := fun t => rexp (t ^ 2 / 2)

private lemma differentiableAt_quad (t : ℝ) : DifferentiableAt ℝ (fun s : ℝ => s ^ 2 / 2) t :=
  (differentiableAt_id.pow 2).div_const 2

private lemma deriv_quad (t : ℝ) : deriv (fun s : ℝ => s ^ 2 / 2) t = t := by
  have h : deriv (fun s : ℝ => s ^ 2) t = 2 * t := by
    rw [deriv_pow_field]
    ring
  rw [deriv_div_const, h]
  ring

private lemma deriv_fexp_apply (t : ℝ) : deriv fexp t = t * rexp (t ^ 2 / 2) := by
  have h : deriv (fun x : ℝ => rexp (x ^ 2 / 2)) t
      = rexp (t ^ 2 / 2) * deriv (fun x : ℝ => x ^ 2 / 2) t :=
    deriv_exp (differentiableAt_quad t)
  have h2 : deriv (fun x : ℝ => x ^ 2 / 2) t = t := deriv_quad t
  show deriv (fun x : ℝ => rexp (x ^ 2 / 2)) t = _
  rw [h, h2]
  ring

private lemma deriv_fexp : deriv fexp = fun t => t * rexp (t ^ 2 / 2) := by
  ext t
  exact deriv_fexp_apply t

private lemma differentiableAt_fexp (t : ℝ) : DifferentiableAt ℝ fexp t := by
  show DifferentiableAt ℝ (fun x : ℝ => rexp (x ^ 2 / 2)) t
  exact (differentiableAt_quad t).exp

private lemma deriv_two_fexp_apply (t : ℝ) :
    deriv (deriv fexp) t = (1 + t ^ 2) * rexp (t ^ 2 / 2) := by
  rw [deriv_fexp]
  have hmul := deriv_fun_mul (𝕜 := ℝ) (c := fun s : ℝ => s) (d := fun s : ℝ => rexp (s ^ 2 / 2))
    (x := t) differentiableAt_id (differentiableAt_fexp t)
  have hd : deriv (fun s : ℝ => s) t = 1 := by rw [deriv_id'']
  have he : deriv (fun s : ℝ => rexp (s ^ 2 / 2)) t = t * rexp (t ^ 2 / 2) :=
    deriv_fexp_apply t
  have h : deriv (fun s : ℝ => s * rexp (s ^ 2 / 2)) t
      = 1 * rexp (t ^ 2 / 2) + t * (t * rexp (t ^ 2 / 2)) := by
    rw [hmul, hd, he]
  rw [h]
  ring

private lemma deriv_two_fexp : deriv (deriv fexp) = fun t => (1 + t ^ 2) * rexp (t ^ 2 / 2) := by
  ext t
  exact deriv_two_fexp_apply t

private lemma iteratedDeriv_three_fexp_apply (t : ℝ) :
    iteratedDeriv 3 fexp t = (3 * t + t ^ 3) * rexp (t ^ 2 / 2) := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
  rw [deriv_two_fexp]
  have hmul := deriv_fun_mul (𝕜 := ℝ) (c := fun s : ℝ => 1 + s ^ 2)
    (d := fun s : ℝ => rexp (s ^ 2 / 2)) (x := t)
    ((differentiableAt_const 1).add (differentiableAt_id.pow 2)) (differentiableAt_fexp t)
  have hd : deriv (fun s : ℝ => 1 + s ^ 2) t = 2 * t := by
    have h := deriv_fun_add (𝕜 := ℝ) (f := fun s : ℝ => (1:ℝ)) (g := fun s : ℝ => s ^ 2)
      (x := t) (differentiableAt_const 1) (differentiableAt_id.pow 2)
    have h1 : deriv (fun s : ℝ => (1:ℝ)) t = 0 := by rw [deriv_const]
    have h2 : deriv (fun s : ℝ => s ^ 2) t = 2 * t := by
      rw [deriv_pow_field]; ring
    rw [h, h1, h2]
    ring
  have he : deriv (fun s : ℝ => rexp (s ^ 2 / 2)) t = t * rexp (t ^ 2 / 2) :=
    deriv_fexp_apply t
  have h : deriv (fun s : ℝ => (1 + s ^ 2) * rexp (s ^ 2 / 2)) t
      = 2 * t * rexp (t ^ 2 / 2) + (1 + t ^ 2) * (t * rexp (t ^ 2 / 2)) := by
    rw [hmul, hd, he]
  rw [h]
  ring

private lemma iteratedDeriv_three_fexp :
    iteratedDeriv 3 fexp = fun t => (3 * t + t ^ 3) * rexp (t ^ 2 / 2) := by
  ext t
  exact iteratedDeriv_three_fexp_apply t

private lemma iteratedDeriv_four_fexp_apply (t : ℝ) :
    iteratedDeriv 4 fexp t = (3 + 6 * t ^ 2 + t ^ 4) * rexp (t ^ 2 / 2) := by
  rw [iteratedDeriv_succ]
  rw [iteratedDeriv_three_fexp]
  have hmul := deriv_fun_mul (𝕜 := ℝ) (c := fun s : ℝ => 3 * s + s ^ 3)
    (d := fun s : ℝ => rexp (s ^ 2 / 2)) (x := t)
    (((differentiableAt_const 3).mul differentiableAt_id).add (differentiableAt_id.pow 3))
    (differentiableAt_fexp t)
  have hd : deriv (fun s : ℝ => 3 * s + s ^ 3) t = 3 + 3 * t ^ 2 := by
    have hA := deriv_fun_add (𝕜 := ℝ) (f := fun s : ℝ => (3:ℝ) * s) (g := fun s : ℝ => s ^ 3)
      (x := t) ((differentiableAt_const 3).mul differentiableAt_id) (differentiableAt_id.pow 3)
    have h1 : deriv (fun s : ℝ => (3:ℝ) * s) t = 3 := by
      have hB := deriv_fun_mul (𝕜 := ℝ) (c := fun s : ℝ => (3:ℝ)) (d := fun s : ℝ => s)
        (x := t) (differentiableAt_const 3) differentiableAt_id
      have a : deriv (fun s : ℝ => (3:ℝ)) t = 0 := by rw [deriv_const]
      have b : deriv (fun s : ℝ => s) t = 1 := by rw [deriv_id'']
      rw [hB, a, b]
      ring
    have h2 : deriv (fun s : ℝ => s ^ 3) t = 3 * t ^ 2 := by
      rw [deriv_pow_field]; ring
    rw [hA, h1, h2]
  have he : deriv (fun s : ℝ => rexp (s ^ 2 / 2)) t = t * rexp (t ^ 2 / 2) :=
    deriv_fexp_apply t
  have h : deriv (fun s : ℝ => (3 * s + s ^ 3) * rexp (s ^ 2 / 2)) t
      = (3 + 3 * t ^ 2) * rexp (t ^ 2 / 2) + (3 * t + t ^ 3) * (t * rexp (t ^ 2 / 2)) := by
    rw [hmul, hd, he]
  rw [h]
  ring

private lemma iteratedDeriv_four_fexp :
    iteratedDeriv 4 fexp = fun t => (3 + 6 * t ^ 2 + t ^ 4) * rexp (t ^ 2 / 2) := by
  ext t
  exact iteratedDeriv_four_fexp_apply t

theorem gauss_int_cube : ∫ x, x ^ 3 ∂gaussianReal 0 1 = 0 := by
  have h := iteratedDeriv_mgf_zero (X := fun x : ℝ ↦ x) (μ := gaussianReal 0 1)
    (by simp [integrableExpSet_fun_id_gaussianReal]) 3
  have hmgf : mgf (fun x : ℝ ↦ x) (gaussianReal 0 1) = fexp := mgf_std_gauss
  rw [hmgf, iteratedDeriv_three_fexp] at h
  simp at h
  rw [← h]

theorem gauss_int_fourth : ∫ x, x ^ 4 ∂gaussianReal 0 1 = 3 := by
  have h := iteratedDeriv_mgf_zero (X := fun x : ℝ ↦ x) (μ := gaussianReal 0 1)
    (by simp [integrableExpSet_fun_id_gaussianReal]) 4
  have hmgf : mgf (fun x : ℝ ↦ x) (gaussianReal 0 1) = fexp := mgf_std_gauss
  rw [hmgf, iteratedDeriv_four_fexp] at h
  simp at h
  rw [← h]

/-- Polynomial factors in successive derivatives of the standard Gaussian MGF. -/
def gaussianMGFPoly : ℕ → Polynomial ℝ
  | 0 => 1
  | k + 1 => (gaussianMGFPoly k).derivative + Polynomial.X * gaussianMGFPoly k

private theorem iteratedDeriv_gaussian_mgf (k : ℕ) :
    iteratedDeriv k fexp = fun t => (gaussianMGFPoly k).eval t * rexp (t ^ 2 / 2) := by
  induction k with
  | zero => simp [gaussianMGFPoly, fexp]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have he : HasDerivAt fexp (t * rexp (t ^ 2 / 2)) t := by
      simpa only [deriv_fexp_apply] using (differentiableAt_fexp t).hasDerivAt
    have h := ((gaussianMGFPoly k).hasDerivAt t).mul he
    change deriv ((fun x : ℝ => (gaussianMGFPoly k).eval x) * fexp) t = _
    rw [h.deriv]
    simp only [gaussianMGFPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
    ring

/-- A computable exact formula for every scalar standard Gaussian moment. -/
theorem gauss_int_pow_mgfPoly (k : ℕ) :
    (∫ x : ℝ, x ^ k ∂gaussianReal 0 1) = (gaussianMGFPoly k).eval 0 := by
  have h := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 1)
    (by simp [integrableExpSet_fun_id_gaussianReal]) k
  rw [show mgf (fun x : ℝ => x) (gaussianReal 0 1) = fexp from mgf_std_gauss,
    iteratedDeriv_gaussian_mgf] at h
  simpa using h.symm

theorem gauss_int_sixth : (∫ x : ℝ, x ^ 6 ∂gaussianReal 0 1) = 15 := by
  rw [gauss_int_pow_mgfPoly]
  norm_num [gaussianMGFPoly, Polynomial.derivative_add, Polynomial.derivative_mul]

theorem gauss_int_pow_le4 (n : ℕ) (h4 : n ≤ 4) :
    ∫ x, x ^ n ∂gaussianReal 0 1
      = if n = 0 then 1 else if n = 2 then 1 else if n = 4 then 3 else 0 := by
  interval_cases n
  · simp
  · simp
  · simp [gauss_int_sq]
  · simp [gauss_int_cube]
  · simp [gauss_int_fourth]

theorem gauss_int_odd (n : ℕ) (hn : Odd n) (h4 : n ≤ 4) :
    ∫ x, x ^ n ∂gaussianReal 0 1 = 0 := by
  obtain ⟨k, rfl⟩ := hn
  have hk : k ≤ 1 := by
    have : 2 * k + 1 ≤ 4 := h4
    omega
  interval_cases k
  · simp
  · have : (2 * 1 + 1 : ℕ) = 3 := by norm_num
    rw [this, gauss_int_cube]

/-! ## Product measure and Wick pairings -/

/-- Product of independent standard Gaussian measures on `Fin m → ℝ`. -/
def stdGaussianMeasure (m : ℕ) : Measure (Fin m → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

/-- Standard Gaussian random variables `ξ_a` on `ℝ^m`. -/
def stdGaussianVar (m : ℕ) (a : Fin m) : (Fin m → ℝ) → ℝ := fun ω => ω a

lemma aestronglyMeasurable_coord {m : ℕ} (a : Fin m) :
    AEStronglyMeasurable (fun ω : Fin m → ℝ => ω a) (stdGaussianMeasure m) :=
  (measurable_pi_apply a).aestronglyMeasurable

theorem integral_coord {m : ℕ} (a : Fin m) :
    (∫ ω : Fin m → ℝ, ω a ∂stdGaussianMeasure m)
      = ∫ x : ℝ, x ∂gaussianReal 0 1 := by
  unfold stdGaussianMeasure
  exact MeasureTheory.integral_comp_eval (μ := fun _ => gaussianReal 0 1)
    (i := a) (f := fun x => x) (by fun_prop)

theorem integral_coord_pow {m : ℕ} (a : Fin m) (k : ℕ) :
    (∫ ω : Fin m → ℝ, ω a ^ k ∂stdGaussianMeasure m)
      = ∫ x : ℝ, x ^ k ∂gaussianReal 0 1 := by
  unfold stdGaussianMeasure
  exact MeasureTheory.integral_comp_eval (μ := fun _ => gaussianReal 0 1)
    (i := a) (f := fun x => x ^ k) (by fun_prop)

/-- Second moment: `E[ξ_a ξ_b] = δ_ab`. -/
theorem wick_two {m : ℕ} (a b : Fin m) :
    (∫ ω : Fin m → ℝ, ω a * ω b ∂stdGaussianMeasure m)
      = if a = b then 1 else 0 := by
  by_cases hab : a = b
  · subst hab
    have h : (fun ω : Fin m → ℝ => ω a * ω a) = (fun ω => ω a ^ 2) := by
      ext ω; ring
    rw [h, integral_coord_pow, gauss_int_sq]
    simp
  · have h : (∫ ω : Fin m → ℝ, ω a * ω b ∂stdGaussianMeasure m)
        = (∫ ω, ω a ∂stdGaussianMeasure m) * (∫ ω, ω b ∂stdGaussianMeasure m) := by
      have hindep : iIndepFun (fun i (ω : Fin m → ℝ) => ω i) (stdGaussianMeasure m) := by
        unfold stdGaussianMeasure
        exact iIndepFun_pi (fun _ => aemeasurable_id)
      have hpair : IndepFun (fun ω : Fin m → ℝ => ω a) (fun ω => ω b) (stdGaussianMeasure m) :=
        hindep.indepFun hab
      exact hpair.integral_fun_mul_eq_mul_integral
        (aestronglyMeasurable_coord a) (aestronglyMeasurable_coord b)
    rw [h, integral_coord, integral_coord]
    simp [gauss_int_id, hab]

/-- Odd moments of a centered standard Gaussian vanish. -/
theorem gaussian_odd_moment_zero {m : ℕ} (a : Fin m) :
    (∫ ω : Fin m → ℝ, ω a ^ 3 ∂stdGaussianMeasure m) = 0 := by
  rw [integral_coord_pow, gauss_int_cube]

/-- Fourth moment of a standard Gaussian: `E[ξ⁴] = 3`. -/
theorem gaussian_fourth {m : ℕ} (a : Fin m) :
    (∫ ω : Fin m → ℝ, ω a ^ 4 ∂stdGaussianMeasure m) = 3 := by
  rw [integral_coord_pow, gauss_int_fourth]

/-! ## Multiplicity factorization of a four-fold product -/

/-- Multiplicity of `i` among `{a,b,c,d}`. -/
def mult4 {m : ℕ} (a b c d i : Fin m) : ℕ :=
  (if i = a then 1 else 0) + (if i = b then 1 else 0)
    + (if i = c then 1 else 0) + (if i = d then 1 else 0)

lemma mult4_le {m : ℕ} (a b c d i : Fin m) : mult4 a b c d i ≤ 4 := by
  unfold mult4
  have h1 : (if i = a then 1 else 0) ≤ 1 := by split_ifs <;> norm_num
  have h2 : (if i = b then 1 else 0) ≤ 1 := by split_ifs <;> norm_num
  have h3 : (if i = c then 1 else 0) ≤ 1 := by split_ifs <;> norm_num
  have h4 : (if i = d then 1 else 0) ≤ 1 := by split_ifs <;> norm_num
  omega

lemma pow_mult4 {m : ℕ} (a b c d i : Fin m) (x : ℝ) :
    x ^ mult4 a b c d i
      = x ^ (if i = a then 1 else 0) * x ^ (if i = b then 1 else 0)
        * x ^ (if i = c then 1 else 0) * x ^ (if i = d then 1 else 0) := by
  unfold mult4
  rw [pow_add, pow_add, pow_add]

lemma prod_single_indicator {m : ℕ} (a : Fin m) (x : Fin m → ℝ) :
    ∏ i, x i ^ (if i = a then 1 else 0) = x a := by
  classical
  rw [Finset.prod_eq_single a]
  · simp
  · intro i _ hi
    have : (if i = a then (1:ℕ) else 0) = 0 := if_neg hi
    rw [this, pow_zero]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

lemma prod_as_powers {m : ℕ} (a b c d : Fin m) (ω : Fin m → ℝ) :
    ω a * ω b * ω c * ω d = ∏ i, ω i ^ mult4 a b c d i := by
  classical
  rw [show (∏ i : Fin m, ω i ^ mult4 a b c d i)
      = ∏ i : Fin m, (ω i ^ (if i = a then 1 else 0) * ω i ^ (if i = b then 1 else 0)
        * ω i ^ (if i = c then 1 else 0) * ω i ^ (if i = d then 1 else 0)) by
    apply Finset.prod_congr rfl
    intro i _
    exact pow_mult4 a b c d i (ω i)]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  rw [prod_single_indicator, prod_single_indicator, prod_single_indicator, prod_single_indicator]

lemma integral_prod_powers {m : ℕ} (k : Fin m → ℕ) :
    (∫ ω : Fin m → ℝ, ∏ i, ω i ^ k i ∂stdGaussianMeasure m)
      = ∏ i, ∫ x : ℝ, x ^ k i ∂gaussianReal 0 1 := by
  unfold stdGaussianMeasure
  exact MeasureTheory.integral_fintype_prod_eq_prod _

lemma integral_prod_as_powers {m : ℕ} (a b c d : Fin m) :
    (∫ ω : Fin m → ℝ, ω a * ω b * ω c * ω d ∂stdGaussianMeasure m)
      = ∏ i, ∫ x : ℝ, x ^ mult4 a b c d i ∂gaussianReal 0 1 := by
  have h : (fun ω : Fin m → ℝ => ω a * ω b * ω c * ω d)
      = fun ω => ∏ i, ω i ^ mult4 a b c d i := by
    ext ω
    exact prod_as_powers a b c d ω
  rw [h, integral_prod_powers]

lemma prod_mom_eq_zero_of_exists_odd {m : ℕ} (a b c d : Fin m)
    (h : ∃ i, Odd (mult4 a b c d i)) :
    ∏ i, ∫ x : ℝ, x ^ mult4 a b c d i ∂gaussianReal 0 1 = 0 := by
  classical
  obtain ⟨i, hi⟩ := h
  rw [Finset.prod_eq_zero (Finset.mem_univ i)]
  have hle : mult4 a b c d i ≤ 4 := mult4_le a b c d i
  rw [gauss_int_pow_le4 _ hle]
  have : mult4 a b c d i ≠ 0 ∧ mult4 a b c d i ≠ 2 ∧ mult4 a b c d i ≠ 4 := by
    refine ⟨?_, ?_, ?_⟩
    · intro hh
      rw [hh] at hi
      exact Nat.not_odd_zero hi
    · intro hh
      rw [hh] at hi
      exact absurd hi (by decide)
    · intro hh
      rw [hh] at hi
      exact absurd hi (by decide)
  rcases this with ⟨h0, h2, h4⟩
  simp [h0, h2, h4]

lemma mult4_of_all_eq {m : ℕ} (a : Fin m) (i : Fin m) :
    mult4 a a a a i = if i = a then 4 else 0 := by
  unfold mult4
  by_cases hi : i = a
  · subst hi
    simp
  · simp [hi]

lemma prod_mom_all_eq {m : ℕ} (a : Fin m) :
    ∏ i, ∫ x : ℝ, x ^ mult4 a a a a i ∂gaussianReal 0 1 = 3 := by
  classical
  have hsplit : ∏ i, ∫ x : ℝ, x ^ mult4 a a a a i ∂gaussianReal 0 1
      = (∫ x : ℝ, x ^ mult4 a a a a a ∂gaussianReal 0 1)
        * ∏ i ∈ (Finset.univ.erase a), ∫ x : ℝ, x ^ mult4 a a a a i ∂gaussianReal 0 1 := by
    rw [← Finset.mul_prod_erase (s := Finset.univ) _ (a := a) (Finset.mem_univ a)]
  have hself : mult4 a a a a a = 4 := by
    unfold mult4; simp
  have hother : ∀ i ∈ Finset.univ.erase a, mult4 a a a a i = 0 := by
    intro i hi
    have : i ≠ a := by
      intro hh
      simp [hh] at hi
    unfold mult4
    simp [this]
  rw [hsplit, hself, gauss_int_fourth]
  have hrest : ∏ i ∈ (Finset.univ.erase a), ∫ x : ℝ, x ^ mult4 a a a a i ∂gaussianReal 0 1 = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    rw [hother i hi]
    simp
  rw [hrest]
  ring

lemma mult4_xx_yy {m : ℕ} (x y : Fin m) (h : x ≠ y) (i : Fin m) :
    mult4 x x y y i = (if i = x then 2 else 0) + (if i = y then 2 else 0) := by
  unfold mult4
  by_cases hx : i = x <;> by_cases hy : i = y <;> simp [hx, hy, h, h.symm]

lemma mult4_xy_xy {m : ℕ} (x y : Fin m) (h : x ≠ y) (i : Fin m) :
    mult4 x y x y i = (if i = x then 2 else 0) + (if i = y then 2 else 0) := by
  unfold mult4
  by_cases hx : i = x <;> by_cases hy : i = y <;> simp [hx, hy, h, h.symm]

lemma mult4_xy_yx {m : ℕ} (x y : Fin m) (h : x ≠ y) (i : Fin m) :
    mult4 x y y x i = (if i = x then 2 else 0) + (if i = y then 2 else 0) := by
  unfold mult4
  by_cases hx : i = x <;> by_cases hy : i = y <;> simp [hx, hy, h, h.symm]

lemma prod_mom_of_pair_pair {m : ℕ} (x y : Fin m) (h : x ≠ y)
    (k : Fin m → ℕ) (hk : ∀ i, k i = (if i = x then 2 else 0) + (if i = y then 2 else 0)) :
    ∏ i, ∫ z : ℝ, z ^ k i ∂gaussianReal 0 1 = 1 := by
  classical
  have hx : k x = 2 := by
    rw [hk]
    have : ¬(x = y) := h
    simp [this]
  have hy : k y = 2 := by
    rw [hk]
    have : ¬(y = x) := Ne.symm h
    simp [this]
  have hz : ∀ i, i ≠ x → i ≠ y → k i = 0 := by
    intro i hix hiy
    rw [hk]; simp [hix, hiy]
  apply Finset.prod_eq_one
  intro i _
  by_cases hix : i = x
  · subst hix; rw [hx, gauss_int_sq]
  by_cases hiy : i = y
  · subst hiy; rw [hy, gauss_int_sq]
  · rw [hz i hix hiy]; simp

lemma prod_mom_xx_yy {m : ℕ} (x y : Fin m) (h : x ≠ y) :
    ∏ i, ∫ z : ℝ, z ^ mult4 x x y y i ∂gaussianReal 0 1 = 1 :=
  prod_mom_of_pair_pair x y h _ (mult4_xx_yy x y h)

lemma prod_mom_xy_xy {m : ℕ} (x y : Fin m) (h : x ≠ y) :
    ∏ i, ∫ z : ℝ, z ^ mult4 x y x y i ∂gaussianReal 0 1 = 1 :=
  prod_mom_of_pair_pair x y h _ (mult4_xy_xy x y h)

lemma prod_mom_xy_yx {m : ℕ} (x y : Fin m) (h : x ≠ y) :
    ∏ i, ∫ z : ℝ, z ^ mult4 x y y x i ∂gaussianReal 0 1 = 1 :=
  prod_mom_of_pair_pair x y h _ (mult4_xy_yx x y h)

/-- The fourth Wick moment: `E[ξ_a ξ_b ξ_c ξ_d] = δ_ab δ_cd + δ_ac δ_bd + δ_ad δ_bc`. -/
theorem wick_four {m : ℕ} (a b c d : Fin m) :
    (∫ ω : Fin m → ℝ, ω a * ω b * ω c * ω d ∂stdGaussianMeasure m)
      = (if a = b then 1 else 0) * (if c = d then 1 else 0)
        + (if a = c then 1 else 0) * (if b = d then 1 else 0)
        + (if a = d then 1 else 0) * (if b = c then 1 else 0) := by
  rw [integral_prod_as_powers]
  by_cases hab : a = b <;> by_cases hac : a = c <;> by_cases had : a = d <;>
    by_cases hbc : b = c <;> by_cases hbd : b = d <;> by_cases hcd : c = d
  all_goals simp_all
  · rw [prod_mom_all_eq]; norm_num
  · exact prod_mom_eq_zero_of_exists_odd c c c d
      ⟨c, by unfold mult4; simp [*]; try decide; try norm_num⟩
  · exact prod_mom_eq_zero_of_exists_odd d d c d
      ⟨d, by unfold mult4; simp [*]; try decide; try norm_num⟩
  · exact prod_mom_xx_yy b d (by assumption)
  · exact prod_mom_eq_zero_of_exists_odd b b c d
      ⟨c, by unfold mult4; simp [*]; try decide; try norm_num⟩
  · exact prod_mom_eq_zero_of_exists_odd d b d d
      ⟨b, by unfold mult4; simp [*]; try decide; try norm_num⟩
  · exact prod_mom_xy_xy c d (by assumption)
  · exact prod_mom_eq_zero_of_exists_odd c b c d
      ⟨b, by unfold mult4; simp [*]; try decide; try norm_num⟩
  · exact prod_mom_xy_yx d c (by assumption)
  · exact prod_mom_eq_zero_of_exists_odd d b c d
      ⟨b, by unfold mult4; simp [*]; try decide; try norm_num⟩
  · exact prod_mom_eq_zero_of_exists_odd a d d d
      ⟨d, by unfold mult4; simp [Ne.symm had]; try decide; try norm_num⟩
  · exact prod_mom_eq_zero_of_exists_odd a c c d
      ⟨a, by unfold mult4; simp [*, ne_comm]; try decide; try norm_num⟩
  · exact prod_mom_eq_zero_of_exists_odd a d c d
      ⟨a, by unfold mult4; simp [*, ne_comm]; try decide; try norm_num⟩
  · exact prod_mom_eq_zero_of_exists_odd a b d d
      ⟨a, by unfold mult4; simp [*, ne_comm]; try decide; try norm_num⟩
  · exact prod_mom_eq_zero_of_exists_odd a b c d
      ⟨a, by unfold mult4; simp [*, ne_comm]; try decide; try norm_num⟩

/-! ## Algebraic bounds: `n c_q ≤ q³` -/

/-- `n c_q = q(q+1)²/4 ≤ q³` for `q ≥ 1`. -/
theorem n_c_le_q_cube (q : ℕ) (hq : 0 < q) :
    ((n q : ℕ) : ℝ) * c q ≤ (q : ℝ) ^ 3 := by
  have h1 : ((n q : ℕ) : ℝ) = (q : ℝ) * ((q + 1 : ℕ) : ℝ) / 2 := by
    rw [n_mul_c, c_eq]
    field_simp
  have h2 : c q = ((q + 1 : ℕ) : ℝ) / 2 := c_eq q
  rw [h1, h2]
  have hq1 : (0:ℝ) < q := by exact_mod_cast hq
  have hq1' : (1:ℝ) ≤ q := by exact_mod_cast (Nat.succ_le_of_lt hq)
  have hqp : (0:ℝ) ≤ q + 1 := by positivity
  have hkey : (0:ℝ) ≤ 3 * (q:ℝ) ^ 2 - 2 * (q:ℝ) - 1 := by
    have hk1 : (0:ℝ) ≤ 3 * (q:ℝ) + 1 := by nlinarith
    have hk2 : (0:ℝ) ≤ (q:ℝ) - 1 := by nlinarith
    nlinarith [mul_nonneg hk1 hk2]
  field_simp
  push_cast at *
  nlinarith [hkey]

theorem n_c_le_q_cube' (q : ℕ) :
    ((n q : ℕ) : ℝ) * c q ≤ (q : ℝ) ^ 3 := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    simp [n_eq, c_eq]
  · exact n_c_le_q_cube q hq

/-- Proposition 2.4, first bound: `3 n c_q ≤ 3q³`. -/
theorem prop_2_4_quartic_dimension (q : ℕ) :
    3 * ((n q : ℕ) : ℝ) * c q ≤ 3 * (q : ℝ) ^ 3 := by
  have := n_c_le_q_cube' q
  nlinarith

/-- Proposition 2.4, second bound constant: `27 n c_q ≤ 27 q³`. -/
theorem prop_2_4_cubic_dimension (q : ℕ) :
    27 * ((n q : ℕ) : ℝ) * c q ≤ 27 * (q : ℝ) ^ 3 := by
  have := prop_2_4_quartic_dimension q
  nlinarith [this]

/-! ## Trace of products of PSD matrices -/

/-- `Tr(Ψ²) - Tr(B²) = Tr((Ψ-B)(Ψ+B)) ≥ 0` when `B ≼ Ψ` and `Ψ ± B` PSD. -/
theorem trace_sq_mono {B Ψ : Matrix (Fin q) (Fin q) ℝ}
    (hB : B.PosSemidef) (hΨ : Ψ.PosSemidef) (hle : (Ψ - B).PosSemidef) :
    Matrix.trace (B * B) ≤ Matrix.trace (Ψ * Ψ) := by
  have hsum : (Ψ + B).PosSemidef := hΨ.add hB
  have hprod : (0:ℝ) ≤ Matrix.trace ((Ψ - B) * (Ψ + B)) :=
    trace_mul_nonneg hle hsum
  have key : Matrix.trace ((Ψ - B) * (Ψ + B))
      = Matrix.trace (Ψ * Ψ) - Matrix.trace (B * B) := by
    have e1 : (Ψ - B) * (Ψ + B) = (Ψ * Ψ - B * Ψ) + (Ψ * B - B * B) := by
      rw [Matrix.mul_add, Matrix.sub_mul, Matrix.sub_mul]
    rw [e1, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub]
    have e2 : Matrix.trace (Ψ * B) = Matrix.trace (B * Ψ) :=
      Matrix.trace_mul_comm Ψ B
    rw [e2]
    ring
  linarith

/-- Every scalar Gaussian power is integrable. -/
theorem integrable_std_pow (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) := by
  exact integrable_pow_of_mem_interior_integrableExpSet
    (by simp [integrableExpSet_fun_id_gaussianReal]) k

/-- All coordinate monomials of finite degree are integrable. -/
theorem integrable_gaussian_monomial {m : ℕ} (k : Fin m → ℕ) :
    Integrable (fun ω : Fin m → ℝ => ∏ i, ω i ^ k i) (stdGaussianMeasure m) :=
  Integrable.fintype_prod (fun i => integrable_std_pow (k i))

theorem integrable_wick_four {m : ℕ} (a b c d : Fin m) :
    Integrable (fun ω : Fin m → ℝ => ω a * ω b * ω c * ω d) (stdGaussianMeasure m) := by
  simpa only [prod_as_powers] using integrable_gaussian_monomial (mult4 a b c d)

/-- A centered Gaussian matrix represented in independent standard Gaussian coordinates. -/
def gaussianMatrix {m : ℕ} (B : Fin m → Matrix (Fin q) (Fin q) ℝ) (ω : Fin m → ℝ) :
    Matrix (Fin q) (Fin q) ℝ := ∑ a, ω a • B a

/-- Exact expansion of the fourth trace power, before taking expectation. -/
theorem trace_gaussianMatrix_four {m : ℕ} (B : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (ω : Fin m → ℝ) :
    Matrix.trace (gaussianMatrix B ω ^ 4) =
      ∑ a, ∑ b, ∑ c, ∑ d, (ω a * ω b * ω c * ω d) *
        Matrix.trace (B a * B b * B c * B d) := by
  have hexp : gaussianMatrix B ω ^ 4 =
      ∑ a, ∑ b, ∑ c, ∑ d, (ω a * ω b * ω c * ω d) • (B a * B b * B c * B d) := by
    rw [show gaussianMatrix B ω ^ 4 = gaussianMatrix B ω * gaussianMatrix B ω *
      gaussianMatrix B ω * gaussianMatrix B ω by simp [pow_succ]]
    unfold gaussianMatrix
    simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [sum_four_reverse]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    congr 1 <;> first | ring | rfl
  rw [hexp]
  simp only [Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]

/-- All fourth trace powers of Gaussian matrix linear combinations are integrable. -/
theorem integrable_trace_gaussianMatrix_four {m : ℕ} (B : Fin m → Matrix (Fin q) (Fin q) ℝ) :
    Integrable (fun ω => Matrix.trace (gaussianMatrix B ω ^ 4)) (stdGaussianMeasure m) := by
  simp_rw [trace_gaussianMatrix_four]
  exact integrable_finset_sum _ (fun a _ => integrable_finset_sum _ (fun b _ =>
    integrable_finset_sum _ (fun c _ => integrable_finset_sum _ (fun d _ =>
      (integrable_wick_four a b c d).mul_const _))))

/-- Expansion (14) for the actual Gaussian integral, preserving the order of matrix factors. -/
theorem fourth_moment_expansion {m : ℕ} (B : Fin m → Matrix (Fin q) (Fin q) ℝ) :
    (∫ ω, Matrix.trace (gaussianMatrix B ω ^ 4) ∂stdGaussianMeasure m) =
      2 * Matrix.trace ((∑ a, B a * B a) * (∑ a, B a * B a)) +
      ∑ a, ∑ b, Matrix.trace (B a * B b * B a * B b) := by
  simp_rw [trace_gaussianMatrix_four]
  rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ (fun b _ =>
    integrable_finset_sum _ (fun c _ => integrable_finset_sum _ (fun d _ =>
      (integrable_wick_four a b c d).mul_const _))))]
  simp_rw [integral_finset_sum _ (fun b _ => integrable_finset_sum _ (fun c _ =>
    integrable_finset_sum _ (fun d _ => (integrable_wick_four _ b c d).mul_const _)))]
  simp_rw [integral_finset_sum _ (fun c _ => integrable_finset_sum _ (fun d _ =>
    (integrable_wick_four _ _ c d).mul_const _))]
  simp_rw [integral_finset_sum _ (fun d _ => (integrable_wick_four _ _ _ d).mul_const _)]
  simp_rw [integral_mul_const, wick_four, add_mul, Finset.sum_add_distrib]
  simp only [ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hcy : ∀ a b, Matrix.trace (B a * B b * B b * B a) =
      Matrix.trace (B a * B a * B b * B b) := by
    intro a b
    rw [Matrix.trace_mul_cycle]
    simp only [Matrix.mul_assoc]
  simp only [Finset.sum_const_zero, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  try simp_rw [hcy]
  have hsum : (∑ a, ∑ b, Matrix.trace (B a * B a * B b * B b)) =
      Matrix.trace ((∑ a, B a * B a) * (∑ a, B a * B a)) := by
    simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
    rw [Finset.sum_comm]
  rw [hsum]
  ring

/-- Fourth-moment estimate for any Gaussian matrix coefficient family with a PSD square bound. -/
theorem fourth_moment_le {m : ℕ} (B : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hB : ∀ a, (B a).IsSymm) (Ψ : Matrix (Fin q) (Fin q) ℝ)
    (hΨ : Ψ.PosSemidef) (hle : (Ψ - ∑ a, B a * B a).PosSemidef) :
    (∫ ω, Matrix.trace (gaussianMatrix B ω ^ 4) ∂stdGaussianMeasure m) ≤
      3 * Matrix.trace (Ψ * Ψ) := by
  rw [fourth_moment_expansion]
  have h1 := lemma_2_3_first B hB
  have h2 := lemma_2_3_second B Ψ hΨ hB hle
  have h3 : (∑ a, ∑ b, Matrix.trace (B a * B b * B a * B b)) ≤
      ∑ a, ∑ b, |Matrix.trace (B a * B b * B a * B b)| :=
    Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => le_abs_self _))
  linarith

/-- A covariance contraction in an arbitrary orthonormal eigenbasis has bounded square sum. -/
theorem gaussian_coeff_square_bound {m : ℕ} (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hF : OrthonormalFrob F) (σ : Fin m → ℝ) (hσ : ∀ a, 0 ≤ σ a ∧ σ a ≤ 1) :
    (c q • oneMat q - ∑ a, (σ a • F a) * (σ a • F a)).PosSemidef := by
  have he : c q • oneMat q - ∑ a, (σ a • F a) * (σ a • F a) =
      ∑ a, (1 - σ a ^ 2) • (F a * F a) := by
    rw [← sum_squares_orthonormal F hF, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sub_smul, one_smul, pow_two]
  rw [he]
  have hh : (0 : Matrix (Fin q) (Fin q) ℝ) ≤ ∑ a, (1 - σ a ^ 2) • (F a * F a) := by
    apply Finset.sum_nonneg
    intro a _
    have hs : (F a * F a).PosSemidef := by
      have ht : (F a)ᴴ = F a := by
        simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hF.1 a
      simpa only [ht] using Matrix.posSemidef_conjTranspose_mul_self (F a)
    have hc : 0 ≤ 1 - σ a ^ 2 := by nlinarith [(hσ a).1, (hσ a).2]
    exact (hs.smul hc).nonneg
  exact hh.posSemidef

/-- Proposition 2.4: the quartic Gaussian trace bound, in arbitrary covariance eigenmodes. -/
theorem prop_2_4_quartic {m : ℕ} (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hF : OrthonormalFrob F) (σ : Fin m → ℝ) (hσ : ∀ a, 0 ≤ σ a ∧ σ a ≤ 1) :
    (∫ ω, Matrix.trace (gaussianMatrix (fun a => σ a • F a) ω ^ 4)
      ∂stdGaussianMeasure m) ≤ 3 * (n q : ℝ) * c q := by
  have hc : (c q • oneMat q).PosSemidef := Matrix.PosSemidef.one.smul (c_pos q).le
  have hb := fourth_moment_le (fun a => σ a • F a) (fun a => (hF.1 a).smul (σ a))
    (c q • oneMat q) hc (gaussian_coeff_square_bound F hF σ hσ)
  have he : 3 * Matrix.trace ((c q • oneMat q) * (c q • oneMat q)) =
      3 * (n q : ℝ) * c q := by
    simp only [oneMat, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      smul_smul, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    rw [n_mul_c]
    ring
  rwa [he] at hb

end Paper10
