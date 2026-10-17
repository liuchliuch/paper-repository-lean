import Paper34.TensorNorming
import Mathlib.Tactic.LinearCombination

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory Set
namespace Paper34.TensorNorming
open Paper34.Kernel Paper34.LocalSupremum

lemma integral_derivative_zero (f f' : C(Torus, ℂ))
    (hder : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (s : Torus)) (f' (t : Torus)) t) :
    (∫ x : Torus, f' x ∂haar) = 0 := by
  have hcont : Continuous (fun t : ℝ => f' (t : Torus)) :=
    f'.continuous.comp (AddCircle.continuous_mk' (2 * Real.pi))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (0 : ℝ) (2 * Real.pi)) => hder t)
    (hcont.intervalIntegrable 0 (2 * Real.pi))
  have hperiod : ((2 * Real.pi : ℝ) : Torus) = 0 := AddCircle.coe_period _
  have hzero : ((0 : ℝ) : Torus) = 0 := rfl
  rw [hperiod, hzero, sub_self] at hFTC
  rw [integral_lift f'] at hFTC
  have hT0 : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (show 2 * Real.pi ≠ 0 by positivity)
  exact (mul_eq_zero.mp hFTC).resolve_left hT0

/-- Fourier differentiation is derived from the fundamental theorem of calculus
and periodic boundary cancellation, for the actual continuous torus functions. -/
lemma derivative_fourierCoeff (f f' : C(Torus, ℂ))
    (hder : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (s : Torus)) (f' (t : Torus)) t)
    (k : ℤ) : fourierCoeff f' k = ((k : ℂ) * Complex.I) * fourierCoeff f k := by
  let G : C(Torus, ℂ) :=
    (-((k : ℂ) * Complex.I)) • (fourier (-k) * f) + fourier (-k) * f'
  have hG (t : ℝ) : HasDerivAt (fun s : ℝ => fourier (-k) (s : Torus) * f (s : Torus))
      (G (t : Torus)) t := by
    have h := (hasDerivAt_fourier_angular (-k) t).mul (hder t)
    convert h using 1
    simp only [G, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      ContinuousMap.mul_apply, smul_eq_mul, Int.cast_neg]
    ring
  have hzero : (∫ x : Torus, G x ∂haar) = 0 :=
    integral_derivative_zero (fourier (-k) * f) G hG
  have hsplit : (∫ x : Torus, G x ∂haar) =
      -((k : ℂ) * Complex.I) * fourierCoeff f k + fourierCoeff f' k := by
    simp only [G, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      ContinuousMap.mul_apply, smul_eq_mul]
    rw [integral_add, integral_const_mul]
    · rfl
    · exact (continuous_const.mul ((fourier (-k)).continuous.mul f.continuous)).integrable_of_hasCompactSupport
        (μ := haar) (HasCompactSupport.of_compactSpace _)
    · exact ((fourier (-k)).continuous.mul f'.continuous).integrable_of_hasCompactSupport
        (μ := haar) (HasCompactSupport.of_compactSpace _)
  rw [hsplit] at hzero
  linear_combination hzero

/-- One differentiated factor in the product reproducing kernel. -/
def derivativeKernel (n d : ℕ) (i : Fin n) : C(TorusN n, ℂ) :=
  productKernel (fun j => if j = i then valleePoussinDerivative d else valleePoussin d)

lemma convolution_eq_sum {n d : ℕ} (H : TrigPolynomial n d) (g : Fin n → C(Torus, ℂ))
    (x : TorusN n) :
    (∫ u : TorusN n, H.eval u * productKernel g (x - u) ∂haarN n) =
      ∑ k ∈ H.frequencies, H.coeff k * (monomial k x * ∏ i, fourierCoeff (g i) (k i)) := by
  simp only [TrigPolynomial.eval, TrigPolynomial.toContinuousMap, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [integral_const_mul, integral_monomial_productKernel]
  · intro k hk
    exact (continuous_const.mul ((monomial k).continuous.mul
      ((productKernel g).continuous.comp (continuous_const.sub continuous_id)))).integrable_of_hasCompactSupport
      (μ := haarN n) (HasCompactSupport.of_compactSpace _)

theorem reproduce_partial {n d : ℕ} (H : TrigPolynomial n d) (hd : 1 ≤ d)
    (i : Fin n) (x : TorusN n) :
    (∫ u : TorusN n, H.eval u * derivativeKernel n d i (x - u) ∂haarN n) =
      (H.partial i).eval x := by
  rw [derivativeKernel, convolution_eq_sum]
  simp only [TrigPolynomial.eval, TrigPolynomial.toContinuousMap, TrigPolynomial.partial,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hcoeff (j : Fin n) :
      fourierCoeff ((if j = i then valleePoussinDerivative d else valleePoussin d) : C(Torus, ℂ)) (k j) =
        if j = i then ((k i : ℂ) * Complex.I) else 1 := by
    split_ifs with hji
    · subst j
      rw [derivative_fourierCoeff _ _ (hasDerivAt_valleePoussin d),
        valleePoussin_coeff d hd _ (H.degree k hk i), mul_one]
    · exact valleePoussin_coeff d hd _ (H.degree k hk j)
  simp_rw [hcoeff]
  rw [Finset.prod_ite_eq']
  simp only [Finset.mem_univ, if_true]
  ring

lemma derivativeKernel_L1 {n d : ℕ} (hd : 1 ≤ d) (i : Fin n) :
    (∫ x : TorusN n, ‖derivativeKernel n d i x‖ ∂haarN n) ≤
      (10 * d : ℝ) * 3 ^ (n - 1) := by
  let g : Fin n → C(Torus, ℂ) := fun j =>
    if j = i then valleePoussinDerivative d else valleePoussin d
  let A : Fin n → ℝ := fun j => ∫ x : Torus, ‖g j x‖ ∂haar
  have hprod : (∫ x : TorusN n, ‖derivativeKernel n d i x‖ ∂haarN n) = ∏ j, A j := by
    simp only [derivativeKernel, productKernel, ContinuousMap.coe_mk, norm_prod]
    exact integral_fintype_prod_eq_prod (μ := fun _ => haar) (fun j x => ‖g j x‖)
  have hA (j : Fin n) : 0 ≤ A j := integral_nonneg fun _ => norm_nonneg _
  rw [hprod, ← Finset.mul_prod_erase _ A (Finset.mem_univ i)]
  have hAi : A i ≤ 10 * d := by
    simpa only [A, g, if_pos rfl] using valleePoussinDerivative_L1 d hd
  have hAj (j : Fin n) (hj : j ∈ Finset.univ.erase i) : A j ≤ 3 := by
    have hji := (Finset.mem_erase.mp hj).1
    simpa only [A, g, if_neg hji] using valleePoussin_L1 d hd
  calc
    A i * ∏ j ∈ Finset.univ.erase i, A j ≤
        (10 * d : ℝ) * ∏ _j ∈ Finset.univ.erase i, (3 : ℝ) := by
      apply mul_le_mul hAi
      · exact Finset.prod_le_prod (fun j _ => hA j) hAj
      · exact Finset.prod_nonneg fun j _ => hA j
      · positivity
    _ = _ := by simp

/-- Endpoint `L¹` Bernstein, equation (3.5), for actual bounded-degree Fourier
polynomials. Fubini is used on the actual continuous convolution integrand. -/
theorem partial_L1 {n d : ℕ} (H : TrigPolynomial n d) (hd : 1 ≤ d) (i : Fin n) :
    (∫ x : TorusN n, ‖(H.partial i).eval x‖ ∂haarN n) ≤
      (10 * 3 ^ (n - 1) : ℝ) * d * ∫ u : TorusN n, ‖H.eval u‖ ∂haarN n := by
  let F (x u : TorusN n) : ℝ := ‖H.eval u‖ * ‖derivativeKernel n d i (x - u)‖
  have hF : Integrable (Function.uncurry F) ((haarN n).prod (haarN n)) :=
    (((continuous_eval H).comp continuous_snd).norm.mul
      ((derivativeKernel n d i).continuous.comp (continuous_fst.sub continuous_snd)).norm).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpoint (x : TorusN n) : ‖(H.partial i).eval x‖ ≤ ∫ u, F x u ∂haarN n := by
    rw [← reproduce_partial H hd i x]
    simpa only [norm_mul] using norm_integral_le_integral_norm
      (fun u : TorusN n => H.eval u * derivativeKernel n d i (x - u))
  have h := integral_mono (integrable_continuousN (H.partial i).toContinuousMap).norm
    hF.integral_prod_left hpoint
  have htrans (u : TorusN n) :
      (∫ x : TorusN n, ‖derivativeKernel n d i (x - u)‖ ∂haarN n) =
        ∫ x : TorusN n, ‖derivativeKernel n d i x‖ ∂haarN n :=
    integral_sub_right_eq_self (μ := haarN n) (fun x : TorusN n => ‖derivativeKernel n d i x‖) u
  simp only [Function.uncurry] at h
  rw [integral_integral_swap hF] at h
  simp only [F] at h
  simp_rw [integral_const_mul, htrans] at h
  rw [integral_mul_const] at h
  calc
    _ ≤ (∫ u : TorusN n, ‖H.eval u‖ ∂haarN n) *
        (∫ x : TorusN n, ‖derivativeKernel n d i x‖ ∂haarN n) := h
    _ ≤ (∫ u : TorusN n, ‖H.eval u‖ ∂haarN n) * ((10 * d : ℝ) * 3 ^ (n - 1)) :=
      mul_le_mul_of_nonneg_left (derivativeKernel_L1 hd i) (integral_nonneg fun _ => norm_nonneg _)
    _ = _ := by ring

/-- Lemma 3.2, with an explicit common dimension-dependent constant. -/
theorem local_supremum_and_endpoint_Bernstein {n d m : ℕ} (H : TrigPolynomial n d)
    (hd : 1 ≤ d) (hm : d ≤ m) :
    let B : ℝ := (3 + 10 * Real.pi) ^ n + 10 * 3 ^ (n - 1)
    (gridWeight m ^ n * ∑ j : GridIndex n m, cellSup H.toContinuousMap j ≤
      B * ∫ u : TorusN n, ‖H.eval u‖ ∂haarN n) ∧
    (∀ i : Fin n, (∫ x : TorusN n, ‖(H.partial i).eval x‖ ∂haarN n) ≤
      B * d * ∫ u : TorusN n, ‖H.eval u‖ ∂haarN n) := by
  dsimp
  have hnorm : 0 ≤ ∫ u : TorusN n, ‖H.eval u‖ ∂haarN n := integral_nonneg fun _ => norm_nonneg _
  constructor
  · have h := local_supremum_bound H hd hm
    have hc : (0 : ℝ) ≤ 10 * 3 ^ (n - 1) := by positivity
    nlinarith
  · intro i
    have h := partial_L1 H hd i
    have hc : (0 : ℝ) ≤ (3 + 10 * Real.pi) ^ n := by positivity
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith [mul_nonneg hc (mul_nonneg hd0 hnorm)]

end Paper34.TensorNorming
