import Paper34.LocalSupremum
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.LinearCombination

/-!
# Actual finite Fourier polynomials and product reproducing kernels

All Fourier coefficients and convolutions are actual normalized Haar integrals.
The frequency support is finite and the coordinate degree bound is explicit.
-/

noncomputable section

open scoped BigOperators ComplexConjugate
open MeasureTheory Set

namespace Paper34.TensorNorming

open Paper34.Kernel Paper34.LocalSupremum

abbrev TorusN (n : ℕ) := Fin n → Torus
abbrev haarN (n : ℕ) : Measure (TorusN n) := Measure.pi (fun _ => haar)

/-- A genuine exponential monomial on the product torus. -/
def monomial {n : ℕ} (k : Fin n → ℤ) : C(TorusN n, ℂ) where
  toFun x := ∏ i, fourier (k i) (x i)
  continuous_toFun := continuous_finset_prod _ fun i _ =>
    (fourier (k i)).continuous.comp (continuous_apply i)

/-- The source coordinate degree condition on an actual finite Fourier sum. -/
structure TrigPolynomial (n d : ℕ) where
  frequencies : Finset (Fin n → ℤ)
  coeff : (Fin n → ℤ) → ℂ
  degree : ∀ k ∈ frequencies, ∀ i, (k i).natAbs ≤ d

/-- Evaluation is a finite sum of actual continuous torus functions. -/
def TrigPolynomial.toContinuousMap {n d : ℕ} (H : TrigPolynomial n d) : C(TorusN n, ℂ) :=
  ∑ k ∈ H.frequencies, H.coeff k • monomial k

def TrigPolynomial.eval {n d : ℕ} (H : TrigPolynomial n d) (x : TorusN n) : ℂ :=
  H.toContinuousMap x

lemma continuous_eval {n d : ℕ} (H : TrigPolynomial n d) : Continuous H.eval :=
  H.toContinuousMap.continuous

lemma integrable_continuousN {n : ℕ} (f : C(TorusN n, ℂ)) : Integrable f (haarN n) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma fourier_sub (k : ℤ) (x u : Torus) :
    fourier k (x - u) = fourier k x * fourier (-k) u := by
  change (AddCircle.toCircle (k • (x - u)) : ℂ) =
    (AddCircle.toCircle (k • x) : ℂ) * (AddCircle.toCircle ((-k) • u) : ℂ)
  rw [smul_sub, sub_eq_add_neg, AddCircle.toCircle_add, Circle.coe_mul, neg_smul]

/-- Reproduction of one Fourier monomial by a real convolution integral. -/
lemma integral_fourier_kernel (g : C(Torus, ℂ)) (k : ℤ) (x : Torus) :
    (∫ u : Torus, fourier k u * g (x - u) ∂haar) =
      fourier k x * fourierCoeff g k := by
  have hchange := integral_sub_left_eq_self
    (fun u : Torus => fourier k (x - u) * g u) haar x
  simp only [sub_sub_cancel] at hchange
  rw [hchange]
  simp_rw [fourier_sub, mul_assoc]
  rw [integral_const_mul]
  rfl

/-- A separable product kernel, without any assigned Fourier data. -/
def productKernel {n : ℕ} (g : Fin n → C(Torus, ℂ)) : C(TorusN n, ℂ) where
  toFun x := ∏ i, g i (x i)
  continuous_toFun := continuous_finset_prod _ fun i _ =>
    (g i).continuous.comp (continuous_apply i)

/-- The product multiplier identity is proved by actual finite-dimensional Fubini. -/
lemma integral_monomial_productKernel {n : ℕ} (g : Fin n → C(Torus, ℂ))
    (k : Fin n → ℤ) (x : TorusN n) :
    (∫ u : TorusN n, monomial k u * productKernel g (x - u) ∂haarN n) =
      monomial k x * ∏ i, fourierCoeff (g i) (k i) := by
  simp only [monomial, productKernel, ContinuousMap.coe_mk, Pi.sub_apply,
    ← Finset.prod_mul_distrib]
  calc
    _ = ∏ i : Fin n, ∫ u : Torus, fourier (k i) u * g i (x i - u) ∂haar :=
      integral_fintype_prod_eq_prod (μ := fun _ => haar) (fun i u => fourier (k i) u * g i (x i - u))
    _ = _ := by simp_rw [integral_fourier_kernel]

/-- Genuine convolution reproduction of every source finite Fourier polynomial. -/
theorem reproduce {n d : ℕ} (H : TrigPolynomial n d) (g : Fin n → C(Torus, ℂ))
    (hg : ∀ i (k : ℤ), k.natAbs ≤ d → fourierCoeff (g i) k = 1) (x : TorusN n) :
    (∫ u : TorusN n, H.eval u * productKernel g (x - u) ∂haarN n) = H.eval x := by
  simp only [TrigPolynomial.eval, TrigPolynomial.toContinuousMap, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [integral_const_mul, integral_monomial_productKernel]
    have hprod : (∏ i : Fin n, fourierCoeff (g i) (k i)) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      exact hg i (k i) (H.degree k hk i)
    rw [hprod, mul_one]
  · intro k hk
    exact (continuous_const.mul ((monomial k).continuous.mul
      ((productKernel g).continuous.comp (continuous_const.sub continuous_id)))).integrable_of_hasCompactSupport
      (μ := haarN n) (HasCompactSupport.of_compactSpace _)

/-- The product de la Vallée Poussin kernel in the source proof. -/
def valleeProduct (n d : ℕ) : C(TorusN n, ℂ) := productKernel (fun _ => valleePoussin d)

theorem reproduce_vallee {n d : ℕ} (H : TrigPolynomial n d) (hd : 1 ≤ d) (x : TorusN n) :
    (∫ u : TorusN n, H.eval u * valleeProduct n d (x - u) ∂haarN n) = H.eval x :=
  reproduce H (fun _ => valleePoussin d) (fun _ k hk => valleePoussin_coeff d hd k hk) x

abbrev GridIndex (n m : ℕ) := Fin n → Fin (2 * m)

def gridWeight (m : ℕ) : ℝ := (Real.pi / m) / (2 * Real.pi)

def angularPoint {n : ℕ} (theta : Fin n → ℝ) : TorusN n := fun i => (theta i : Torus)

def gridCell {n m : ℕ} (j : GridIndex n m) : Set (Fin n → ℝ) :=
  Icc (fun i => (j i : ℕ) * (Real.pi / m))
    (fun i => ((j i : ℕ) + 1 : ℝ) * (Real.pi / m))

lemma continuous_angularPoint (n : ℕ) : Continuous (@angularPoint n) :=
  continuous_pi fun i => (AddCircle.continuous_mk' (2 * Real.pi)).comp (continuous_apply i)

lemma gridCell_nonempty {n m : ℕ} (j : GridIndex n m) : (gridCell j).Nonempty := by
  refine ⟨fun i => (j i : ℕ) * (Real.pi / m), le_rfl, ?_⟩
  intro i
  have h : 0 ≤ Real.pi / (m : ℝ) := by positivity
  dsimp
  nlinarith

/-- This tensorization concerns the kernel alone. The chosen point in a cell
may depend jointly on its entire multi-index. -/
theorem representative_kernel_sum {n d m : ℕ} (hd : 1 ≤ d) (hm : d ≤ m)
    (r : GridIndex n m → Fin n → ℝ) (hr : ∀ j, r j ∈ gridCell j) (u : TorusN n) :
    gridWeight m ^ n * ∑ j : GridIndex n m,
      ‖valleeProduct n d (angularPoint (r j) - u)‖ ≤ (3 + 10 * Real.pi) ^ n := by
  let A (i : Fin n) (a : Fin (2 * m)) : ℝ :=
    intervalSup (shiftLift (valleePoussin d) (u i))
      ((a : ℕ) * (Real.pi / m)) (((a : ℕ) + 1 : ℝ) * (Real.pi / m))
  have hA0 (i : Fin n) (a : Fin (2 * m)) : 0 ≤ A i a := by
    have hbound := norm_le_intervalSup (continuous_shiftLift (valleePoussin d) (u i))
      (show ((a : ℕ) : ℝ) * (Real.pi / m) ∈
        Icc ((a : ℕ) * (Real.pi / m)) (((a : ℕ) + 1 : ℝ) * (Real.pi / m)) by
          constructor
          · exact le_rfl
          · have : 0 ≤ Real.pi / (m : ℝ) := by positivity
            nlinarith)
    exact (norm_nonneg _).trans hbound
  have hcoord (i : Fin n) : gridWeight m * ∑ a : Fin (2 * m), A i a ≤
      3 + 10 * Real.pi := by
    dsimp [A]
    change gridWeight m * (∑ a : Fin (2 * m),
      (fun a : ℕ => intervalSup (shiftLift (valleePoussin d) (u i))
        ((a : ℝ) * (Real.pi / m)) (((a : ℝ) + 1) * (Real.pi / m))) (a : ℕ)) ≤ _
    rw [Fin.sum_univ_eq_sum_range (fun a : ℕ =>
      intervalSup (shiftLift (valleePoussin d) (u i))
        ((a : ℝ) * (Real.pi / m)) (((a : ℝ) + 1) * (Real.pi / m))) (2 * m)]
    exact kernelGridSup_le d m hd hm (u i)
  have hpoint (j : GridIndex n m) :
      ‖valleeProduct n d (angularPoint (r j) - u)‖ ≤ ∏ i, A i (j i) := by
    simp only [valleeProduct, productKernel, ContinuousMap.coe_mk, norm_prod, Pi.sub_apply]
    apply Finset.prod_le_prod (fun i hi => norm_nonneg _)
    intro i hi
    exact norm_le_intervalSup (continuous_shiftLift (valleePoussin d) (u i))
      ⟨(hr j).1 i, (hr j).2 i⟩
  have hw : 0 ≤ gridWeight m := by unfold gridWeight; positivity
  calc
    _ ≤ gridWeight m ^ n * ∑ j : GridIndex n m, ∏ i, A i (j i) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hpoint j) (pow_nonneg hw n)
    _ = ∏ i : Fin n, (gridWeight m * ∑ a : Fin (2 * m), A i a) := by
      rw [Finset.prod_mul_distrib, ← Fintype.prod_sum]
      simp
    _ ≤ ∏ _i : Fin n, (3 + 10 * Real.pi) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact mul_nonneg hw (Finset.sum_nonneg fun a _ => hA0 i a)
      · intro i hi
        exact hcoord i
    _ = _ := by simp

/-- The arbitrary-representative form of the source local supremum bound.
The function is reproduced before applying the product kernel estimate. -/
theorem representative_norming {n d m : ℕ} (H : TrigPolynomial n d)
    (hd : 1 ≤ d) (hm : d ≤ m) (r : GridIndex n m → Fin n → ℝ)
    (hr : ∀ j, r j ∈ gridCell j) :
    gridWeight m ^ n * ∑ j : GridIndex n m, ‖H.eval (angularPoint (r j))‖ ≤
      (3 + 10 * Real.pi) ^ n * ∫ u : TorusN n, ‖H.eval u‖ ∂haarN n := by
  let F (j : GridIndex n m) (u : TorusN n) : ℝ :=
    ‖H.eval u‖ * ‖valleeProduct n d (angularPoint (r j) - u)‖
  have hF (j : GridIndex n m) : Continuous (F j) :=
    (continuous_eval H).norm.mul ((valleeProduct n d).continuous.comp
      (continuous_const.sub continuous_id)).norm
  have hFi (j : GridIndex n m) : Integrable (F j) (haarN n) :=
    (hF j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpoint (j : GridIndex n m) : ‖H.eval (angularPoint (r j))‖ ≤
      ∫ u : TorusN n, F j u ∂haarN n := by
    rw [← reproduce_vallee H hd (angularPoint (r j))]
    simpa only [norm_mul] using norm_integral_le_integral_norm
      (fun u : TorusN n => H.eval u * valleeProduct n d (angularPoint (r j) - u))
  have hw : 0 ≤ gridWeight m := by unfold gridWeight; positivity
  calc
    _ ≤ gridWeight m ^ n * ∑ j : GridIndex n m, ∫ u, F j u ∂haarN n :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hpoint j) (pow_nonneg hw n)
    _ = ∫ u : TorusN n, gridWeight m ^ n * ∑ j : GridIndex n m, F j u ∂haarN n := by
      rw [integral_const_mul, integral_finset_sum _ (fun j _ => hFi j)]
    _ ≤ ∫ u : TorusN n, (3 + 10 * Real.pi) ^ n * ‖H.eval u‖ ∂haarN n := by
      apply integral_mono
      · exact ((continuous_const.mul (continuous_finset_sum _ fun j _ => hF j))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact (continuous_const.mul (continuous_eval H).norm).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · intro u
        have hk := representative_kernel_sum hd hm r hr u
        have hk' := mul_le_mul_of_nonneg_left hk (norm_nonneg (H.eval u))
        simpa only [F, ← Finset.mul_sum] using (show
          gridWeight m ^ n * (‖H.eval u‖ * ∑ j : GridIndex n m,
            ‖valleeProduct n d (angularPoint (r j) - u)‖) ≤
          (3 + 10 * Real.pi) ^ n * ‖H.eval u‖ by nlinarith [hk'])
    _ = _ := integral_const_mul _ _

/-- Actual cell supremum on the closed real angular box. -/
def cellSup {n : ℕ} (f : C(TorusN n, ℂ)) {m : ℕ} (j : GridIndex n m) : ℝ :=
  sSup ((fun theta => ‖f (angularPoint theta)‖) '' gridCell j)

lemma cellSup_attained {n m : ℕ} (f : C(TorusN n, ℂ)) (j : GridIndex n m) :
    ∃ theta ∈ gridCell j, ‖f (angularPoint theta)‖ = cellSup f j := by
  have hc : Continuous (fun theta : Fin n → ℝ => ‖f (angularPoint theta)‖) :=
    (f.continuous.comp (continuous_angularPoint n)).norm
  obtain ⟨theta, htheta, hmax⟩ := (isCompact_Icc : IsCompact (gridCell j)).exists_isMaxOn
    (gridCell_nonempty j) hc.continuousOn
  refine ⟨theta, htheta, ?_⟩
  change ‖f (angularPoint theta)‖ = sSup ((fun theta => ‖f (angularPoint theta)‖) '' gridCell j)
  apply le_antisymm
  · exact le_csSup (((isCompact_Icc : IsCompact (gridCell j)).image hc).bddAbove)
      ⟨theta, htheta, rfl⟩
  · apply csSup_le ((gridCell_nonempty j).image _)
    rintro y ⟨s, hs, rfl⟩
    exact hmax hs

/-- Equation (3.4), with the explicit dimension-dependent constant
`(3 + 10π)^n`, for every actual bounded-degree finite Fourier polynomial. -/
theorem local_supremum_bound {n d m : ℕ} (H : TrigPolynomial n d)
    (hd : 1 ≤ d) (hm : d ≤ m) :
    gridWeight m ^ n * ∑ j : GridIndex n m, cellSup H.toContinuousMap j ≤
      (3 + 10 * Real.pi) ^ n * ∫ u : TorusN n, ‖H.eval u‖ ∂haarN n := by
  classical
  choose r hr heq using fun j : GridIndex n m => cellSup_attained H.toContinuousMap j
  have h := representative_norming H hd hm r hr
  simpa only [TrigPolynomial.eval, heq] using h

/-- The actual Dirichlet kernel used in the source `L¹` to uniform estimate. -/
def dirichlet (d : ℕ) : C(Torus, ℂ) := ∑ k ∈ Finset.Icc (-(d : ℤ)) d, fourier k

lemma dirichlet_coeff (d : ℕ) (k : ℤ) (hk : k.natAbs ≤ d) :
    fourierCoeff (dirichlet d) k = 1 := by
  rw [dirichlet, Paper34.Kernel.fourierCoeff_sum]
  simp_rw [Paper34.Kernel.fourierCoeff_fourier]
  have hmem : k ∈ Finset.Icc (-(d : ℤ)) d := by
    simp only [Finset.mem_Icc]
    omega
  rw [Finset.sum_eq_single k]
  · simp
  · intro j hj hjk
    exact if_neg hjk
  · intro hnot
    exact (hnot hmem).elim

lemma dirichlet_norm_le (d : ℕ) (x : Torus) : ‖dirichlet d x‖ ≤ 2 * d + 1 := by
  simp only [dirichlet, ContinuousMap.sum_apply]
  calc
    _ ≤ ∑ k ∈ Finset.Icc (-(d : ℤ)) d, ‖fourier k x‖ := norm_sum_le _ _
    _ = 2 * d + 1 := by
      simp only [fourier_apply, Circle.norm_coe, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [Int.card_Icc]
      have hcard : ((d : ℤ) + 1 - -(d : ℤ)).toNat = 2 * d + 1 := by omega
      rw [hcard]
      push_cast
      rfl

lemma dirichlet_product_norm_le (n d : ℕ) (x : TorusN n) :
    ‖productKernel (fun _ : Fin n => dirichlet d) x‖ ≤ (2 * d + 1 : ℝ) ^ n := by
  simp only [productKernel, ContinuousMap.coe_mk, norm_prod]
  calc
    _ ≤ ∏ _i : Fin n, (2 * d + 1 : ℝ) :=
      Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => dirichlet_norm_le d (x i))
    _ = _ := by simp

/-- The precise Dirichlet-kernel `L¹` to uniform estimate used at (4.7). -/
theorem nikolskii {n d : ℕ} (H : TrigPolynomial n d) (x : TorusN n) :
    ‖H.eval x‖ ≤ (2 * d + 1 : ℝ) ^ n * ∫ u : TorusN n, ‖H.eval u‖ ∂haarN n := by
  have hr := reproduce H (fun _ => dirichlet d) (fun _ k hk => dirichlet_coeff d k hk) x
  calc
    _ = ‖∫ u : TorusN n, H.eval u * productKernel (fun _ => dirichlet d) (x - u) ∂haarN n‖ := by rw [hr]
    _ ≤ ∫ u : TorusN n, ‖H.eval u‖ * ‖productKernel (fun _ => dirichlet d) (x - u)‖ ∂haarN n := by
      simpa only [norm_mul] using norm_integral_le_integral_norm
        (fun u : TorusN n => H.eval u * productKernel (fun _ => dirichlet d) (x - u))
    _ ≤ ∫ u : TorusN n, ‖H.eval u‖ * (2 * d + 1 : ℝ) ^ n ∂haarN n := by
      apply integral_mono
      · exact ((continuous_eval H).norm.mul ((productKernel (fun _ => dirichlet d)).continuous.comp
          (continuous_const.sub continuous_id)).norm).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact ((continuous_eval H).norm.mul continuous_const).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · intro u
        exact mul_le_mul_of_nonneg_left (dirichlet_product_norm_le n d (x - u)) (norm_nonneg _)
    _ = _ := by rw [integral_mul_const, mul_comm]

lemma hasDerivAt_fourier_angular (k : ℤ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => fourier k (s : Torus))
      ((k : ℂ) * Complex.I * fourier k (t : Torus)) t := by
  convert hasDerivAt_fourier (2 * Real.pi) k t using 1
  congr 1
  push_cast
  field_simp <;> ring

lemma integral_lift (g : C(Torus, ℂ)) :
    (∫ t in (0 : ℝ)..2 * Real.pi, g (t : Torus)) =
      ((2 * Real.pi : ℝ) : ℂ) * ∫ x : Torus, g x ∂haar := by
  have h := AddCircle.intervalIntegral_preimage (2 * Real.pi) 0 g
  simp only [zero_add] at h
  rw [h, AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), Complex.real_smul]

/-- The coordinate derivative as another genuine finite Fourier polynomial. -/
def TrigPolynomial.partial {n d : ℕ} (H : TrigPolynomial n d) (i : Fin n) : TrigPolynomial n d where
  frequencies := H.frequencies
  coeff k := H.coeff k * ((k i : ℂ) * Complex.I)
  degree := H.degree

lemma monomial_update {n : ℕ} (k : Fin n → ℤ) (theta : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    monomial k (angularPoint (Function.update theta i t)) =
      fourier (k i) (t : Torus) * ∏ j ∈ Finset.univ.erase i, fourier (k j) (theta j : Torus) := by
  rw [monomial, ContinuousMap.coe_mk, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [angularPoint, Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

lemma hasDerivAt_monomial_update {n : ℕ} (k : Fin n → ℤ) (theta : Fin n → ℝ) (i : Fin n) :
    HasDerivAt (fun t : ℝ => monomial k (angularPoint (Function.update theta i t)))
      (((k i : ℂ) * Complex.I) * monomial k (angularPoint theta)) (theta i) := by
  simp_rw [monomial_update]
  have h := (hasDerivAt_fourier_angular (k i) (theta i)).mul_const
    (∏ j ∈ Finset.univ.erase i, fourier (k j) (theta j : Torus))
  convert h using 1
  have heq := monomial_update k theta i (theta i)
  rw [Function.update_eq_self] at heq
  rw [heq]
  ring

/-- The finite Fourier derivative agrees with the actual angular slice derivative. -/
theorem hasDerivAt_partial {n d : ℕ} (H : TrigPolynomial n d) (i : Fin n) (theta : Fin n → ℝ) :
    HasDerivAt (fun t : ℝ => H.eval (angularPoint (Function.update theta i t)))
      ((H.partial i).eval (angularPoint theta)) (theta i) := by
  simp only [TrigPolynomial.eval, TrigPolynomial.toContinuousMap, TrigPolynomial.partial,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  apply HasDerivAt.fun_sum
  intro k hk
  convert (hasDerivAt_monomial_update k theta i).const_mul (H.coeff k) using 1
  ring

end Paper34.TensorNorming
