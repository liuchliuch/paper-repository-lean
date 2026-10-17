import Paper34.TensorDerivative
import Paper34.CosineFourierLift
import Paper34.TrigBernsteinContract

/-!
# Coordinate-dependent degrees and grid sizes (Appendix A.3)

The zero-degree coordinate kernel is the actual constant function `1`.
All positive-degree kernels, convolutions and Haar measures are those already
proved for the source torus model.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory Set

namespace Paper34.Anisotropic

open Paper34.Kernel Paper34.LocalSupremum Paper34.TensorNorming

structure BoxTrigPolynomial {n : ℕ} (d : Fin n → ℕ) where
  frequencies : Finset (Fin n → ℤ)
  coeff : (Fin n → ℤ) → ℂ
  degree : ∀ k ∈ frequencies, ∀ i, (k i).natAbs ≤ d i

def BoxTrigPolynomial.toUniform {n : ℕ} {d : Fin n → ℕ} (H : BoxTrigPolynomial d) :
    TrigPolynomial n (∑ i, d i) where
  frequencies := H.frequencies
  coeff := H.coeff
  degree k hk i := (H.degree k hk i).trans
    (Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i))

def BoxTrigPolynomial.toContinuousMap {n : ℕ} {d : Fin n → ℕ} (H : BoxTrigPolynomial d) : C(TorusN n, ℂ) :=
  H.toUniform.toContinuousMap

def BoxTrigPolynomial.eval {n : ℕ} {d : Fin n → ℕ} (H : BoxTrigPolynomial d) : TorusN n → ℂ :=
  H.toUniform.eval

def BoxTrigPolynomial.partial {n : ℕ} {d : Fin n → ℕ} (H : BoxTrigPolynomial d) (i : Fin n) :
    BoxTrigPolynomial d where
  frequencies := H.frequencies
  coeff k := H.coeff k * ((k i : ℂ) * Complex.I)
  degree := H.degree

lemma partial_toUniform {n : ℕ} {d : Fin n → ℕ} (H : BoxTrigPolynomial d) (i : Fin n) :
    (H.partial i).toUniform = H.toUniform.partial i := rfl

lemma hasDerivAt_partial {n : ℕ} {d : Fin n → ℕ} (H : BoxTrigPolynomial d)
    (i : Fin n) (theta : Fin n → ℝ) :
    HasDerivAt (fun t : ℝ => H.eval (angularPoint (Function.update theta i t)))
      ((H.partial i).eval (angularPoint theta)) (theta i) :=
  TensorNorming.hasDerivAt_partial H.toUniform i theta

/-- The source polynomial with its actual separate coordinate-degree bounds. -/
structure BoxPolynomial {n : ℕ} (d : Fin n → ℕ) where
  val : MvPolynomial (Fin n) ℝ
  degree : ∀ s ∈ val.support, ∀ i, s i ≤ d i

def BoxPolynomial.toUniform {n : ℕ} {d : Fin n → ℕ} (q : BoxPolynomial d) :
    Paper34.PolynomialSpace n (∑ i, d i) :=
  ⟨q.val, (MvPolynomial.mem_restrictDegree (Fin n) q.val _).mpr
    (fun s hs i => (q.degree s hs i).trans
      (Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)))⟩

lemma cosinePolynomial_mem_box {n : ℕ} {d : Fin n → ℕ} (q : BoxPolynomial d) :
    CosineFourierLift.cosinePolynomial q.val ∈ CosineFourierLift.boxSpace d := by
  apply Submodule.sum_mem
  intro s hs
  apply Submodule.smul_mem
  exact CosineFourierLift.boxSpace_mono (q.degree s hs)
    (CosineFourierLift.product_cosine_powers_mem s)

lemma exists_box_representation {n : ℕ} {d : Fin n → ℕ} (F : C(TorusN n, ℂ))
    (hF : F ∈ CosineFourierLift.boxSpace d) :
    ∃ H : BoxTrigPolynomial d, H.toUniform.toContinuousMap = F := by
  obtain ⟨l, hl, he⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).mp hF
  let H : BoxTrigPolynomial d :=
    { frequencies := l.support
      coeff := l
      degree := fun k hk i => ((Finsupp.mem_supported ℂ l).mp hl hk) i }
  refine ⟨H, ?_⟩
  change (∑ k ∈ l.support, l k • monomial k) = F
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using he

def BoxPolynomial.fourierLift {n : ℕ} {d : Fin n → ℕ} (q : BoxPolynomial d) : BoxTrigPolynomial d :=
  Classical.choose (exists_box_representation _ (cosinePolynomial_mem_box q))

lemma fourierLift_spec {n : ℕ} {d : Fin n → ℕ} (q : BoxPolynomial d) :
    q.fourierLift.toUniform.toContinuousMap = CosineFourierLift.cosinePolynomial q.val :=
  Classical.choose_spec (exists_box_representation _ (cosinePolynomial_mem_box q))

lemma fourierLift_angular {n : ℕ} {d : Fin n → ℕ} (q : BoxPolynomial d) (theta : Fin n → ℝ) :
    q.fourierLift.eval (angularPoint theta) = (Paper34.angularEval q.toUniform theta : ℂ) := by
  have h := CosineFourierLift.toTrigPolynomial_angular q.toUniform theta
  change (CosineFourierLift.toTrigPolynomial q.toUniform).toContinuousMap (angularPoint theta) = _ at h
  rw [CosineFourierLift.toTrigPolynomial_spec] at h
  change q.fourierLift.toUniform.toContinuousMap (angularPoint theta) = _
  rw [fourierLift_spec]
  exact h

/-- The constant kernel convention `V₀ ≡ 1` from Appendix A.3. -/
def coordinateKernel (d : ℕ) : C(Torus, ℂ) := if d = 0 then 1 else valleePoussin d

def coordinateDerivativeKernel (d : ℕ) : C(Torus, ℂ) :=
  if d = 0 then 0 else valleePoussinDerivative d

lemma coordinateKernel_coeff (d : ℕ) (k : ℤ) (hk : k.natAbs ≤ d) :
    fourierCoeff (coordinateKernel d) k = 1 := by
  by_cases hd : d = 0
  · have hk0 : k = 0 := by omega
    subst k
    simp only [coordinateKernel, if_pos hd, fourierCoeff, neg_zero, fourier_zero, one_smul,
      ContinuousMap.one_apply, integral_const, measureReal_univ_eq_one, one_smul]
  · simpa only [coordinateKernel, if_neg hd] using valleePoussin_coeff d (by omega) k hk

lemma coordinateKernel_L1 (d : ℕ) :
    (∫ x : Torus, ‖coordinateKernel d x‖ ∂haar) ≤ 3 := by
  by_cases hd : d = 0
  · simp [coordinateKernel, hd, measureReal_univ_eq_one]
  · simpa only [coordinateKernel, if_neg hd] using valleePoussin_L1 d (by omega)

lemma coordinateDerivativeKernel_L1 (d : ℕ) :
    (∫ x : Torus, ‖coordinateDerivativeKernel d x‖ ∂haar) ≤ 10 * d := by
  by_cases hd : d = 0
  · simp [coordinateDerivativeKernel, hd]
  · simpa only [coordinateDerivativeKernel, if_neg hd] using valleePoussinDerivative_L1 d (by omega)

lemma coordinateKernel_hasDerivAt (d : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => coordinateKernel d (s : Torus))
      (coordinateDerivativeKernel d (t : Torus)) t := by
  by_cases hd : d = 0
  · simpa only [coordinateKernel, coordinateDerivativeKernel, if_pos hd,
      ContinuousMap.one_apply, ContinuousMap.zero_apply] using hasDerivAt_const t (1 : ℂ)
  · simpa only [coordinateKernel, coordinateDerivativeKernel, if_neg hd] using hasDerivAt_valleePoussin d t

lemma coordinateDerivativeKernel_coeff (d : ℕ) (k : ℤ) (hk : k.natAbs ≤ d) :
    fourierCoeff (coordinateDerivativeKernel d) k = (k : ℂ) * Complex.I := by
  rw [derivative_fourierCoeff _ _ (coordinateKernel_hasDerivAt d), coordinateKernel_coeff d k hk, mul_one]

abbrev GridIndex (n : ℕ) (m : Fin n → ℕ) := ∀ i, Fin (2 * m i)
abbrev PositiveIndex (n : ℕ) (m : Fin n → ℕ) := ∀ i, Fin (m i)

def gridWeight {n : ℕ} (m : Fin n → ℕ) : ℝ := ∏ i, TensorNorming.gridWeight (m i)

def gridCell {n : ℕ} {m : Fin n → ℕ} (j : GridIndex n m) : Set (Fin n → ℝ) :=
  Icc (fun i => (j i : ℕ) * (Real.pi / m i))
    (fun i => ((j i : ℕ) + 1 : ℝ) * (Real.pi / m i))

lemma gridCell_nonempty {n : ℕ} {m : Fin n → ℕ} (j : GridIndex n m) : (gridCell j).Nonempty := by
  refine ⟨fun i => (j i : ℕ) * (Real.pi / m i), le_rfl, ?_⟩
  intro i
  have : 0 ≤ Real.pi / (m i : ℝ) := by positivity
  dsimp
  nlinarith

def boxKernel {n : ℕ} (d : Fin n → ℕ) : C(TorusN n, ℂ) :=
  productKernel (fun i => coordinateKernel (d i))

lemma reproduce_box {n : ℕ} {d : Fin n → ℕ} (H : BoxTrigPolynomial d) (x : TorusN n) :
    (∫ u : TorusN n, H.eval u * boxKernel d (x - u) ∂haarN n) = H.eval x := by
  rw [boxKernel, show H.eval = H.toUniform.eval from rfl, convolution_eq_sum]
  simp only [BoxTrigPolynomial.toUniform, TrigPolynomial.eval, TrigPolynomial.toContinuousMap,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hprod : (∏ i : Fin n, fourierCoeff (coordinateKernel (d i)) (k i)) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    exact coordinateKernel_coeff (d i) (k i) (H.degree k hk i)
  rw [hprod, mul_one]

lemma coordinate_gridSup_le (d m : ℕ) (hm : max 1 d ≤ m) (u : Torus) :
    TensorNorming.gridWeight m * ∑ j ∈ Finset.range (2 * m),
      intervalSup (shiftLift (coordinateKernel d) u)
        (j * (Real.pi / m)) ((j + 1) * (Real.pi / m)) ≤ 3 + 10 * Real.pi := by
  by_cases hd : d = 0
  · have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hsup (j : ℕ) : intervalSup (shiftLift (coordinateKernel d) u)
        (j * (Real.pi / m)) ((j + 1) * (Real.pi / m)) = 1 := by
      have hab : (j : ℝ) * (Real.pi / m) ≤ (j + 1) * (Real.pi / m) := by
        have : 0 ≤ Real.pi / (m : ℝ) := by positivity
        nlinarith
      obtain ⟨t, ht, heq⟩ := intervalSup_attained
        (continuous_shiftLift (coordinateKernel d) u) hab
      simpa only [shiftLift, coordinateKernel, if_pos hd, ContinuousMap.one_apply, norm_one] using heq.symm
    simp_rw [hsup]
    have hone : TensorNorming.gridWeight m * ∑ _j ∈ Finset.range (2 * m), (1 : ℝ) = 1 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, TensorNorming.gridWeight]
      push_cast
      field_simp
    rw [hone]
    have := Real.pi_pos
    linarith
  · simpa only [coordinateKernel, if_neg hd, TensorNorming.gridWeight, kernelGridSup] using
      kernelGridSup_le d m (by omega) (by omega) u

/-- Tensorized shift-uniform kernel bound on coordinate-dependent grids. -/
theorem representative_kernel_sum {n : ℕ} {d m : Fin n → ℕ}
    (hm : ∀ i, max 1 (d i) ≤ m i)
    (r : GridIndex n m → Fin n → ℝ) (hr : ∀ j, r j ∈ gridCell j) (u : TorusN n) :
    gridWeight m * ∑ j : GridIndex n m, ‖boxKernel d (angularPoint (r j) - u)‖ ≤
      (3 + 10 * Real.pi) ^ n := by
  let A (i : Fin n) (a : Fin (2 * m i)) : ℝ :=
    intervalSup (shiftLift (coordinateKernel (d i)) (u i))
      ((a : ℕ) * (Real.pi / m i)) (((a : ℕ) + 1 : ℝ) * (Real.pi / m i))
  have hA0 (i : Fin n) (a : Fin (2 * m i)) : 0 ≤ A i a := by
    have hbound := norm_le_intervalSup (continuous_shiftLift (coordinateKernel (d i)) (u i))
      (show ((a : ℕ) : ℝ) * (Real.pi / m i) ∈
        Icc ((a : ℕ) * (Real.pi / m i)) (((a : ℕ) + 1 : ℝ) * (Real.pi / m i)) by
          constructor
          · exact le_rfl
          · have : 0 ≤ Real.pi / (m i : ℝ) := by positivity
            nlinarith)
    exact (norm_nonneg _).trans hbound
  have hcoord (i : Fin n) : TensorNorming.gridWeight (m i) * ∑ a : Fin (2 * m i), A i a ≤
      3 + 10 * Real.pi := by
    dsimp [A]
    rw [Fin.sum_univ_eq_sum_range (fun a : ℕ =>
      intervalSup (shiftLift (coordinateKernel (d i)) (u i))
        ((a : ℝ) * (Real.pi / m i)) (((a : ℝ) + 1) * (Real.pi / m i))) (2 * m i)]
    exact coordinate_gridSup_le (d i) (m i) (hm i) (u i)
  have hpoint (j : GridIndex n m) : ‖boxKernel d (angularPoint (r j) - u)‖ ≤ ∏ i, A i (j i) := by
    simp only [boxKernel, productKernel, ContinuousMap.coe_mk, norm_prod, Pi.sub_apply]
    apply Finset.prod_le_prod (fun i hi => norm_nonneg _)
    intro i hi
    exact norm_le_intervalSup (continuous_shiftLift (coordinateKernel (d i)) (u i))
      ⟨(hr j).1 i, (hr j).2 i⟩
  have hw (i : Fin n) : 0 ≤ TensorNorming.gridWeight (m i) := by
    unfold TensorNorming.gridWeight
    positivity
  calc
    _ ≤ gridWeight m * ∑ j : GridIndex n m, ∏ i, A i (j i) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hpoint j)
        (Finset.prod_nonneg fun i _ => hw i)
    _ = ∏ i : Fin n, (TensorNorming.gridWeight (m i) * ∑ a : Fin (2 * m i), A i a) := by
      rw [Finset.prod_mul_distrib, ← Fintype.prod_sum]
      rfl
    _ ≤ ∏ _i : Fin n, (3 + 10 * Real.pi) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact mul_nonneg (hw i) (Finset.sum_nonneg fun a _ => hA0 i a)
      · intro i hi
        exact hcoord i
    _ = _ := by simp

theorem representative_norming {n : ℕ} {d m : Fin n → ℕ} (H : BoxTrigPolynomial d)
    (hm : ∀ i, max 1 (d i) ≤ m i) (r : GridIndex n m → Fin n → ℝ)
    (hr : ∀ j, r j ∈ gridCell j) :
    gridWeight m * ∑ j : GridIndex n m, ‖H.eval (angularPoint (r j))‖ ≤
      (3 + 10 * Real.pi) ^ n * ∫ u : TorusN n, ‖H.eval u‖ ∂haarN n := by
  let F (j : GridIndex n m) (u : TorusN n) : ℝ :=
    ‖H.eval u‖ * ‖boxKernel d (angularPoint (r j) - u)‖
  have hF (j : GridIndex n m) : Continuous (F j) :=
    (continuous_eval H.toUniform).norm.mul ((boxKernel d).continuous.comp
      (continuous_const.sub continuous_id)).norm
  have hFi (j : GridIndex n m) : Integrable (F j) (haarN n) :=
    (hF j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpoint (j : GridIndex n m) : ‖H.eval (angularPoint (r j))‖ ≤
      ∫ u : TorusN n, F j u ∂haarN n := by
    rw [← reproduce_box H (angularPoint (r j))]
    simpa only [norm_mul] using norm_integral_le_integral_norm
      (fun u : TorusN n => H.eval u * boxKernel d (angularPoint (r j) - u))
  have hw : 0 ≤ gridWeight m := by
    apply Finset.prod_nonneg
    intro i hi
    unfold TensorNorming.gridWeight
    positivity
  calc
    _ ≤ gridWeight m * ∑ j : GridIndex n m, ∫ u, F j u ∂haarN n :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hpoint j) hw
    _ = ∫ u : TorusN n, gridWeight m * ∑ j : GridIndex n m, F j u ∂haarN n := by
      rw [integral_const_mul, integral_finset_sum _ (fun j _ => hFi j)]
    _ ≤ ∫ u : TorusN n, (3 + 10 * Real.pi) ^ n * ‖H.eval u‖ ∂haarN n := by
      apply integral_mono
      · exact ((continuous_const.mul (continuous_finset_sum _ fun j _ => hF j))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact (continuous_const.mul (continuous_eval H.toUniform).norm).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · intro u
        have hk := representative_kernel_sum hm r hr u
        have hk' := mul_le_mul_of_nonneg_left hk (norm_nonneg (H.eval u))
        simpa only [F, ← Finset.mul_sum] using (show
          gridWeight m * (‖H.eval u‖ * ∑ j : GridIndex n m,
            ‖boxKernel d (angularPoint (r j) - u)‖) ≤
          (3 + 10 * Real.pi) ^ n * ‖H.eval u‖ by nlinarith [hk'])
    _ = _ := integral_const_mul _ _

/-- Actual cell supremum on the closed real angular box. -/
def cellSup {n : ℕ} (f : C(TorusN n, ℂ)) {m : Fin n → ℕ} (j : GridIndex n m) : ℝ :=
  sSup ((fun theta => ‖f (angularPoint theta)‖) '' gridCell j)

lemma cellSup_attained {n : ℕ} {m : Fin n → ℕ} (f : C(TorusN n, ℂ)) (j : GridIndex n m) :
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
theorem local_supremum_bound {n : ℕ} {d m : Fin n → ℕ} (H : BoxTrigPolynomial d)
    (hm : ∀ i, max 1 (d i) ≤ m i) :
    gridWeight m * ∑ j : GridIndex n m, cellSup H.toContinuousMap j ≤
      (3 + 10 * Real.pi) ^ n * ∫ u : TorusN n, ‖H.eval u‖ ∂haarN n := by
  classical
  choose r hr heq using fun j : GridIndex n m => cellSup_attained H.toContinuousMap j
  have h := representative_norming H hm r hr
  have heq' (j : GridIndex n m) : ‖H.eval (angularPoint (r j))‖ = cellSup H.toContinuousMap j := heq j
  simpa only [heq'] using h

def derivativeKernel {n : ℕ} (d : Fin n → ℕ) (i : Fin n) : C(TorusN n, ℂ) :=
  productKernel (fun j => if j = i then coordinateDerivativeKernel (d i) else coordinateKernel (d j))

lemma reproduce_partial {n : ℕ} {d : Fin n → ℕ} (H : BoxTrigPolynomial d)
    (i : Fin n) (x : TorusN n) :
    (∫ u : TorusN n, H.eval u * derivativeKernel d i (x - u) ∂haarN n) =
      (H.partial i).eval x := by
  rw [derivativeKernel, show H.eval = H.toUniform.eval from rfl, convolution_eq_sum]
  simp only [BoxTrigPolynomial.eval, BoxTrigPolynomial.partial, BoxTrigPolynomial.toUniform,
    TrigPolynomial.eval, TrigPolynomial.toContinuousMap, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hcoeff (j : Fin n) :
      fourierCoeff ((if j = i then coordinateDerivativeKernel (d i) else coordinateKernel (d j)) : C(Torus, ℂ)) (k j) =
        if j = i then ((k i : ℂ) * Complex.I) else 1 := by
    split_ifs with hji
    · subst j
      exact coordinateDerivativeKernel_coeff (d i) (k i) (H.degree k hk i)
    · exact coordinateKernel_coeff (d j) (k j) (H.degree k hk j)
  simp_rw [hcoeff]
  rw [Finset.prod_ite_eq']
  simp only [Finset.mem_univ, if_true]
  ring

lemma derivativeKernel_L1 {n : ℕ} (d : Fin n → ℕ) (i : Fin n) :
    (∫ x : TorusN n, ‖derivativeKernel d i x‖ ∂haarN n) ≤
      (10 * d i : ℝ) * 3 ^ (n - 1) := by
  let g : Fin n → C(Torus, ℂ) := fun j =>
    if j = i then coordinateDerivativeKernel (d i) else coordinateKernel (d j)
  let A : Fin n → ℝ := fun j => ∫ x : Torus, ‖g j x‖ ∂haar
  have hprod : (∫ x : TorusN n, ‖derivativeKernel d i x‖ ∂haarN n) = ∏ j, A j := by
    simp only [derivativeKernel, productKernel, ContinuousMap.coe_mk, norm_prod]
    exact integral_fintype_prod_eq_prod (μ := fun _ => haar) (fun j x => ‖g j x‖)
  have hA (j : Fin n) : 0 ≤ A j := integral_nonneg fun _ => norm_nonneg _
  rw [hprod, ← Finset.mul_prod_erase _ A (Finset.mem_univ i)]
  have hAi : A i ≤ 10 * d i := by
    simpa only [A, g, if_pos rfl] using coordinateDerivativeKernel_L1 (d i)
  have hAj (j : Fin n) (hj : j ∈ Finset.univ.erase i) : A j ≤ 3 := by
    have hji := (Finset.mem_erase.mp hj).1
    simpa only [A, g, if_neg hji] using coordinateKernel_L1 (d j)
  calc
    A i * ∏ j ∈ Finset.univ.erase i, A j ≤
        (10 * d i : ℝ) * ∏ _j ∈ Finset.univ.erase i, (3 : ℝ) := by
      apply mul_le_mul hAi
      · exact Finset.prod_le_prod (fun j _ => hA j) hAj
      · exact Finset.prod_nonneg fun j _ => hA j
      · positivity
    _ = _ := by simp

/-- The anisotropic endpoint bound has exactly the coordinate factor `d i`,
including zero degrees, because the zero-degree derivative kernel is zero. -/
theorem partial_L1 {n : ℕ} {d : Fin n → ℕ} (H : BoxTrigPolynomial d) (i : Fin n) :
    (∫ x : TorusN n, ‖(H.partial i).eval x‖ ∂haarN n) ≤
      (10 * 3 ^ (n - 1) : ℝ) * d i * ∫ u : TorusN n, ‖H.eval u‖ ∂haarN n := by
  let F (x u : TorusN n) : ℝ := ‖H.eval u‖ * ‖derivativeKernel d i (x - u)‖
  have hF : Integrable (Function.uncurry F) ((haarN n).prod (haarN n)) :=
    (((continuous_eval H.toUniform).comp continuous_snd).norm.mul
      ((derivativeKernel d i).continuous.comp (continuous_fst.sub continuous_snd)).norm).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpoint (x : TorusN n) : ‖(H.partial i).eval x‖ ≤ ∫ u, F x u ∂haarN n := by
    rw [← reproduce_partial H i x]
    simpa only [norm_mul] using norm_integral_le_integral_norm
      (fun u : TorusN n => H.eval u * derivativeKernel d i (x - u))
  have h := integral_mono (integrable_continuousN (H.partial i).toUniform.toContinuousMap).norm
    hF.integral_prod_left hpoint
  have htrans (u : TorusN n) :
      (∫ x : TorusN n, ‖derivativeKernel d i (x - u)‖ ∂haarN n) =
        ∫ x : TorusN n, ‖derivativeKernel d i x‖ ∂haarN n :=
    integral_sub_right_eq_self (μ := haarN n) (fun x : TorusN n => ‖derivativeKernel d i x‖) u
  simp only [Function.uncurry] at h
  rw [integral_integral_swap hF] at h
  simp only [F] at h
  simp_rw [integral_const_mul, htrans] at h
  rw [integral_mul_const] at h
  calc
    _ ≤ (∫ u : TorusN n, ‖H.eval u‖ ∂haarN n) *
        (∫ x : TorusN n, ‖derivativeKernel d i x‖ ∂haarN n) := h
    _ ≤ (∫ u : TorusN n, ‖H.eval u‖ ∂haarN n) * ((10 * d i : ℝ) * 3 ^ (n - 1)) :=
      mul_le_mul_of_nonneg_left (derivativeKernel_L1 d i) (integral_nonneg fun _ => norm_nonneg _)
    _ = _ := by ring

lemma partial_eval_zero_of_degree_zero {n : ℕ} {d : Fin n → ℕ}
    (H : BoxTrigPolynomial d) (i : Fin n) (hdi : d i = 0) (x : TorusN n) :
    (H.partial i).eval x = 0 := by
  simp only [BoxTrigPolynomial.eval, BoxTrigPolynomial.partial, BoxTrigPolynomial.toUniform,
    TrigPolynomial.eval, TrigPolynomial.toContinuousMap, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro k hk
  have hki : k i = 0 := by have h := H.degree k hk i; omega
  simp only [hki, Int.cast_zero, zero_mul, mul_zero]

/-- The coordinate slice has its true coordinate Fourier degree, independently
of the degrees of every other coordinate. -/
lemma slice_mem_trigPolynomialSpace {n : ℕ} {d : Fin n → ℕ} (H : BoxTrigPolynomial d)
    (theta : Fin n → ℝ) (i : Fin n) :
    (fun t : ℝ => H.eval (angularPoint (Function.update theta i t))) ∈
      TrigBernstein.trigPolynomialSpace (d i) := by
  have heval : (fun t : ℝ => H.eval (angularPoint (Function.update theta i t))) =
      ∑ k ∈ H.frequencies, (H.coeff k * ∏ j ∈ Finset.univ.erase i,
        fourier (k j) (theta j : Torus)) • TrigBernstein.character (k i) := by
    funext t
    simp only [BoxTrigPolynomial.eval, BoxTrigPolynomial.toUniform, TrigPolynomial.eval,
      TrigPolynomial.toContinuousMap, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      smul_eq_mul, Finset.sum_apply, Pi.smul_apply, TrigBernstein.character, monomial_update]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [heval]
  apply Submodule.sum_mem
  intro k hk
  exact (TrigBernstein.trigPolynomialSpace (d i)).smul_mem _
    (TrigBernstein.character_mem (d i) (k i) (H.degree k hk i))

/-- Only the general classical trigonometric Bernstein theorem is an explicit
external input. The coordinate degree and the zero-degree case are internal. -/
theorem partial_norm_le_of_classicalBernstein (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {n : ℕ} {d : Fin n → ℕ} (H : BoxTrigPolynomial d) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ theta : Fin n → ℝ, ‖H.eval (angularPoint theta)‖ ≤ M)
    (i : Fin n) (theta : Fin n → ℝ) :
    ‖(H.partial i).eval (angularPoint theta)‖ ≤ (d i : ℝ) * M := by
  by_cases hdi : d i = 0
  · rw [partial_eval_zero_of_degree_zero H i hdi, norm_zero, hdi, Nat.cast_zero, zero_mul]
  · have h := hBernstein (d i) (by omega)
      (fun t : ℝ => H.eval (angularPoint (Function.update theta i t)))
      (slice_mem_trigPolynomialSpace H theta i) M hM
      (fun t => hbound (Function.update theta i t)) (theta i)
    rw [(hasDerivAt_partial H i theta).deriv] at h
    exact h

theorem hasDerivAt_partial_at {n : ℕ} {d : Fin n → ℕ} (H : BoxTrigPolynomial d)
    (theta : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => H.eval (angularPoint (Function.update theta i s)))
      ((H.partial i).eval (angularPoint (Function.update theta i t))) t := by
  simpa only [Function.update_self, Function.update_idem] using
    hasDerivAt_partial H i (Function.update theta i t)

/-- Sharp coordinate derivative bound for the actual source polynomial, with
its individual source degree and the standard Bernstein input. -/
theorem angularDerivative_bound (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {n : ℕ} {d : Fin n → ℕ} (q : BoxPolynomial d)
    (theta : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    |deriv (fun s : ℝ => Paper34.angularEval q.toUniform (Function.update theta i s)) t| ≤
      (d i : ℝ) * Paper34.supNorm q.toUniform := by
  have hcomplex := hasDerivAt_partial_at q.fourierLift theta i t
  have heq : (fun s : ℝ => q.fourierLift.eval (angularPoint (Function.update theta i s))) =
      (fun s : ℝ => (Paper34.angularEval q.toUniform (Function.update theta i s) : ℂ)) :=
    funext fun s => fourierLift_angular q (Function.update theta i s)
  rw [heq] at hcomplex
  have hreal := (Paper34.differentiable_angularSlice q.toUniform theta i t).hasDerivAt.ofReal_comp
  have heqder := hreal.unique hcomplex
  have hbound (eta : Fin n → ℝ) : ‖q.fourierLift.eval (angularPoint eta)‖ ≤ Paper34.supNorm q.toUniform := by
    rw [fourierLift_angular, Complex.norm_real, Real.norm_eq_abs]
    exact Paper34.angularEval_le_supNorm q.toUniform eta
  have hb := partial_norm_le_of_classicalBernstein hBernstein q.fourierLift
    (Paper34.supNorm q.toUniform) (Paper34.supNorm_nonneg q.toUniform) hbound
    i (Function.update theta i t)
  rw [← heqder, Complex.norm_real, Real.norm_eq_abs] at hb
  exact hb

end Paper34.Anisotropic
