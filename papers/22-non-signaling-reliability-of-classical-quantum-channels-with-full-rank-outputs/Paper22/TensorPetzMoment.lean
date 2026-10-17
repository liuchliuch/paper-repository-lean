import Paper22.TensorPetz

/-! Multiplicativity of the actual Petz power-mixture moment on product
input distributions and tensor channels. -/
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator Kronecker
open Matrix
noncomputable section
namespace Paper22
variable {n d m e : ℕ}

def productWeights (q : Fin n → ℝ) (r : Fin m → ℝ) (a : Fin (n*m)) : ℝ :=
  q (finProdFinEquiv.symm a).1*r (finProdFinEquiv.symm a).2

@[simp] theorem productWeights_prod (q : Fin n → ℝ) (r : Fin m → ℝ)
    (x : Fin n) (y : Fin m) : productWeights q r (finProdFinEquiv (x,y))=q x*r y := by
  simp [productWeights]

theorem sum_product_indices {G : Type*} [AddCommMonoid G] (f : Fin (n*m) → G) :
    (∑ a, f a) = ∑ x : Fin n, ∑ y : Fin m, f (finProdFinEquiv (x,y)) := by
  rw [← finProdFinEquiv.sum_comp f]
  exact Fintype.sum_prod_type _

theorem productWeights_probability {q : Fin n → ℝ} {r : Fin m → ℝ}
    (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x=1)
    (hr0 : ∀ y, 0 ≤ r y) (hr1 : ∑ y, r y=1) :
    (∀ a, 0 ≤ productWeights q r a) ∧ ∑ a, productWeights q r a=1 := by
  constructor
  · intro a
    exact mul_nonneg (hq0 _) (hr0 _)
  · rw [sum_product_indices]
    simp only [productWeights_prod,← Finset.mul_sum,hr1,mul_one,hq1]

/-- Fractional powers of the actual channel outputs respect its tensor reindexing. -/
theorem tensor_channel_rpow (V : CQChannel n d) (W : CQChannel m e)
    (x : Fin n) (y : Fin m) {α : ℝ} (hα : 0 ≤ α) :
    CFC.rpow ((V.tensor W).states (finProdFinEquiv (x,y))) α =
      (CFC.rpow (V.states x) α ⊗ₖ CFC.rpow (W.states y) α).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm := by
  simp only [CQChannel.tensor,Equiv.symm_apply_apply]
  rw [matrix_rpow_reindex finProdFinEquiv
    (posSemidef_kronecker (V.isDensity x).posSemidef (W.isDensity y).posSemidef).nonneg hα,
    matrix_rpow_kronecker (V.isDensity x).nonneg (W.isDensity y).nonneg hα]

/-- Product-distribution power mixtures are actual Kronecker products. -/
theorem petzPowerMixture_tensor (V : CQChannel n d) (W : CQChannel m e)
    (q : Fin n → ℝ) (r : Fin m → ℝ) {α : ℝ} (hα : 0 ≤ α) :
    petzPowerMixture (V.tensor W) (productWeights q r) α =
      (petzPowerMixture V q α ⊗ₖ petzPowerMixture W r α).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm := by
  unfold petzPowerMixture
  rw [sum_product_indices]
  simp_rw [productWeights_prod,tensor_channel_rpow V W _ _ hα]
  ext i j
  simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.submatrix_apply,Matrix.kroneckerMap_apply,
    Pi.smul_apply,Finset.sum_mul,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp only [Algebra.smul_def,Complex.coe_algebraMap,Complex.ofReal_mul]
  ring

/-- The positive power trace is multiplicative on product input distributions. -/
theorem petzPowerMoment_tensor (V : CQChannel n d) (W : CQChannel m e)
    {q : Fin n → ℝ} {r : Fin m → ℝ} (hq : ∀ x, 0 ≤ q x) (hr : ∀ y, 0 ≤ r y)
    {α : ℝ} (hα : 0 < α) :
    (CFC.rpow (petzPowerMixture (V.tensor W) (productWeights q r) α) (1/α)).trace.re =
      (CFC.rpow (petzPowerMixture V q α) (1/α)).trace.re *
      (CFC.rpow (petzPowerMixture W r α) (1/α)).trace.re := by
  rw [petzPowerMixture_tensor V W _ _ hα.le,
    matrix_rpow_reindex finProdFinEquiv
      (posSemidef_kronecker (petzPowerMixture_nonneg V hq α).posSemidef
        (petzPowerMixture_nonneg W hr α).posSemidef).nonneg (one_div_nonneg.mpr hα.le),
    trace_submatrix_equiv,matrix_rpow_kronecker (petzPowerMixture_nonneg V hq α)
      (petzPowerMixture_nonneg W hr α) (one_div_nonneg.mpr hα.le),Matrix.trace_kronecker]
  have hA : 0 ≤ CFC.rpow (petzPowerMixture V q α) (1/α) := CFC.rpow_nonneg
  have hB : 0 ≤ CFC.rpow (petzPowerMixture W r α) (1/α) := CFC.rpow_nonneg
  rw [Complex.mul_re,hA.posSemidef.trace_nonneg.2.symm,hB.posSemidef.trace_nonneg.2.symm]
  simp only [Complex.zero_im,mul_zero,sub_zero]

end Paper22
end
