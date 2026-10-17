import Paper26.FisherVolume
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Quantitative ingredients for the Fisher-volume inequality

The lemmas in this file retain separate coordinate marginals. No unproved
Sobolev or Loomis–Whitney inequality is assumed.
-/
noncomputable section
open scoped ENNReal NNReal
open MeasureTheory MeasureTheory.Measure Set Function Finset

namespace Paper26.SharpFisherVolume

section LoomisWhitney
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (μ : ι → Measure ℝ) [∀ i, SigmaFinite (μ i)]

/-- A function does not depend on coordinate `i`. -/
def IndependentOf (f : (ι → ℝ) → ℝ≥0∞) (i : ι) : Prop :=
  ∀ x t, f (update x i t) = f x

omit [Fintype ι] in
lemma IndependentOf.lmarginal {f : (ι → ℝ) → ℝ≥0∞} {i : ι}
    (hi : IndependentOf f i) (hf : Measurable f) (s : Finset ι) :
    IndependentOf (lmarginal μ s f) i := by
  intro x t
  by_cases his : i ∈ s
  · exact lmarginal_update_of_mem μ his f x t
  · rw [lmarginal_update_of_notMem hf his]
    congr 1
    funext y
    exact hi y t

/-- The product of the separate partial marginals after integrating coordinates
in `s`. Coordinate `j` is omitted from the integral of factor `j`. -/
def partialProduct (f : ι → (ι → ℝ) → ℝ≥0∞) (w : ι → ℝ)
    (s : Finset ι) (x : ι → ℝ) : ℝ≥0∞ :=
  ∏ j, (lmarginal μ (s.erase j) (f j) x) ^ w j

lemma measurable_partialProduct {f : ι → (ι → ℝ) → ℝ≥0∞}
    (hf : ∀ j, Measurable (f j)) (w : ι → ℝ) (s : Finset ι) :
    Measurable (partialProduct μ f w s) := by
  exact Finset.measurable_fun_prod _ fun j _ => ((hf j).lmarginal μ).pow_const _

/-- One coordinate of a generalized Loomis–Whitney integral is handled by
ordinary finite-family Hölder. -/
lemma partialProduct_integrate_le {f : ι → (ι → ℝ) → ℝ≥0∞}
    (hf : ∀ j, Measurable (f j)) (hi : ∀ j, IndependentOf (f j) j)
    (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hsum : ∀ i, ∑ j ∈ (univ.erase i), w j = 1)
    (s : Finset ι) (i : ι) (his : i ∉ s) (x : ι → ℝ) :
    (∫⁻ t, partialProduct μ f w s (update x i t) ∂μ i) ≤
      partialProduct μ f w (insert i s) x := by
  have hconst : ∀ t,
      lmarginal μ (s.erase i) (f i) (update x i t) = lmarginal μ s (f i) x := by
    intro t
    rw [Finset.erase_eq_of_notMem his]
    exact (hi i).lmarginal μ (hf i) s x t
  have hmeas : ∀ j, Measurable (fun t : ℝ =>
      lmarginal μ (s.erase j) (f j) (update x i t)) :=
    fun j => ((hf j).lmarginal μ).comp (measurable_update _)
  calc
    (∫⁻ t, partialProduct μ f w s (update x i t) ∂μ i) =
        (lmarginal μ s (f i) x) ^ w i *
          ∫⁻ t, ∏ j ∈ univ.erase i,
            (lmarginal μ (s.erase j) (f j) (update x i t)) ^ w j ∂μ i := by
      unfold partialProduct
      simp_rw [← Finset.mul_prod_erase univ _ (mem_univ i), hconst]
      rw [lintegral_const_mul]
      exact Finset.measurable_fun_prod _ (fun j _ => (hmeas j).pow_const _) 
    _ ≤ (lmarginal μ s (f i) x) ^ w i *
        ∏ j ∈ univ.erase i,
          (∫⁻ t, lmarginal μ (s.erase j) (f j) (update x i t) ∂μ i) ^ w j := by
      exact mul_le_mul_left'
        (ENNReal.lintegral_prod_norm_pow_le (univ.erase i)
          (fun j _ => (hmeas j).aemeasurable) (hsum i) (fun j _ => hw j)) _
    _ = partialProduct μ f w (insert i s) x := by
      unfold partialProduct
      rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
      congr 1
      · rw [Finset.erase_insert his]
      · apply Finset.prod_congr rfl
        intro j hj
        have hji : j ≠ i := (mem_erase.mp hj).1
        rw [Finset.erase_insert_of_ne hji.symm]
        congr 1
        exact (lmarginal_insert (f j) (hf j)
          (fun h => his (Finset.mem_of_mem_erase h)) x).symm

/-- Generalized Loomis–Whitney for separate coordinate-independent factors.
The right-hand marginal of factor `j` integrates every coordinate except `j`.
The weight equations are precisely the finite-family Hölder equations used at
each coordinate. -/
theorem lintegral_prod_le_prod_marginals
    {f : ι → (ι → ℝ) → ℝ≥0∞}
    (hf : ∀ j, Measurable (f j)) (hi : ∀ j, IndependentOf (f j) j)
    (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hsum : ∀ i, ∑ j ∈ (univ.erase i), w j = 1) (x : ι → ℝ) :
    (∫⁻ y, ∏ j, f j y ^ w j ∂Measure.pi μ) ≤
      ∏ j, (lmarginal μ (univ.erase j) (f j) x) ^ w j := by
  have hbound : ∀ s : Finset ι,
      lmarginal μ s (partialProduct μ f w ∅) ≤ partialProduct μ f w s := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert i s his ih =>
      intro y
      rw [lmarginal_insert _ (measurable_partialProduct μ hf w ∅) his]
      calc
        (∫⁻ t, lmarginal μ s (partialProduct μ f w ∅) (update y i t) ∂μ i)
            ≤ ∫⁻ t, partialProduct μ f w s (update y i t) ∂μ i :=
          lintegral_mono (fun t => ih (update y i t))
        _ ≤ partialProduct μ f w (insert i s) y :=
          partialProduct_integrate_le μ hf hi w hw hsum s i his y
  simpa [partialProduct] using hbound univ x

end LoomisWhitney

/-- Compact support gives a bound from each end of the real line. Adding the
two bounds retains the factor two that is essential for the sharp dimension
scale. -/
theorem two_enorm_le_lintegral_deriv {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (x : ℝ) :
    (2 : ℝ≥0∞) * ‖g x‖ₑ ≤ ∫⁻ t, ‖deriv g t‖ₑ := by
  have hl := HasCompactSupport.enorm_le_lintegral_Ici_deriv hg hc x
  have hr : ‖g x‖ₑ ≤ ∫⁻ t in Ioi x, ‖deriv g t‖ₑ := by
    have h := enorm_integral_le_lintegral_enorm (fun t => deriv g t)
      (μ := volume.restrict (Ioi x))
    simpa only [HasCompactSupport.integral_Ioi_deriv_eq hg hc x, enorm_neg] using h
  calc
    (2 : ℝ≥0∞) * ‖g x‖ₑ = ‖g x‖ₑ + ‖g x‖ₑ := two_mul _
    _ ≤ (∫⁻ t in Iic x, ‖deriv g t‖ₑ) + ∫⁻ t in Ioi x, ‖deriv g t‖ₑ :=
      add_le_add hl hr
    _ = ∫⁻ t, ‖deriv g t‖ₑ := by
      simpa only [compl_Iic] using
        (lintegral_add_compl (fun t => ‖deriv g t‖ₑ) measurableSet_Iic)

section Directional
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual derivative along the i-th coordinate line. -/
def coordinateDerivative (u : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) : ℝ :=
  fderiv ℝ u x (Pi.single i 1)

lemma continuous_coordinateDerivative {u : (ι → ℝ) → ℝ}
    (hu : ContDiff ℝ 1 u) (i : ι) : Continuous (coordinateDerivative u i) :=
  (hu.continuous_fderiv le_rfl).clm_apply continuous_const

lemma deriv_update_eq_coordinateDerivative {u : (ι → ℝ) → ℝ}
    (hu : ContDiff ℝ 1 u) (x : ι → ℝ) (i : ι) (t : ℝ) :
    deriv (u ∘ update x i) t = coordinateDerivative u i (update x i t) := by
  rw [fderiv_comp_deriv _ (hu.differentiable le_rfl).differentiableAt
    (hasDerivAt_update x i t).differentiableAt]
  simp only [coordinateDerivative, deriv_update]

lemma two_enorm_le_lineVariation {u : (ι → ℝ) → ℝ}
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) (x : ι → ℝ) (i : ι) :
    (2 : ℝ≥0∞) * ‖u x‖ₑ ≤
      lmarginal (fun _ : ι => volume) {i}
        (fun y => ‖coordinateDerivative u i y‖ₑ) x := by
  have h := two_enorm_le_lintegral_deriv
    (hu.comp (by convert contDiff_update 1 x i))
    (hc.comp_isClosedEmbedding (isClosedEmbedding_update x i)) (x i)
  simpa only [lmarginal_singleton, deriv_update_eq_coordinateDerivative hu,
    Function.comp_apply, Function.update_eq_self] using h

/-- Anisotropic Sobolev estimate before taking the final norm. Separate
coordinate derivative integrals are retained throughout the proof. -/
theorem lintegral_two_mul_enorm_pow_le_prod_directional
    {q : ℝ} (hq : Real.HolderConjugate (Fintype.card ι) q)
    {u : (ι → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    (∫⁻ x, ((2 : ℝ≥0∞) * ‖u x‖ₑ) ^ q) ≤
      ∏ i, (∫⁻ x, ‖coordinateDerivative u i x‖ₑ) ^
        (1 / (Fintype.card ι - 1 : ℝ)) := by
  let μ : ι → Measure ℝ := fun _ => volume
  let d : ι → (ι → ℝ) → ℝ≥0∞ := fun i x => ‖coordinateDerivative u i x‖ₑ
  let f : ι → (ι → ℝ) → ℝ≥0∞ := fun i => lmarginal μ {i} (d i)
  let p : ℝ := 1 / (Fintype.card ι - 1 : ℝ)
  have hd : ∀ i, Measurable (d i) := fun i =>
    (continuous_coordinateDerivative hu i).measurable.enorm
  have hf : ∀ i, Measurable (f i) := fun i => (hd i).lmarginal μ
  have hi : ∀ i, IndependentOf (f i) i := by
    intro i x t
    exact lmarginal_update_of_mem μ (mem_singleton_self i) (d i) x t
  have hp : 0 ≤ p := by dsimp [p]; exact div_nonneg zero_le_one (sub_nonneg.mpr hq.lt.le)
  have hw : ∀ i : ι, ∑ j ∈ univ.erase i, p = 1 := by
    intro i
    have hcard : 1 ≤ Fintype.card ι := by exact_mod_cast hq.lt.le
    simp only [sum_const, nsmul_eq_mul, card_erase_of_mem (mem_univ i), card_univ]
    rw [Nat.cast_sub hcard, Nat.cast_one]
    dsimp [p]
    exact mul_one_div_cancel (sub_pos.mpr hq.lt).ne'
  have hprod : ∀ x : ι → ℝ,
      ((2 : ℝ≥0∞) * ‖u x‖ₑ) ^ q =
        ∏ _i : ι, ((2 : ℝ≥0∞) * ‖u x‖ₑ) ^ p := by
    intro x
    rw [prod_const]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, card_univ]
    congr 1
    rw [hq.conjugate_eq]
    dsimp [p]
    ring
  calc
    (∫⁻ x, ((2 : ℝ≥0∞) * ‖u x‖ₑ) ^ q)
        = ∫⁻ x, ∏ _i : ι, ((2 : ℝ≥0∞) * ‖u x‖ₑ) ^ p := by
      exact lintegral_congr hprod
    _ ≤ ∫⁻ x, ∏ i, f i x ^ p := by
      apply lintegral_mono
      intro x
      apply Finset.prod_le_prod'
      intro i _
      exact ENNReal.rpow_le_rpow (two_enorm_le_lineVariation hu hc x i) hp
    _ ≤ ∏ i, (lmarginal μ (univ.erase i) (f i) (fun _ => 0)) ^ p := by
      exact lintegral_prod_le_prod_marginals μ hf hi (fun _ => p) (fun _ => hp) hw _
    _ = ∏ i, (∫⁻ x, ‖coordinateDerivative u i x‖ₑ) ^ p := by
      apply Finset.prod_congr rfl
      intro i _
      congr 1
      change lmarginal μ (univ.erase i) (lmarginal μ {i} (d i)) _ = _
      rw [← lmarginal_union μ (d i) (hd i)
        (Finset.disjoint_singleton_right.mpr (notMem_erase i univ)),
        Finset.union_singleton, insert_erase (mem_univ i), lmarginal_univ]
      rfl

/-- Taking the Sobolev root leaves the geometric mean of the separate L¹
coordinate derivative integrals. -/
theorem two_mul_eLpNorm_le_geom_directional
    {q : ℝ≥0} (hq : NNReal.HolderConjugate (Fintype.card ι) q)
    {u : (ι → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    (2 : ℝ≥0∞) * eLpNorm u q volume ≤
      ∏ i, (∫⁻ x, ‖coordinateDerivative u i x‖ₑ) ^ (1 / (Fintype.card ι : ℝ)) := by
  have hpos : 0 < (q : ℝ) := hq.coe.symm.pos
  apply (ENNReal.rpow_le_rpow_iff hpos).mp
  calc
    ((2 : ℝ≥0∞) * eLpNorm u q volume) ^ (q : ℝ) =
        ∫⁻ x, ((2 : ℝ≥0∞) * ‖u x‖ₑ) ^ (q : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hpos.le,
        eLpNorm_nnreal_pow_eq_lintegral hq.symm.pos.ne']
      rw [← lintegral_const_mul]
      · apply lintegral_congr
        intro x
        exact (ENNReal.mul_rpow_of_nonneg _ _ hpos.le).symm
      · exact (hu.continuous.measurable.enorm.pow_const _)
    _ ≤ ∏ i, (∫⁻ x, ‖coordinateDerivative u i x‖ₑ) ^
        (1 / (Fintype.card ι - 1 : ℝ)) :=
      lintegral_two_mul_enorm_pow_le_prod_directional hq.coe hu hc
    _ = (∏ i, (∫⁻ x, ‖coordinateDerivative u i x‖ₑ) ^
        (1 / (Fintype.card ι : ℝ))) ^ (q : ℝ) := by
      rw [← ENNReal.prod_rpow_of_nonneg hpos.le]
      apply Finset.prod_congr rfl
      intro i _
      rw [← ENNReal.rpow_mul]
      congr 1
      rw [hq.coe.conjugate_eq]
      simp only [NNReal.coe_natCast]
      have hdim : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hq.lt
      field_simp [(lt_trans zero_lt_one hdim).ne', (sub_pos.mpr hdim).ne']

omit [DecidableEq ι] in
/-- Finite-valued extended nonnegative AM–GM, in the exact form needed for the
coordinate integrals. -/
lemma geom_le_average (a : ι → ℝ≥0∞) (ha : ∀ i, a i ≠ ∞)
    (hn : 0 < Fintype.card ι) :
    (∏ i, a i ^ (1 / (Fintype.card ι : ℝ))) ≤
      ((Fintype.card ι : ℝ≥0)⁻¹ : ℝ≥0) * ∑ i, a i := by
  let b : ι → ℝ≥0 := fun i => (a i).toNNReal
  have hb : ∀ i, (b i : ℝ≥0∞) = a i := fun i => ENNReal.coe_toNNReal (ha i)
  have hn0 : (Fintype.card ι : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  have hnn := NNReal.geom_mean_le_arith_mean_weighted univ
    (fun _ : ι => (Fintype.card ι : ℝ≥0)⁻¹) b (by
      simp only [sum_const, card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ hn0)
  have hexp : ((Fintype.card ι : ℝ≥0)⁻¹ : ℝ) = 1 / (Fintype.card ι : ℝ) := by
    simp
  calc
    (∏ i, a i ^ (1 / (Fintype.card ι : ℝ))) =
        ((∏ i, b i ^ (((Fintype.card ι : ℝ≥0)⁻¹ : ℝ))) : ℝ≥0) := by
      rw [ENNReal.coe_finset_prod]
      apply Finset.prod_congr rfl
      intro i _
      have hpow := ENNReal.coe_rpow_of_nonneg (b i)
        (show 0 ≤ 1 / (Fintype.card ι : ℝ) by positivity)
      simpa only [hexp, hb] using hpow.symm
    _ ≤ ((∑ i, (Fintype.card ι : ℝ≥0)⁻¹ * b i) : ℝ≥0) :=
      ENNReal.coe_le_coe.mpr hnn
    _ = ((Fintype.card ι : ℝ≥0)⁻¹ : ℝ≥0) * ∑ i, a i := by
      simp only [ENNReal.coe_finset_sum, ENNReal.coe_mul, hb, Finset.mul_sum]

/-- The anisotropic L¹ Sobolev bound with its explicit `1/(2n)` constant. -/
theorem eLpNorm_le_average_directional
    {q : ℝ≥0} (hq : NNReal.HolderConjugate (Fintype.card ι) q)
    {u : (ι → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    eLpNorm u q volume ≤ (2 : ℝ≥0∞)⁻¹ *
      (((Fintype.card ι : ℝ≥0)⁻¹ : ℝ≥0) *
        ∑ i, ∫⁻ x, ‖coordinateDerivative u i x‖ₑ) := by
  have ha : ∀ i, (∫⁻ x, ‖coordinateDerivative u i x‖ₑ) ≠ ∞ := by
    intro i
    rw [← eLpNorm_one_eq_lintegral_enorm]
    exact ((continuous_coordinateDerivative hu i).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ (Pi.single i 1))).eLpNorm_lt_top.ne
  have hb := (two_mul_eLpNorm_le_geom_directional hq hu hc).trans
    (geom_le_average _ ha (by exact_mod_cast hq.coe.pos))
  have hm := mul_le_mul_left' hb (2 : ℝ≥0∞)⁻¹
  simpa only [ENNReal.inv_mul_cancel_left (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)] using hm

end Directional

section Euclidean
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Euclidean Cauchy–Schwarz on the directional coefficients of a real linear
functional, using the Riesz isometry to identify its gradient. -/
lemma sum_norm_apply_basis_le (L : EuclideanSpace ℝ ι →L[ℝ] ℝ) :
    (∑ i, ‖L (EuclideanSpace.basisFun ι ℝ i)‖) ≤
      Real.sqrt (Fintype.card ι) * ‖L‖ := by
  have hsq : (∑ i, ‖L (EuclideanSpace.basisFun ι ℝ i)‖ ^ 2) = ‖L‖ ^ 2 := by
    have hb := (EuclideanSpace.basisFun ι ℝ).sum_sq_norm_inner_left
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm L)
    simpa only [InnerProductSpace.toDual_symm_apply, LinearIsometryEquiv.norm_map] using hb
  have h := Finset.sum_mul_sq_le_sq_mul_sq univ
    (fun _ : ι => (1 : ℝ)) (fun i => ‖L (EuclideanSpace.basisFun ι ℝ i)‖)
  simp only [one_mul, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one, hsq] at h
  have hn := Real.sq_sqrt (show 0 ≤ (Fintype.card ι : ℝ) by positivity)
  have hs : 0 ≤ ∑ i, ‖L (EuclideanSpace.basisFun ι ℝ i)‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hr := Real.sqrt_nonneg (Fintype.card ι : ℝ)
  have hl := norm_nonneg L
  apply (sq_le_sq₀ hs (mul_nonneg hr hl)).mp
  rw [mul_pow, hn]
  exact h

/-- Quantitative L¹ Euclidean Sobolev inequality obtained from distinct
coordinate marginals, with the cube-comparison constant `1/(2 sqrt(n))`.
The factored coefficient avoids any convention about inverse zero. -/
theorem eLpNorm_le_euclidean_fderiv_one
    {q : ℝ≥0} (hq : NNReal.HolderConjugate (Fintype.card ι) q)
    {u : EuclideanSpace ℝ ι → ℝ} (hu : ContDiff ℝ 1 u)
    (hc : HasCompactSupport u) :
    eLpNorm u q volume ≤ (2 : ℝ≥0∞)⁻¹ *
      (((Fintype.card ι : ℝ≥0)⁻¹ : ℝ≥0) *
        ENNReal.ofReal (Real.sqrt (Fintype.card ι)) *
          eLpNorm (fderiv ℝ u) 1 volume) := by
  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) := PiLp.continuousLinearEquiv 2 ℝ _
  let v : (ι → ℝ) → ℝ := u ∘ e.symm
  have hv : ContDiff ℝ 1 v := hu.comp e.symm.contDiff
  have hvc : HasCompactSupport v := hc.comp_homeomorph e.symm.toHomeomorph
  have he : MeasurePreserving e.symm volume volume := PiLp.volume_preserving_toLp ι
  have hn : eLpNorm v q volume = eLpNorm u q volume :=
    eLpNorm_comp_measurePreserving hu.continuous.aestronglyMeasurable he
  have hd : ∀ i x, coordinateDerivative v i x =
      fderiv ℝ u (e.symm x) (EuclideanSpace.basisFun ι ℝ i) := by
    intro i x
    unfold coordinateDerivative v
    rw [fderiv_comp x (hu.differentiable le_rfl _ ) e.symm.differentiableAt,
      e.symm.fderiv]
    simp [e, EuclideanSpace.basisFun_apply]
  have hsum : (∑ i, ∫⁻ x, ‖coordinateDerivative v i x‖ₑ) ≤
      ENNReal.ofReal (Real.sqrt (Fintype.card ι)) * eLpNorm (fderiv ℝ u) 1 volume := by
    rw [← lintegral_finset_sum _ (fun i _ =>
      (continuous_coordinateDerivative hv i).measurable.enorm)]
    calc
      (∫⁻ x, ∑ i, ‖coordinateDerivative v i x‖ₑ)
          ≤ ∫⁻ x, ENNReal.ofReal (Real.sqrt (Fintype.card ι)) *
              ‖fderiv ℝ u (e.symm x)‖ₑ := by
        apply lintegral_mono
        intro x
        have heq := ENNReal.ofReal_le_ofReal
          (sum_norm_apply_basis_le (fderiv ℝ u (e.symm x)))
        simpa only [hd, ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _),
          ENNReal.ofReal_mul (Real.sqrt_nonneg _), ofReal_norm] using heq
      _ = ENNReal.ofReal (Real.sqrt (Fintype.card ι)) * eLpNorm (fderiv ℝ u) 1 volume := by
        rw [lintegral_const_mul]
        · rw [eLpNorm_one_eq_lintegral_enorm]
          congr 1
          exact he.lintegral_comp (hu.continuous_fderiv le_rfl).measurable.enorm
        · exact ((hu.continuous_fderiv le_rfl).comp e.symm.continuous).measurable.enorm
  rw [← hn]
  exact (eLpNorm_le_average_directional hq hv hvc).trans (by
    simpa only [mul_assoc] using
      mul_le_mul_left' (mul_le_mul_left' hsum
        (((Fintype.card ι : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞)) (2 : ℝ≥0∞)⁻¹)

end Euclidean

end Paper26.SharpFisherVolume
