import Paper34.HaarChebyshev
import Paper34.ChebyshevDensity
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The actual product-Chebyshev density in source (1.1)

Finite-product Tonelli is proved from the library's two-factor theorem and the
standard measurable splitting of `Fin (n+1)`. It converts the proved one-variable
cosine pushforward density into the exact density of `Model.chebyshevLaw n`.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Paper34.ProductChebyshevDensity

noncomputable section

lemma measurable_density : Measurable ChebyshevDensity.density := by
  unfold ChebyshevDensity.density
  apply Measurable.indicator _ measurableSet_Icc
  apply Measurable.ennreal_ofReal
  exact measurable_const.div (measurable_const.mul
    (Real.continuous_sqrt.measurable.comp (measurable_const.sub (measurable_id.pow_const 2))))

/-- Finite-product Tonelli, with all coordinate integrands measurable. -/
lemma lintegral_fin_prod {n : ℕ} (mu : Fin n → Measure ℝ) [∀ i, SigmaFinite (mu i)]
    (f : Fin n → ℝ → ENNReal) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : Point n, ∏ i, f i (x i) ∂Measure.pi mu) =
      ∏ i, ∫⁻ t, f i t ∂mu i := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ∫⁻ x : ℝ × Point n, f 0 x.1 * ∏ i : Fin n, f i.succ (x.2 i)
          ∂(mu 0).prod (Measure.pi (fun i => mu i.succ)) := by
        rw [← ((measurePreserving_piFinSuccAbove mu 0).symm).lintegral_comp_emb
          (MeasurableEquiv.measurableEmbedding _)]
        simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
          Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      _ = (∫⁻ t, f 0 t ∂mu 0) * ∏ i : Fin n, ∫⁻ t, f i.succ t ∂mu i.succ := by
        have hg : Measurable (fun y : Point n => ∏ i, f i.succ (y i)) :=
          Finset.measurable_prod _ (fun i _ => (hf i.succ).comp (measurable_pi_apply i))
        rw [lintegral_prod_mul (hf 0).aemeasurable hg.aemeasurable]
        rw [ih (fun i => mu i.succ) (fun i => f i.succ) (fun i => hf i.succ)]
      _ = _ := by rw [Fin.prod_univ_succ]

instance density_isProbabilityMeasure :
    IsProbabilityMeasure ((volume : Measure ℝ).withDensity ChebyshevDensity.density) := by
  rw [← ChebyshevDensity.realAngularLaw_map_cos]
  letI : IsProbabilityMeasure ChebyshevDensity.realAngularLaw := by
    change IsProbabilityMeasure HaarChebyshev.positiveAngularLaw
    infer_instance
  exact Measure.isProbabilityMeasure_map Real.continuous_cos.measurable.aemeasurable

/-- The product of the actual coordinate densities, including their support. -/
def productDensity (n : ℕ) (x : Point n) : ENNReal :=
  ∏ k, ChebyshevDensity.density (x k)

lemma measurable_productDensity (n : ℕ) : Measurable (productDensity n) :=
  Finset.measurable_prod _ (fun i _ => measurable_density.comp (measurable_pi_apply i))

/-- Product of density measures equals density of the product Lebesgue measure. -/
lemma pi_withDensity (n : ℕ) :
    Measure.pi (fun _ : Fin n => (volume : Measure ℝ).withDensity ChebyshevDensity.density) =
      (volume : Measure (Point n)).withDensity (productDensity n) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  change (∫⁻ x, ∏ i, ChebyshevDensity.density (x i)
      ∂(volume.restrict (Set.pi Set.univ s))) = _
  rw [volume_pi, Measure.restrict_pi_pi]
  rw [lintegral_fin_prod _ _ (fun _ => measurable_density)]
  simp_rw [withDensity_apply _ (hs _)]

/-- The actual `Model` law has the complete product density of source (1.1). -/
theorem chebyshevLaw_eq_withDensity (n : ℕ) :
    chebyshevLaw n = (volume : Measure (Point n)).withDensity (productDensity n) := by
  rw [chebyshevLaw, HaarChebyshev.angularLaw_eq_pi,
    Measure.pi_map_pi (fun _ => Real.continuous_cos.measurable.aemeasurable)]
  have h : Measure.map Real.cos HaarChebyshev.positiveAngularLaw =
      volume.withDensity ChebyshevDensity.density := ChebyshevDensity.realAngularLaw_map_cos
  simp_rw [h]
  exact pi_withDensity n

/-- Pointwise form matching the source's displayed product of real densities. -/
lemma productDensity_eq_cube_indicator (n : ℕ) :
    productDensity n = (cube n).indicator (fun x : Point n =>
      ENNReal.ofReal (∏ k, 1 / (Real.pi * Real.sqrt (1 - x k ^ 2)))) := by
  classical
  funext x
  by_cases hx : x ∈ cube n
  · rw [Set.indicator_of_mem hx]
    unfold productDensity
    rw [ENNReal.ofReal_prod_of_nonneg (fun k _ => by positivity)]
    apply Finset.prod_congr rfl
    intro k _
    exact Set.indicator_of_mem (show x k ∈ Icc (-1 : ℝ) 1 from ⟨hx.1 k, hx.2 k⟩) _
  · rw [Set.indicator_of_notMem hx]
    have hnot : ¬ ∀ k : Fin n, x k ∈ Icc (-1 : ℝ) 1 := by
      intro h
      exact hx ⟨fun k => (h k).1, fun k => (h k).2⟩
    obtain ⟨k, hk⟩ := not_forall.mp hnot
    unfold productDensity
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    exact Set.indicator_of_notMem hk _

/-- Equation (1.1), for the actual product law and actual ambient Lebesgue measure. -/
theorem source_density_1_1 (n : ℕ) :
    chebyshevLaw n = (volume : Measure (Point n)).withDensity
      ((cube n).indicator (fun x : Point n =>
        ENNReal.ofReal (∏ k, 1 / (Real.pi * Real.sqrt (1 - x k ^ 2))))) := by
  rw [chebyshevLaw_eq_withDensity, productDensity_eq_cube_indicator]

end

end Paper34.ProductChebyshevDensity
