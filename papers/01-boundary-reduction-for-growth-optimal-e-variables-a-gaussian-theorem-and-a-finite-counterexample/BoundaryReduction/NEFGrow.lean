import BoundaryReduction.FiniteMixtureEntropy
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Analysis.InnerProductSpace.PiL2

open Real Set MeasureTheory InformationTheory ProbabilityTheory
open scoped Classical ENNReal NNReal
namespace BoundaryReduction.NEF

variable {α ι : Type*} [MeasurableSpace α] {d : ℕ}
variable (P₀ : Measure α) [IsProbabilityMeasure P₀]
variable (Y : α → EuclideanSpace ℝ (Fin d)) (hY : Measurable Y)
variable (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : IsOpen Θ)
variable (hexp : ∀ θ ∈ Θ, Integrable (fun x => exp (inner ℝ θ (Y x))) P₀)

noncomputable def law (θ : EuclideanSpace ℝ (Fin d)) : Measure α :=
  P₀.tilted (fun x => inner ℝ θ (Y x))

noncomputable def density (θ : EuclideanSpace ℝ (Fin d)) (x : α) : ℝ :=
  exp (inner ℝ θ (Y x))/(∫ z, exp (inner ℝ θ (Y z)) ∂P₀)

include hY hΘ hexp

lemma projection_interior {θ : EuclideanSpace ℝ (Fin d)} (hθ : θ ∈ Θ) :
    (1:ℝ) ∈ interior (integrableExpSet (fun x => inner ℝ θ (Y x)) P₀) := by
  have hopen : IsOpen ((fun t : ℝ => t • θ) ⁻¹' Θ) :=
    hΘ.preimage (continuous_id.smul continuous_const)
  have hmem : (1:ℝ) ∈ (fun t : ℝ => t • θ) ⁻¹' Θ := by simpa using hθ
  apply (interior_mono (s := (fun t : ℝ => t • θ) ⁻¹' Θ) ?_)
    (by rwa [hopen.interior_eq])
  intro t ht
  change Integrable (fun x => exp (t*inner ℝ θ (Y x))) P₀
  simpa only [real_inner_smul_left] using hexp (t • θ) ht

lemma law_probability {θ : EuclideanSpace ℝ (Fin d)} (hθ : θ ∈ Θ) :
    IsProbabilityMeasure (law P₀ Y θ) := isProbabilityMeasure_tilted (hexp θ hθ)

/-- Regularity supplies finite KL for every genuine NEF member. -/
theorem law_kl_ne_top {θ : EuclideanSpace ℝ (Fin d)} (hθ : θ ∈ Θ) :
    klDiv (law P₀ Y θ) P₀ ≠ ∞ := by
  let X : α → ℝ := fun x => inner ℝ θ (Y x)
  have hX : Measurable X := (innerSL ℝ θ).continuous.measurable.comp hY
  have he : Integrable (fun x => exp (X x)) P₀ := hexp θ hθ
  letI : IsProbabilityMeasure (law P₀ Y θ) := law_probability P₀ Y hY Θ hΘ hexp hθ
  have hi : Integrable X (law P₀ Y θ) := by
    apply (integrable_tilted_iff he X).mpr
    have hh := integrable_pow_mul_exp_of_mem_interior_integrableExpSet
      (projection_interior P₀ Y hY Θ hΘ hexp hθ) 1
    simpa only [pow_one,one_mul,smul_eq_mul,mul_comm] using hh
  have hac : law P₀ Y θ ≪ P₀ := tilted_absolutelyContinuous _ _
  have hllr := llr_tilted_left (Measure.AbsolutelyContinuous.rfl : P₀ ≪ P₀) he hX.aemeasurable
  have hz := llr_self P₀
  have hae : llr (law P₀ Y θ) P₀ =ᵐ[law P₀ Y θ]
      fun x => X x-log (∫ z, exp (X z) ∂P₀) := by
    apply hac.ae_le
    filter_upwards [hllr,hz] with x hx hx0
    simpa only [hx0,Pi.zero_apply,add_zero] using hx
  exact klDiv_ne_top_iff.mpr ⟨hac,(hi.sub (integrable_const _)).congr (Filter.EventuallyEq.symm hae)⟩

/-- Lemma 2.1 for every subfamily of a regular NEF, under any indexing
(in particular mean parametrization). Minimality is unnecessary for this bound. -/
theorem lemma_2_1 (parameter : ι → EuclideanSpace ℝ (Fin d))
    (hparameter : ∀ i, parameter i ∈ Θ) :
    MeasureGrow.growth P₀ (fun i => law P₀ Y (parameter i)) ≤
      (↑(MeasureGrow.information P₀ (fun i => law P₀ Y (parameter i))) : EReal) := by
  letI (i : ι) : IsProbabilityMeasure (law P₀ Y (parameter i)) :=
    law_probability P₀ Y hY Θ hΘ hexp (hparameter i)
  have hkl (i : ι) := law_kl_ne_top P₀ Y hY Θ hΘ hexp (hparameter i)
  apply MeasureGrow.growth_le_information hkl
  intro F
  apply MeasureGrow.finiteMixture_kl_ne_top_of_densities F (fun i => density P₀ Y (parameter i))
  · intro i
    exact (((innerSL ℝ (parameter i)).continuous.measurable).comp hY).exp.div_const _
  · intro i x
    exact div_nonneg (exp_pos _).le (integral_nonneg (fun _ => (exp_pos _).le))
  · intro i
    rfl
  · exact hkl

/-- The integrability assertion following (2.4), with no positivity assumption on S. -/
theorem evar_positive_log_integrable (parameter : ι → EuclideanSpace ℝ (Fin d))
    (hparameter : ∀ i, parameter i ∈ Θ) (S : MeasureEVar P₀) (i : ι) :
    Integrable (fun x => max (log (S.value x)) 0) (law P₀ Y (parameter i)) := by
  letI : IsProbabilityMeasure (law P₀ Y (parameter i)) :=
    law_probability P₀ Y hY Θ hΘ hexp (hparameter i)
  exact MeasureGrow.integrable_posLog S.measurable S.nonneg S.integrable
    (law_kl_ne_top P₀ Y hY Θ hΘ hexp (hparameter i))

end BoundaryReduction.NEF
