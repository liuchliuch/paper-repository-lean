import BoundaryReduction.GaussianBoundary
import BoundaryReduction.FiniteKL

open Real Set MeasureTheory ProbabilityTheory InformationTheory BigOperators
open scoped Classical NNReal ENNReal
namespace BoundaryReduction.Gaussian

variable {d : ℕ}

/-- A finite convex combination of actual Gaussian location components in C. -/
structure FinitePrior (C : Set (Space d)) where
  index : Type
  finite : Fintype index
  weights : @BoundaryReduction.FinProb index finite
  mean : index → Space d
  admissible : ∀ i, mean i ∈ C

attribute [instance] FinitePrior.finite

namespace FinitePrior
variable {C : Set (Space d)}

noncomputable def componentExponent (K : Space d →L[ℝ] Space d) (V : FinitePrior C) (i : V.index) (x : Space d) :=
  inner ℝ (V.mean i) (K x)-inner ℝ (V.mean i) (K (V.mean i))/2

noncomputable def finiteLikelihood (K : Space d →L[ℝ] Space d) (V : FinitePrior C) (x : Space d) : ℝ :=
  ∑ i, V.weights.w i*exp (V.componentExponent K i x)

noncomputable def finiteMixture (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) (V : FinitePrior C) : Measure (Space d) :=
  Z.withDensity (fun x => ENNReal.ofReal (V.finiteLikelihood K x))

noncomputable def asPrior {Γ : Set (Space d)} (V : FinitePrior C) (hΓ : ∀ i, V.mean i ∈ Γ) : ProbabilityMeasure Γ :=
  ⟨∑ i, ENNReal.ofReal (V.weights.w i) • Measure.dirac ⟨V.mean i,hΓ i⟩, by
    constructor
    simp only [Measure.finset_sum_apply, MeasurableSet.univ, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => V.weights.nonneg i), V.weights.sum_eq_one]
    norm_num⟩

lemma integral_asPrior {Γ : Set (Space d)} [CompactSpace Γ]
    (V : FinitePrior C) (hΓ : ∀ i, V.mean i ∈ Γ) (g : Γ → ℝ) (hg : Continuous g) :
    (∫ r, g r ∂(V.asPrior hΓ : Measure Γ)) =
      ∑ i, V.weights.w i*g ⟨V.mean i,hΓ i⟩ := by
  unfold asPrior
  simp only [ProbabilityMeasure.coe_mk]
  rw [integral_finset_sum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_measure, ENNReal.toReal_ofReal (V.weights.nonneg i), integral_dirac]
    rfl
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma likelihood_asPrior {Γ : Set (Space d)} [CompactSpace Γ]
    (K : Space d →L[ℝ] Space d) (V : FinitePrior C) (hΓ : ∀ i, V.mean i ∈ Γ) (x : Space d) :
    likelihood K (V.asPrior hΓ : Measure Γ) x = V.finiteLikelihood K x := by
  rw [likelihood, integral_asPrior V hΓ (fun r : Γ => exp (exponent K r x))
    (Real.continuous_exp.comp (continuous_exponent K x))]
  rfl

lemma mixture_asPrior {Γ : Set (Space d)} [CompactSpace Γ]
    (K : Space d →L[ℝ] Space d) (Z : Measure (Space d))
    (V : FinitePrior C) (hΓ : ∀ i, V.mean i ∈ Γ) :
    mixtureMeasure K Z (V.asPrior hΓ) = V.finiteMixture K Z := by
  unfold mixtureMeasure finiteMixture
  congr 1
  ext x
  rw [likelihood_asPrior]

noncomputable def weaken {D : Set (Space d)} (V : FinitePrior C) (hCD : C ⊆ D) : FinitePrior D :=
  ⟨V.index, V.finite, V.weights, V.mean, fun i => hCD (V.admissible i)⟩

end FinitePrior

noncomputable def finiteInformation (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) (C : Set (Space d)) : ℝ≥0∞ :=
  sInf {x : ℝ≥0∞ | ∃ V : FinitePrior C, x = klDiv (V.finiteMixture K Z) Z}

variable {Γ : Set (Space d)} [CompactSpace Γ]

/-- Every Borel prior with finite support has a genuine finite-weight representation. -/
theorem exists_finite_representation (K : Space d →L[ℝ] Space d)
    (W : ProbabilityMeasure Γ) (hfin : (W : Measure Γ).support.Finite) :
    ∃ V : FinitePrior Γ, ∀ x : Space d, V.finiteLikelihood K x = likelihood K (W : Measure Γ) x := by
  let S := (W : Measure Γ).support
  letI : Fintype S := hfin.fintype
  have hS : MeasurableSet S := Measure.isClosed_support.measurableSet
  let P : Measure S := (W : Measure Γ).comap Subtype.val
  letI : IsProbabilityMeasure P := (MeasurableEmbedding.subtype_coe hS).isProbabilityMeasure_comap
    (by simpa only [Subtype.range_coe] using (Measure.support_mem_ae (μ := (W : Measure Γ))))
  have hp : P.map Subtype.val = (W : Measure Γ) := by
    change ((W : Measure Γ).comap Subtype.val).map Subtype.val = (W : Measure Γ)
    rw [map_comap_subtype_coe hS]
    exact Measure.restrict_eq_self_of_ae_mem Measure.support_mem_ae
  let weights : BoundaryReduction.FinProb S :=
    ⟨fun r => P.real {r}, fun _ => ENNReal.toReal_nonneg, by
      have h := integral_fintype (μ := P) (fun _ : S => (1:ℝ)) (integrable_const 1)
      simpa using h.symm⟩
  let V : FinitePrior Γ := ⟨S, inferInstance, weights, fun r => (r.1 : Space d), fun r => r.1.2⟩
  refine ⟨V, ?_⟩
  intro x
  have hi : Integrable (fun r : S => exp (exponent K r.1 x)) P := by
    have hc : Continuous (fun r : S => exp (exponent K r.1 x)) :=
      (Real.continuous_exp.comp (continuous_exponent K x)).comp continuous_subtype_val
    simpa using hc.continuousOn.integrableOn_compact (μ := P) isCompact_univ
  have h := integral_fintype (μ := P) (fun r : S => exp (exponent K r.1 x)) hi
  have hmap : (∫ r : S, exp (exponent K r.1 x) ∂P) = likelihood K (W : Measure Γ) x := by
    rw [← hp]
    exact (integral_map (by fun_prop) (Real.continuous_exp.comp (continuous_exponent K x)).aestronglyMeasurable).symm
  rw [h] at hmap
  exact hmap

end BoundaryReduction.Gaussian
