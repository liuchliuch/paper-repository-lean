import BoundaryReduction.MeasureInformation
import Mathlib.Analysis.Convex.Jensen

open Real Set MeasureTheory InformationTheory BigOperators
open scoped Classical ENNReal NNReal
namespace BoundaryReduction.MeasureGrow

variable {α ι : Type*} [MeasurableSpace α]
variable {P₀ : Measure α} [IsProbabilityMeasure P₀]

lemma integrable_klFun_density {Q : Measure α} [IsProbabilityMeasure Q] {g : α → ℝ}
    (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hQ : Q = P₀.withDensity (fun x => ENNReal.ofReal (g x))) (hKL : klDiv Q P₀ ≠ ∞) :
    Integrable (fun x => klFun (g x)) P₀ := by
  have hac := (klDiv_ne_top_iff.mp hKL).1
  have hi := (integrable_klFun_rnDeriv_iff hac).mpr (klDiv_ne_top_iff.mp hKL).2
  have hrn := Measure.rnDeriv_withDensity P₀ hg.ennreal_ofReal
  apply hi.congr
  filter_upwards [hrn] with x hx
  rw [hQ,hx,ENNReal.toReal_ofReal (hg0 x)]

lemma finiteMixture_density {P : ι → Measure α} (F : FiniteMixture P)
    (g : ι → α → ℝ) (hg : ∀ i, Measurable (g i)) (hg0 : ∀ i x, 0 ≤ g i x)
    (hP : ∀ i, P i = P₀.withDensity (fun x => ENNReal.ofReal (g i x))) :
    F.measure = P₀.withDensity (fun x => ENNReal.ofReal (∑ i, F.weights.w i*g (F.parameter i) x)) := by
  ext s hs
  rw [FiniteMixture.measure,Measure.finset_sum_apply,withDensity_apply _ hs]
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (F.weights.nonneg i) (hg0 _ _))]
  rw [lintegral_finset_sum Finset.univ (fun i _ => (measurable_const.mul (hg (F.parameter i))).ennreal_ofReal)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.smul_apply,hP,withDensity_apply _ hs]
  simp_rw [ENNReal.ofReal_mul (F.weights.nonneg i)]
  rw [lintegral_const_mul _ (hg (F.parameter i)).ennreal_ofReal]
  rfl

/-- Finiteness of KL is preserved by actual finite convex mixtures. -/
theorem finiteMixture_kl_ne_top_of_densities {P : ι → Measure α}
    [∀ i, IsProbabilityMeasure (P i)] (F : FiniteMixture P)
    (g : ι → α → ℝ) (hg : ∀ i, Measurable (g i)) (hg0 : ∀ i x, 0 ≤ g i x)
    (hP : ∀ i, P i = P₀.withDensity (fun x => ENNReal.ofReal (g i x)))
    (hKL : ∀ i, klDiv (P i) P₀ ≠ ∞) : klDiv F.measure P₀ ≠ ∞ := by
  let u : α → ℝ := fun x => ∑ i, F.weights.w i*g (F.parameter i) x
  have hu : Measurable u := Finset.measurable_sum _ (fun i _ => measurable_const.mul (hg _))
  have hu0 (x : α) : 0 ≤ u x := Finset.sum_nonneg (fun i _ => mul_nonneg (F.weights.nonneg i) (hg0 _ _))
  have hQ : F.measure = P₀.withDensity (fun x => ENNReal.ofReal (u x)) := finiteMixture_density F g hg hg0 hP
  have hac : F.measure ≪ P₀ := hQ ▸ withDensity_absolutelyContinuous _ _
  have hbound : Integrable (fun x => ∑ i, F.weights.w i*klFun (g (F.parameter i) x)) P₀ :=
    integrable_finset_sum _ (fun i _ =>
      (integrable_klFun_density (hg _) (hg0 _) (hP _) (hKL _)).const_mul _)
  have hi : Integrable (fun x => klFun (u x)) P₀ := by
    apply hbound.mono' (InformationTheory.continuous_klFun.measurable.comp hu).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (klFun_nonneg (hu0 x))]
    exact convexOn_klFun.map_sum_le (fun i _ => F.weights.nonneg i) F.weights.sum_eq_one
      (fun i _ => hg0 (F.parameter i) x)
  have hrn := Measure.rnDeriv_withDensity P₀ hu.ennreal_ofReal
  have hirn : Integrable (fun x => klFun ((F.measure.rnDeriv P₀ x).toReal)) P₀ := by
    apply hi.congr
    filter_upwards [hrn] with x hx
    rw [hQ,hx,ENNReal.toReal_ofReal (hu0 x)]
  exact klDiv_ne_top_iff.mpr ⟨hac,(integrable_klFun_rnDeriv_iff hac).mp hirn⟩

end BoundaryReduction.MeasureGrow
