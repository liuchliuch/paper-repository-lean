import Paper14.ExcessMarginalLimits
import Paper14.DominatedProductLimits

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal
namespace Paper14
noncomputable section

/-- The level-0/level-1 rectangle isolates the second-coordinate shift. -/
theorem level01_product_integral_le {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
    {T φ : E → E} (hT : MeasurePreserving T μ μ) {Y : Set E} (hY : MeasurableSet Y) (hp : 0<μ Y)
    (hφ : MeasurePreserving φ μ (normalizedRestriction μ Y))
    (hc : ∀ᵐ x ∂μ,inducedMap T Y (φ x)=φ (T x))
    (n : ℕ) {F : E × E → ℝ} (hF : Measurable F) (hb : ∀ p,‖F p‖≤1)
    (hinv : ∀ p : E × E,F (T p.1,T p.2)=F p) :
    (∫ p,‖F (p.1,T p.2)-F p‖ ∂((excessMarginalFinite T μ Y n 0).prod (excessMarginalFinite T μ Y n 1) : Measure (E × E))) ≤
      ∫ p,‖F ((inducedMap T Y)^[n] p.1,(inducedMap T Y)^[n] p.2)-F p‖
        ∂(normalizedRestriction μ Y).prod (normalizedRestriction μ Y) := by
  let ν := normalizedRestriction μ Y
  let S := inducedMap T Y
  letI := normalizedRestriction_probability hp.ne'
  have hS := induced_preserves_of_conjugacy hT hY hφ hc
  let D : E × E → ℝ := fun p => ‖F (S^[n] p.1,S^[n] p.2)-F p‖
  have hDmeas : Measurable D :=
    ((hF.comp ((hS.measurable.iterate n).prodMap (hS.measurable.iterate n))).sub hF).norm
  have hDI : Integrable D (ν.prod ν) := by
    apply Integrable.of_bound hDmeas.aestronglyMeasurable 2
    filter_upwards [] with p
    change ‖‖F (S^[n] p.1,S^[n] p.2)-F p‖‖≤2
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (by nlinarith [hb (S^[n] p.1,S^[n] p.2),hb p])
  have hFiter (k : ℕ) (p : E × E) : F (T^[k] p.1,T^[k] p.2)=F p := by
    induction k with
    | zero => rfl
    | succ k ih => rw [iterate_succ_apply',iterate_succ_apply',hinv (T^[k] p.1,T^[k] p.2),ih]
  have hE (j : ℕ) : MeasurableSet (excessLevel T Y n j) :=
    hY.inter ((measurable_excessDn hT.measurable hY n) (measurableSet_singleton j))
  have hge := ae_Rn_ge hT hY hS n
  have hgeProd : ∀ᵐ p ∂ν.prod ν,n≤Rn T Y n p.1 ∧ n≤Rn T Y n p.2 := by
    filter_upwards [(measurePreserving_fst (μ := ν) (ν := ν)).quasiMeasurePreserving.ae hge,
      (measurePreserving_snd (μ := ν) (ν := ν)).quasiMeasurePreserving.ae hge] with p hp hq
    exact ⟨hp,hq⟩
  change (∫ p,‖F (p.1,T p.2)-F p‖ ∂(excessMarginalFinite T μ Y n 0 : Measure E).prod (excessMarginalFinite T μ Y n 1 : Measure E))≤_
  rw [excessMarginalFinite_coe hT.measurable,excessMarginalFinite_coe hT.measurable,Measure.prod_restrict]
  have heq : (∫ p,‖F (p.1,T p.2)-F p‖ ∂(ν.prod ν).restrict (excessLevel T Y n 0 ×ˢ excessLevel T Y n 1))=
      ∫ p,D p ∂(ν.prod ν).restrict (excessLevel T Y n 0 ×ˢ excessLevel T Y n 1) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem ((hE 0).prod (hE 1)),ae_restrict_of_ae hgeProd] with p hp hgeP
    have hR0 : Rn T Y n p.1=n := by
      have hh := hp.1.2
      change Rn T Y n p.1-n=0 at hh
      omega
    have hR1 : Rn T Y n p.2=n+1 := by
      have hh := hp.2.2
      change Rn T Y n p.2-n=1 at hh
      omega
    change ‖F (p.1,T p.2)-F p‖=‖F ((inducedMap T Y)^[n] p.1,(inducedMap T Y)^[n] p.2)-F p‖
    rw [induced_iterate_eq,induced_iterate_eq,hR0,hR1,iterate_succ_apply,hFiter n (p.1,T p.2)]
  rw [heq]
  exact integral_mono_measure Measure.restrict_le_self (Eventually.of_forall (fun p => norm_nonneg _)) hDI

end
end Paper14
