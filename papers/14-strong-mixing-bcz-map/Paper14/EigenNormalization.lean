import Paper14.WeakMixing
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory Filter Function Set
namespace Paper14
noncomputable section

lemma eigen_norm_eq_one {A : Type*} [MeasurableSpace A] {μ : Measure A} [IsProbabilityMeasure μ]
    {T : A → A} (hT : MeasurePreserving T μ μ) {f : A → ℂ} (hf : MemLp f 2 μ)
    (hf0 : ¬ f=ᵐ[μ] 0) {eig : ℂ} (heig : ∀ᵐ x ∂μ,f (T x)=eig*f x) : ‖eig‖=1 := by
  have hI : Integrable f μ := hf.integrable (by norm_num)
  have hIne : (∫ x,‖f x‖ ∂μ) ≠ 0 := by
    intro hz
    have he := (integral_eq_zero_iff_of_nonneg (fun x => norm_nonneg (f x)) hI.norm).mp hz
    apply hf0
    filter_upwards [he] with x hx
    exact norm_eq_zero.mp hx
  have hm : AEStronglyMeasurable (fun x => ‖f x‖) (Measure.map T μ) := by
    rw [hT.map_eq]
    exact hI.norm.aestronglyMeasurable
  have hmap := integral_map hT.measurable.aemeasurable hm
  rw [hT.map_eq] at hmap
  have he : (∫ x,‖f (T x)‖ ∂μ) = ‖eig‖*(∫ x,‖f x‖ ∂μ) := by
    calc
      _ = ∫ x,‖eig‖*‖f x‖ ∂μ := integral_congr_ae (heig.mono (fun x hx => by rw [hx,norm_mul]))
      _ = _ := integral_const_mul _ _
  have hh : (‖eig‖-1)*(∫ x,‖f x‖ ∂μ)=0 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hIne)

/-- Ergodicity gives the normalized bounded measurable eigenfunction used in Appendix A. -/
theorem normalized_eigenfunction {A : Type*} [MeasurableSpace A] {μ : Measure A} [IsProbabilityMeasure μ]
    {T : A → A} (hT : Ergodic T μ) {f : A → ℂ} (hf : MemLp f 2 μ)
    (hf0 : ¬ f=ᵐ[μ] 0) {eig : ℂ} (heig : ∀ᵐ x ∂μ,f (T x)=eig*f x) :
    ‖eig‖=1 ∧ ∃ g : A → ℂ,Measurable g ∧ (∀ x,‖g x‖≤1) ∧
      (∀ᵐ x ∂μ,‖g x‖=1) ∧ (∀ᵐ x ∂μ,g (T x)=eig*g x) := by
  classical
  have heigNorm := eigen_norm_eq_one hT.1 hf hf0 heig
  have hinv : (fun x => ‖f (T x)‖) =ᵐ[μ] (fun x => ‖f x‖) := by
    filter_upwards [heig] with x hx
    rw [hx,norm_mul,heigNorm,one_mul]
  obtain ⟨c,hc⟩ := hT.ae_eq_const_of_ae_eq_comp_ae hf.norm.aestronglyMeasurable hinv
  have hc0 : 0<c := by
    obtain ⟨x,hx⟩ := hc.exists
    change ‖f x‖=c at hx
    have hcge : 0≤c := by rw [← hx]; exact norm_nonneg _
    apply lt_of_le_of_ne hcge
    intro hz
    apply hf0
    filter_upwards [hc] with x hx
    apply norm_eq_zero.mp
    simpa [const_apply,← hz] using hx
  let f₀ := hf.aestronglyMeasurable.mk f
  have hf₀ : Measurable f₀ := hf.aestronglyMeasurable.measurable_mk
  have hff₀ : f=ᵐ[μ] f₀ := hf.aestronglyMeasurable.ae_eq_mk
  let S := {x | ‖f₀ x‖=c}
  let g : A → ℂ := S.indicator (fun x => f₀ x/(c : ℂ))
  have hS : MeasurableSet S := measurableSet_eq_fun hf₀.norm measurable_const
  have hg : Measurable g := (hf₀.div_const _).indicator hS
  have hunit (x : A) (hx : x∈S) : ‖g x‖=1 := by
    rw [show g x=f₀ x/(c : ℂ) from Set.indicator_of_mem hx _]
    rw [norm_div,show ‖f₀ x‖=c from hx,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc0,div_self hc0.ne']
  have hgb (x : A) : ‖g x‖≤1 := by
    by_cases hx : x∈S
    · exact (hunit x hx).le
    · simp [g,hx]
  have hSae : ∀ᵐ x ∂μ,x∈S := by
    filter_upwards [hc,hff₀] with x hx hfx
    change ‖f₀ x‖=c
    simpa only [const_apply,hfx] using hx
  have hgeq : g=ᵐ[μ] (fun x => f x/(c : ℂ)) := by
    filter_upwards [hSae,hff₀] with x hx hfx
    rw [show g x=f₀ x/(c : ℂ) from Set.indicator_of_mem hx _,hfx]
  refine ⟨heigNorm,g,hg,hgb,hSae.mono hunit,?_⟩
  filter_upwards [hgeq,hT.1.quasiMeasurePreserving.ae_eq hgeq,heig] with x hx hxT hfx
  change g (T x)=f (T x)/(c : ℂ) at hxT
  rw [hxT,hfx,hx]
  ring

end
end Paper14
