import Paper36.MixedProcess

/-! Adding an arbitrary measurable learner choice preserves the proved fresh
row-stack conditional law. This is the bridge from pre-planning history to the
analyst information that also contains the newly sampled posterior model/policy. -/
namespace Paper36.AdaptiveKernel
noncomputable section
open MeasureTheory ProbabilityTheory

variable {Ω Info Aux Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Aux] [MeasurableSpace Y]

/-- Sample the learner's new auxiliary choice from its current information. The
full original experiment, including every unused tape coordinate, is retained. -/
def choiceExtension (μ : Measure Ω) (X : Ω → Info) (hX : Measurable X)
    (choose : ProbabilityTheory.Kernel Info Aux) : Measure (Ω × Aux) :=
  μ ⊗ₘ choose.comap X hX

instance choiceExtension_probability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Info) (hX : Measurable X) (choose : ProbabilityTheory.Kernel Info Aux) [IsMarkovKernel choose] :
    IsProbabilityMeasure (choiceExtension μ X hX choose) := by
  unfold choiceExtension
  infer_instance

/-- A fresh variable remains fresh after any random learner choice that uses the
current information. No finiteness or discreteness of the choice is assumed. -/
theorem freshChoice_joint (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Info) (hX : Measurable X) (Z : Ω → Y) (hZ : Measurable Z)
    (fresh : ProbabilityTheory.Kernel Info Y) [IsMarkovKernel fresh]
    (choose : ProbabilityTheory.Kernel Info Aux) [IsMarkovKernel choose]
    (hjoint : μ.map (fun ω => (X ω,Z ω)) = μ.map X ⊗ₘ fresh) :
    (choiceExtension μ X hX choose).map (fun z => ((X z.1,z.2),Z z.1)) =
      (μ.map X ⊗ₘ choose) ⊗ₘ fresh.prodMkRight Aux := by
  apply (Measure.ext_iff_lintegral _).mpr
  intro f hf
  have hfext : Measurable (fun z : Ω × Aux => f ((X z.1,z.2),Z z.1)) :=
    hf.comp (((hX.comp measurable_fst).prodMk measurable_snd).prodMk (hZ.comp measurable_fst))
  have hg0 : Measurable (fun z : (Info × Y) × Aux => f ((z.1.1,z.2),z.1.2)) :=
    hf.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)
  let κ : ProbabilityTheory.Kernel (Info × Y) Aux := choose.comap Prod.fst measurable_fst
  have hg : Measurable (fun z : Info × Y => ∫⁻ a, f ((z.1,a),z.2) ∂choose z.1) :=
    hg0.lintegral_kernel_prod_right' (κ := κ)
  calc
    _ = ∫⁻ z, f ((X z.1,z.2),Z z.1) ∂choiceExtension μ X hX choose :=
      lintegral_map hf (by fun_prop)
    _ = ∫⁻ ω, ∫⁻ a, f ((X ω,a),Z ω) ∂choose (X ω) ∂μ := by
      rw [choiceExtension, Measure.lintegral_compProd hfext]
      rfl
    _ = ∫⁻ z, ∫⁻ a, f ((z.1,a),z.2) ∂choose z.1 ∂μ.map (fun ω => (X ω,Z ω)) :=
      (lintegral_map hg (hX.prodMk hZ)).symm
    _ = ∫⁻ i, ∫⁻ y, ∫⁻ a, f ((i,a),y) ∂choose i ∂fresh i ∂μ.map X := by
      rw [hjoint, Measure.lintegral_compProd hg]
    _ = ∫⁻ i, ∫⁻ a, ∫⁻ y, f ((i,a),y) ∂fresh i ∂choose i ∂μ.map X := by
      apply lintegral_congr_ae
      apply ae_of_all
      intro i
      have hfi : Measurable (fun z : Y × Aux => f ((i,z.2),z.1)) :=
        hf.comp ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)
      exact lintegral_lintegral_swap hfi.aemeasurable
    _ = _ := by
      have hg1 : Measurable (fun z : (Info × Aux) × Y => f (z.1,z.2)) := hf
      rw [Measure.lintegral_compProd hg1,
        Measure.lintegral_compProd (hg1.lintegral_kernel_prod_right' (κ := fresh.prodMkRight Aux))]
      rfl

theorem freshChoice_information (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Info) (hX : Measurable X) (choose : ProbabilityTheory.Kernel Info Aux) [IsMarkovKernel choose] :
    (choiceExtension μ X hX choose).map (fun z => (X z.1,z.2)) = μ.map X ⊗ₘ choose := by
  apply (Measure.ext_iff_lintegral _).mpr
  intro f hf
  have hfe : Measurable (fun z : Ω × Aux => f (X z.1,z.2)) :=
    hf.comp ((hX.comp measurable_fst).prodMk measurable_snd)
  have hg : Measurable (fun i => ∫⁻ a, f (i,a) ∂choose i) := hf.lintegral_kernel_prod_right'
  calc
    _ = ∫⁻ z, f (X z.1,z.2) ∂choiceExtension μ X hX choose := lintegral_map hf (by fun_prop)
    _ = ∫⁻ ω, ∫⁻ a, f (X ω,a) ∂choose (X ω) ∂μ := by
      rw [choiceExtension, Measure.lintegral_compProd hfe]
      rfl
    _ = ∫⁻ i, ∫⁻ a, f (i,a) ∂choose i ∂μ.map X := (lintegral_map hg hX).symm
    _ = _ := (Measure.lintegral_compProd hf).symm

/-- In particular, adding the current posterior sample and its selected policy
preserves the fresh-unused-row conditional law. -/
theorem freshChoice_condDistrib [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Info) (hX : Measurable X) (Z : Ω → Y) (hZ : Measurable Z)
    (fresh : ProbabilityTheory.Kernel Info Y) [IsMarkovKernel fresh]
    (choose : ProbabilityTheory.Kernel Info Aux) [IsMarkovKernel choose]
    (hfresh : condDistrib Z X μ =ᵐ[μ.map X] fresh) :
    condDistrib (fun z : Ω × Aux => Z z.1) (fun z => (X z.1,z.2)) (choiceExtension μ X hX choose)
      =ᵐ[μ.map X ⊗ₘ choose] fresh.prodMkRight Aux := by
  have hjoint := (condDistrib_ae_eq_iff_measure_eq_compProd X hZ.aemeasurable fresh).mp hfresh
  have he := freshChoice_joint μ X hX Z hZ fresh choose hjoint
  rw [← freshChoice_information μ X hX choose] at he
  have hc := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := choiceExtension μ X hX choose) ((hX.comp measurable_fst).prodMk measurable_snd)
    (hZ.comp measurable_fst) he
  simpa only [Function.comp_def, freshChoice_information μ X hX choose] using hc

end
end Paper36.AdaptiveKernel
