import Paper14.MeasureLimits
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal BoundedContinuousFunction
namespace Paper14
noncomputable section

lemma integrable_of_measurable_bound {E : Type*} [MeasurableSpace E] {μ : Measure E}
    [IsFiniteMeasure μ] {f : E → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall hC)

lemma integral_fst_le_of_marginal {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {η : Measure (E × E)} {C : ℝ≥0} {f : E → ℝ}
    (hη : η.fst ≤ C • μ) (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) :
    (∫ z, f z.1 ∂η) ≤ C * ∫ x, f x ∂μ := by
  have hfi : Integrable f (C • μ) := hf.smul_measure ENNReal.coe_ne_top
  have hmap : Integrable f η.fst := hfi.mono_measure hη
  rw [show (∫ z, f z.1 ∂η) = ∫ x, f x ∂η.fst from
    (integral_map measurable_fst.aemeasurable hmap.aestronglyMeasurable).symm]
  calc _ ≤ ∫ x, f x ∂(C • μ) :=
         integral_mono_measure hη (Eventually.of_forall hf0) hfi
       _ = C * ∫ x, f x ∂μ := by rw [integral_smul_nnreal_measure]; rfl

lemma integral_snd_le_of_marginal {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {η : Measure (E × E)} {C : ℝ≥0} {f : E → ℝ}
    (hη : η.snd ≤ C • μ) (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) :
    (∫ z, f z.2 ∂η) ≤ C * ∫ x, f x ∂μ := by
  have hfi : Integrable f (C • μ) := hf.smul_measure ENNReal.coe_ne_top
  have hmap : Integrable f η.snd := hfi.mono_measure hη
  rw [show (∫ z, f z.2 ∂η) = ∫ x, f x ∂η.snd from
    (integral_map measurable_snd.aemeasurable hmap.aestronglyMeasurable).symm]
  calc _ ≤ ∫ x, f x ∂(C • μ) :=
         integral_mono_measure hη (Eventually.of_forall hf0) hfi
       _ = C * ∫ x, f x ∂μ := by rw [integral_smul_nnreal_measure]; rfl

/-- A product-test approximation bound using the marginal domination.
For bounded tests, L1 density suffices and avoids extra spectral inputs. -/
theorem bounded_product_approximation {E : Type*} [MeasurableSpace E]
    [TopologicalSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasure μ]
    (η : Measure (E × E)) [IsFiniteMeasure η] {C : ℝ≥0}
    (hfst : η.fst ≤ C • μ) (hsnd : η.snd ≤ C • μ)
    {f g : E → ℝ} (hf : Measurable f) (hg : Measurable g)
    {Bf Bg : ℝ} (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg)
    (hfb : ∀ x, ‖f x‖ ≤ Bf) (hgb : ∀ x, ‖g x‖ ≤ Bg)
    (f0 g0 : E →ᵇ ℝ) :
    |(∫ z, f z.1 * g z.2 ∂η) - ∫ z, f0 z.1 * g0 z.2 ∂η| ≤
      C * (Bg * (∫ x, ‖f x-f0 x‖ ∂μ) + ‖f0‖ * (∫ x, ‖g x-g0 x‖ ∂μ)) := by
  have hfI := integrable_of_measurable_bound (μ := μ) hf Bf hfb
  have hgI := integrable_of_measurable_bound (μ := μ) hg Bg hgb
  have hp : Integrable (fun z : E × E => f z.1*g z.2) η :=
    integrable_of_measurable_bound ((hf.comp measurable_fst).mul (hg.comp measurable_snd))
      (Bf*Bg) (fun z => by rw [norm_mul]; exact mul_le_mul (hfb z.1) (hgb z.2) (norm_nonneg _) hBf)
  have hp0 : Integrable (fun z : E × E => f0 z.1*g0 z.2) η := by
    apply integrable_of_measurable_bound (f := fun z : E × E => f0 z.1*g0 z.2)
      (by fun_prop) (‖f0‖*‖g0‖)
    intro z
    rw [norm_mul]
    exact mul_le_mul (f0.norm_coe_le_norm z.1) (g0.norm_coe_le_norm z.2)
      (norm_nonneg _) (norm_nonneg _)
  have hfe := (hfI.sub (f0.integrable μ)).norm
  have hge := (hgI.sub (g0.integrable μ)).norm
  have hfeη : Integrable (fun z : E × E => ‖f z.1-f0 z.1‖) η := by
    exact (integrable_map_measure ((hfe.smul_measure ENNReal.coe_ne_top).mono_measure hfst).aestronglyMeasurable
      measurable_fst.aemeasurable).mp ((hfe.smul_measure ENNReal.coe_ne_top).mono_measure hfst)
  have hgeη : Integrable (fun z : E × E => ‖g z.2-g0 z.2‖) η := by
    exact (integrable_map_measure ((hge.smul_measure ENNReal.coe_ne_top).mono_measure hsnd).aestronglyMeasurable
      measurable_snd.aemeasurable).mp ((hge.smul_measure ENNReal.coe_ne_top).mono_measure hsnd)
  rw [← integral_sub hp hp0,← Real.norm_eq_abs]
  calc _ ≤ ∫ z, ‖f z.1*g z.2-f0 z.1*g0 z.2‖ ∂η := norm_integral_le_integral_norm _
       _ ≤ ∫ z, Bg * ‖f z.1-f0 z.1‖ + ‖f0‖ * ‖g z.2-g0 z.2‖ ∂η := by
         apply integral_mono (hp.sub hp0).norm ((hfeη.const_mul Bg).add (hgeη.const_mul ‖f0‖))
         intro z
         calc ‖f z.1*g z.2-f0 z.1*g0 z.2‖ =
             ‖(f z.1-f0 z.1)*g z.2+f0 z.1*(g z.2-g0 z.2)‖ := by congr 1; ring
              _ ≤ ‖(f z.1-f0 z.1)*g z.2‖+‖f0 z.1*(g z.2-g0 z.2)‖ := norm_add_le _ _
              _ ≤ Bg * ‖f z.1-f0 z.1‖ + ‖f0‖ * ‖g z.2-g0 z.2‖ := by
                simp only [norm_mul]
                nlinarith [hgb z.2,f0.norm_coe_le_norm z.1,norm_nonneg (f z.1-f0 z.1),norm_nonneg (g z.2-g0 z.2)]
       _ = Bg * (∫ z, ‖f z.1-f0 z.1‖ ∂η) + ‖f0‖ * (∫ z, ‖g z.2-g0 z.2‖ ∂η) := by
         rw [integral_add (hfeη.const_mul _) (hgeη.const_mul _),integral_const_mul,integral_const_mul]
       _ ≤ Bg * (C * ∫ x, ‖f x-f0 x‖ ∂μ) + ‖f0‖ * (C * ∫ x, ‖g x-g0 x‖ ∂μ) :=
         add_le_add (mul_le_mul_of_nonneg_left (integral_fst_le_of_marginal hfst hfe (fun _ => norm_nonneg _)) hBg)
           (mul_le_mul_of_nonneg_left (integral_snd_le_of_marginal hsnd hge (fun _ => norm_nonneg _)) (norm_nonneg _))
       _ = _ := by ring

/-- Dominated marginals allow weak convergence to be tested against every
fixed bounded measurable product, even though the underlying map is merely
measurable. -/
theorem tendsto_bounded_product_of_continuous_products {E : Type*} [MeasurableSpace E]
    [MetricSpace E] [CompactSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasure μ]
    {ηn : ℕ → FiniteMeasure (E × E)} {η : FiniteMeasure (E × E)}
    (hlim : ∀ f0 g0 : E →ᵇ ℝ,
      Tendsto (fun n => ∫ z, f0 z.1*g0 z.2 ∂(ηn n : Measure (E × E))) atTop
        (𝓝 (∫ z, f0 z.1*g0 z.2 ∂(η : Measure (E × E))))) (C : ℝ≥0)
    (hfstn : ∀ n, (ηn n : Measure (E × E)).fst ≤ C • μ)
    (hsndn : ∀ n, (ηn n : Measure (E × E)).snd ≤ C • μ)
    (hfst : (η : Measure (E × E)).fst ≤ C • μ)
    (hsnd : (η : Measure (E × E)).snd ≤ C • μ)
    {f g : E → ℝ} (hf : Measurable f) (hg : Measurable g)
    {Bf Bg : ℝ} (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg)
    (hfb : ∀ x, ‖f x‖ ≤ Bf) (hgb : ∀ x, ‖g x‖ ≤ Bg) :
    Tendsto (fun n => ∫ z, f z.1*g z.2 ∂(ηn n : Measure (E × E)))
      atTop (𝓝 (∫ z, f z.1*g z.2 ∂(η : Measure (E × E)))) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hC : 0 ≤ (C : ℝ) := C.coe_nonneg
  have hd1 : 0 < ε / (8*((C:ℝ)+1)*(Bg+1)) := by positivity
  obtain ⟨f0,hf0,_⟩ := (integrable_of_measurable_bound (μ := μ) hf Bf hfb).exists_boundedContinuous_integral_sub_le hd1
  have hd2 : 0 < ε / (8*((C:ℝ)+1)*(‖f0‖+1)) := by positivity
  obtain ⟨g0,hg0,_⟩ := (integrable_of_measurable_bound (μ := μ) hg Bg hgb).exists_boundedContinuous_integral_sub_le hd2
  have herr (ζ : FiniteMeasure (E × E))
      (hζf : (ζ : Measure (E × E)).fst ≤ C • μ)
      (hζg : (ζ : Measure (E × E)).snd ≤ C • μ) :
      |(∫ z, f z.1*g z.2 ∂(ζ : Measure (E × E))) -
        ∫ z, f0 z.1*g0 z.2 ∂(ζ : Measure (E × E))| ≤ ε/4 := by
    apply (bounded_product_approximation (ζ : Measure (E × E)) hζf hζg hf hg hBf hBg hfb hgb f0 g0).trans
    have ht1 : (C:ℝ)*Bg*(ε/(8*((C:ℝ)+1)*(Bg+1))) ≤ ε/8 := by
      have hmul := mul_le_mul_of_nonneg_right
        (show (C:ℝ)*Bg ≤ ((C:ℝ)+1)*(Bg+1) by nlinarith) hd1.le
      have heq : (8*((C:ℝ)+1)*(Bg+1))*(ε/(8*((C:ℝ)+1)*(Bg+1))) = ε :=
        mul_div_cancel₀ _ (by positivity)
      nlinarith
    have ht2 : (C:ℝ)*‖f0‖*(ε/(8*((C:ℝ)+1)*(‖f0‖+1))) ≤ ε/8 := by
      have hmul := mul_le_mul_of_nonneg_right
        (show (C:ℝ)*‖f0‖ ≤ ((C:ℝ)+1)*(‖f0‖+1) by nlinarith [norm_nonneg f0]) hd2.le
      have heq : (8*((C:ℝ)+1)*(‖f0‖+1))*(ε/(8*((C:ℝ)+1)*(‖f0‖+1))) = ε :=
        mul_div_cancel₀ _ (by positivity)
      nlinarith
    have hb1 := mul_le_mul_of_nonneg_left hf0 (mul_nonneg hC hBg)
    have hb2 := mul_le_mul_of_nonneg_left hg0 (mul_nonneg hC (norm_nonneg f0))
    nlinarith
  have hc := Metric.tendsto_atTop.mp (hlim f0 g0) (ε/2) (by positivity)
  obtain ⟨N,hN⟩ := hc
  refine ⟨N,fun n hn => ?_⟩
  have hmid : |(∫ z, f0 z.1*g0 z.2 ∂(ηn n : Measure (E × E))) -
      ∫ z, f0 z.1*g0 z.2 ∂(η : Measure (E × E))| < ε/2 := by
    simpa only [Real.dist_eq] using hN n hn
  rw [Real.dist_eq]
  have htri := abs_add_three
    ((∫ z, f z.1*g z.2 ∂(ηn n : Measure (E × E))) - ∫ z, f0 z.1*g0 z.2 ∂(ηn n : Measure (E × E)))
    ((∫ z, f0 z.1*g0 z.2 ∂(ηn n : Measure (E × E))) - ∫ z, f0 z.1*g0 z.2 ∂(η : Measure (E × E)))
    ((∫ z, f0 z.1*g0 z.2 ∂(η : Measure (E × E))) - ∫ z, f z.1*g z.2 ∂(η : Measure (E × E)))
  have he1 := herr (ηn n) (hfstn n) (hsndn n)
  have he2 := herr η hfst hsnd
  rw [abs_sub_comm] at he2
  simp only [sub_add_sub_cancel] at htri
  linarith

/-- Weak convergence gives all bounded measurable product tests under
uniform marginal domination. -/
theorem weak_limit_bounded_product {E : Type*} [MeasurableSpace E]
    [MetricSpace E] [CompactSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasure μ]
    {ηn : ℕ → FiniteMeasure (E × E)} {η : FiniteMeasure (E × E)}
    (hlim : Tendsto ηn atTop (𝓝 η)) (C : ℝ≥0)
    (hfstn : ∀ n, (ηn n : Measure (E × E)).fst ≤ C • μ)
    (hsndn : ∀ n, (ηn n : Measure (E × E)).snd ≤ C • μ)
    (hfst : (η : Measure (E × E)).fst ≤ C • μ)
    (hsnd : (η : Measure (E × E)).snd ≤ C • μ)
    {f g : E → ℝ} (hf : Measurable f) (hg : Measurable g)
    {Bf Bg : ℝ} (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg)
    (hfb : ∀ x, ‖f x‖ ≤ Bf) (hgb : ∀ x, ‖g x‖ ≤ Bg) :
    Tendsto (fun n => ∫ z, f z.1*g z.2 ∂(ηn n : Measure (E × E)))
      atTop (𝓝 (∫ z, f z.1*g z.2 ∂(η : Measure (E × E)))) := by
  apply tendsto_bounded_product_of_continuous_products ?_ C hfstn hsndn hfst hsnd hf hg hBf hBg hfb hgb
  intro f0 g0
  let F0 : (E × E) →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun z => f0 z.1*g0 z.2,by fun_prop⟩
  exact FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hlim F0

/-- Finite measures with dominated marginals are determined by continuous
product tests. This is proved through measurable rectangle indicators. -/
theorem finiteMeasure_eq_of_continuous_products {E : Type*} [MeasurableSpace E]
    [MetricSpace E] [CompactSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasure μ]
    (η ζ : FiniteMeasure (E × E)) (C : ℝ≥0)
    (hηf : (η : Measure (E × E)).fst ≤ C • μ)
    (hηg : (η : Measure (E × E)).snd ≤ C • μ)
    (hζf : (ζ : Measure (E × E)).fst ≤ C • μ)
    (hζg : (ζ : Measure (E × E)).snd ≤ C • μ)
    (hprod : ∀ f0 g0 : E →ᵇ ℝ,
      (∫ z, f0 z.1*g0 z.2 ∂(η : Measure (E × E))) =
        ∫ z, f0 z.1*g0 z.2 ∂(ζ : Measure (E × E))) : η = ζ := by
  apply FiniteMeasure.toMeasure_injective
  apply Measure.ext_prod
  intro A B hA hB
  let f : E → ℝ := A.indicator (fun _ => 1)
  let g : E → ℝ := B.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hA
  have hg : Measurable g := measurable_const.indicator hB
  have hfb : ∀ x, ‖f x‖ ≤ 1 := by intro x; by_cases hx : x ∈ A <;> simp [f,hx]
  have hgb : ∀ x, ‖g x‖ ≤ 1 := by intro x; by_cases hx : x ∈ B <;> simp [g,hx]
  have hcts : ∀ f0 g0 : E →ᵇ ℝ,
      Tendsto (fun _ : ℕ => ∫ z, f0 z.1*g0 z.2 ∂(η : Measure (E × E))) atTop
        (𝓝 (∫ z, f0 z.1*g0 z.2 ∂(ζ : Measure (E × E)))) := by
    intro f0 g0
    rw [hprod f0 g0]
    exact tendsto_const_nhds
  have hlim := tendsto_bounded_product_of_continuous_products hcts C
    (fun _ => hηf) (fun _ => hηg) hζf hζg hf hg (by norm_num) (by norm_num) hfb hgb
  have heq := tendsto_nhds_unique tendsto_const_nhds hlim
  have hind : (fun z : E × E => f z.1*g z.2) = (A ×ˢ B).indicator (fun _ => (1 : ℝ)) := by
    funext z
    by_cases ha : z.1 ∈ A <;> by_cases hb : z.2 ∈ B <;> simp [f,g,ha,hb]
  rw [hind,integral_indicator (hA.prod hB),integral_indicator (hA.prod hB),integral_const,integral_const] at heq
  simp only [Measure.restrict_apply_univ,smul_eq_mul,mul_one,Measure.real] at heq
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp heq

end
end Paper14
