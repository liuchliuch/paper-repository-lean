import Paper14.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Filter Topology Set
open scoped MeasureTheory ENNReal InnerProductSpace
namespace Paper14
noncomputable section

/-- One direction of the original set/L2 correlation equivalence. -/
theorem strongMixing_of_L2 {A : Type*} [MeasurableSpace A] {μ : Measure A} [IsProbabilityMeasure μ]
    {T : A → A} (hT : Measurable T) (hL2 : StrongMixingL2 T μ) : StrongMixing T μ := by
  intro U V hU hV
  let f : A → ℝ := V.indicator (fun _ => 1)
  let g : A → ℝ := U.indicator (fun _ => 1)
  have hf : MemLp f 2 μ := (memLp_const (1 : ℝ)).indicator hV
  have hg : MemLp g 2 μ := (memLp_const (1 : ℝ)).indicator hU
  have ht := hL2 f g hf hg
  have heq (n : ℕ) : (∫ x,f x*g (T^[n] x) ∂μ) = μ.real ((T^[n]) ⁻¹' U ∩ V) := by
    have hfunc : (fun x => f x*g (T^[n] x)) = ((T^[n]) ⁻¹' U ∩ V).indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hxU : T^[n] x∈U <;> by_cases hxV : x∈V <;> simp [f,g,hxU,hxV]
    rw [hfunc,integral_indicator (((hT.iterate n) hU).inter hV),setIntegral_const]
    simp
  have hfi : (∫ x,f x ∂μ)=μ.real V := by rw [integral_indicator hV,setIntegral_const]; simp
  have hgi : (∫ x,g x ∂μ)=μ.real U := by rw [integral_indicator hU,setIntegral_const]; simp
  simp only [heq,hfi,hgi] at ht
  have hE := ENNReal.tendsto_ofReal ht
  have hv (n : ℕ) : ENNReal.ofReal (μ.real ((T^[n]) ⁻¹' U ∩ V))=μ ((T^[n]) ⁻¹' U ∩ V) :=
    ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hc : ENNReal.ofReal (μ.real V*μ.real U)=μ U*μ V := by
    change ENNReal.ofReal ((μ V).toReal*(μ U).toReal)=_
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal (measure_ne_top _ _),
      ENNReal.ofReal_toReal (measure_ne_top _ _),mul_comm]
  simpa only [hv,hc] using hE

lemma integral_mul_le_L2 {A : Type*} [MeasurableSpace A] {μ : Measure A} {f g : A → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x,f x*g x ∂μ| ≤ (eLpNorm f 2 μ).toReal*(eLpNorm g 2 μ).toReal := by
  have hi : inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x,f x*g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
    simp only [hx,hy,RCLike.inner_apply,conj_trivial,mul_comm]
  rw [← hi,← Real.norm_eq_abs,← Lp.norm_toLp f hf,← Lp.norm_toLp g hg]
  exact norm_inner_le_norm _ _

def realCorrelation {A : Type*} [MeasurableSpace A] (T : A → A) (μ : Measure A) (f g : A → ℝ) (n : ℕ) : ℝ :=
  (∫ x,f x*g (T^[n] x) ∂μ)-(∫ x,f x ∂μ)*(∫ x,g x ∂μ)

section CorrelationBounds
variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [IsProbabilityMeasure μ]
  {T : A → A} (hT : MeasurePreserving T μ μ) {f f₀ g g₀ : A → ℝ}

include hT

lemma integrable_mul_iterate (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (n : ℕ) :
    Integrable (fun x => f x*g (T^[n] x)) μ := by
  exact memLp_one_iff_integrable.mp ((hg.comp_measurePreserving (hT.iterate n)).mul' hf)

omit hT in
lemma integral_le_L2 (hf : MemLp f 2 μ) : |∫ x,f x ∂μ|≤(eLpNorm f 2 μ).toReal := by
  have hh := integral_mul_le_L2 hf (memLp_const (μ := μ) (1 : ℝ))
  have he : eLpNorm (fun _ : A => (1 : ℝ)) 2 μ=1 := by
    rw [eLpNorm_const' _ (by norm_num) (by norm_num)]
    simp
  simpa only [mul_one,he,ENNReal.toReal_one] using hh

lemma realCorrelation_bound (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (n : ℕ) :
    |realCorrelation T μ f g n|≤2*((eLpNorm f 2 μ).toReal*(eLpNorm g 2 μ).toReal) := by
  have hc : eLpNorm (fun x => g (T^[n] x)) 2 μ=eLpNorm g 2 μ :=
    eLpNorm_comp_measurePreserving hg.aestronglyMeasurable (hT.iterate n)
  have hp := integral_mul_le_L2 hf (hg.comp_measurePreserving (hT.iterate n))
  change eLpNorm (g ∘ T^[n]) 2 μ=eLpNorm g 2 μ at hc
  rw [hc] at hp
  change |∫ x,f x*g (T^[n] x) ∂μ| ≤ (eLpNorm f 2 μ).toReal*(eLpNorm g 2 μ).toReal at hp
  have hfI := integral_le_L2 hf
  have hgI := integral_le_L2 hg
  have hprod := mul_le_mul hfI hgI (abs_nonneg _) ENNReal.toReal_nonneg
  have hh := abs_sub ((∫ x,f x*g (T^[n] x) ∂μ)) ((∫ x,f x ∂μ)*(∫ x,g x ∂μ))
  rw [abs_mul] at hh
  dsimp [realCorrelation]
  linarith

lemma realCorrelation_add_left (hf : MemLp f 2 μ) (hf₀ : MemLp f₀ 2 μ) (hg : MemLp g 2 μ) (n : ℕ) :
    realCorrelation T μ (f+f₀) g n=realCorrelation T μ f g n+realCorrelation T μ f₀ g n := by
  unfold realCorrelation
  simp only [Pi.add_apply,add_mul]
  rw [integral_add (integrable_mul_iterate hT hf hg n) (integrable_mul_iterate hT hf₀ hg n),
    integral_add (hf.integrable (by norm_num)) (hf₀.integrable (by norm_num))]
  ring

lemma realCorrelation_add_right (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hg₀ : MemLp g₀ 2 μ) (n : ℕ) :
    realCorrelation T μ f (g+g₀) n=realCorrelation T μ f g n+realCorrelation T μ f g₀ n := by
  unfold realCorrelation
  simp only [Pi.add_apply,mul_add]
  rw [integral_add (integrable_mul_iterate hT hf hg n) (integrable_mul_iterate hT hf hg₀ n),
    integral_add (hg.integrable (by norm_num)) (hg₀.integrable (by norm_num))]
  ring

lemma realCorrelation_sub_left (hf : MemLp f 2 μ) (hf₀ : MemLp f₀ 2 μ) (hg : MemLp g 2 μ) (n : ℕ) :
    realCorrelation T μ (f-f₀) g n=realCorrelation T μ f g n-realCorrelation T μ f₀ g n := by
  unfold realCorrelation
  simp only [Pi.sub_apply,sub_mul]
  rw [integral_sub (integrable_mul_iterate hT hf hg n) (integrable_mul_iterate hT hf₀ hg n),
    integral_sub (hf.integrable (by norm_num)) (hf₀.integrable (by norm_num))]
  ring

lemma realCorrelation_sub_right (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hg₀ : MemLp g₀ 2 μ) (n : ℕ) :
    realCorrelation T μ f (g-g₀) n=realCorrelation T μ f g n-realCorrelation T μ f g₀ n := by
  unfold realCorrelation
  simp only [Pi.sub_apply,mul_sub]
  rw [integral_sub (integrable_mul_iterate hT hf hg n) (integrable_mul_iterate hT hf hg₀ n),
    integral_sub (hg.integrable (by norm_num)) (hg₀.integrable (by norm_num))]
  ring

lemma realCorrelation_approximation (hf : MemLp f 2 μ) (hf₀ : MemLp f₀ 2 μ)
    (hg : MemLp g 2 μ) (hg₀ : MemLp g₀ 2 μ) (n : ℕ) :
    |realCorrelation T μ f g n-realCorrelation T μ f₀ g₀ n|≤
      2*((eLpNorm (f-f₀) 2 μ).toReal*(eLpNorm g 2 μ).toReal+
        (eLpNorm f₀ 2 μ).toReal*(eLpNorm (g-g₀) 2 μ).toReal) := by
  have heq : realCorrelation T μ f g n-realCorrelation T μ f₀ g₀ n=
      realCorrelation T μ (f-f₀) g n+realCorrelation T μ f₀ (g-g₀) n := by
    rw [realCorrelation_sub_left hT hf hf₀ hg,realCorrelation_sub_right hT hf₀ hg hg₀]
    ring
  rw [heq]
  have hh := abs_add_le (realCorrelation T μ (f-f₀) g n) (realCorrelation T μ f₀ (g-g₀) n)
  have h₁ := realCorrelation_bound hT (hf.sub hf₀) hg n
  have h₂ := realCorrelation_bound hT hf₀ (hg.sub hg₀) n
  linarith

end CorrelationBounds

lemma indicator_correlation_tendsto {A : Type*} [MeasurableSpace A] {μ : Measure A} [IsProbabilityMeasure μ]
    {T : A → A} (hT : Measurable T) (hmix : StrongMixing T μ)
    (s t : Set A) (hs : MeasurableSet s) (ht : MeasurableSet t) (c d : ℝ) :
    Tendsto (fun n : ℕ => realCorrelation T μ (s.indicator (fun _ => c)) (t.indicator (fun _ => d)) n)
      atTop (𝓝 0) := by
  have hset : Tendsto (fun n : ℕ => μ.real ((T^[n]) ⁻¹' t ∩ s)) atTop (𝓝 (μ.real t*μ.real s)) := by
    simpa only [Measure.real,ENNReal.toReal_mul] using
      (ENNReal.tendsto_toReal (by finiteness : μ t*μ s≠∞)).comp (hmix t s ht hs)
  have heq (n : ℕ) : realCorrelation T μ (s.indicator (fun _ => c)) (t.indicator (fun _ => d)) n=
      c*d*(μ.real ((T^[n]) ⁻¹' t ∩ s)-μ.real t*μ.real s) := by
    unfold realCorrelation
    have hfunc : (fun x => s.indicator (fun _ => c) x*t.indicator (fun _ => d) (T^[n] x))=
        ((T^[n]) ⁻¹' t ∩ s).indicator (fun _ => c*d) := by
      funext x
      by_cases hxS : x∈s <;> by_cases hxT : T^[n] x∈t <;> simp [hxS,hxT]
    rw [hfunc,integral_indicator (((hT.iterate n) ht).inter hs),setIntegral_const,
      integral_indicator hs,setIntegral_const,integral_indicator ht,setIntegral_const]
    simp only [smul_eq_mul]
    ring
  apply (tendsto_congr heq).mpr
  simpa only [sub_self,mul_zero] using (hset.sub_const (μ.real t*μ.real s)).const_mul (c*d)

lemma simple_correlation_tendsto {A : Type*} [MeasurableSpace A] {μ : Measure A} [IsProbabilityMeasure μ]
    {T : A → A} (hT : MeasurePreserving T μ μ) (hmix : StrongMixing T μ) (f g : SimpleFunc A ℝ) :
    Tendsto (fun n : ℕ => realCorrelation T μ f g n) atTop (𝓝 0) := by
  refine (SimpleFunc.induction (motive := fun f : SimpleFunc A ℝ => ∀ g : SimpleFunc A ℝ,
    Tendsto (fun n : ℕ => realCorrelation T μ f g n) atTop (𝓝 0)) ?_ ?_ f) g
  · intro c s hs g
    refine SimpleFunc.induction (motive := fun g : SimpleFunc A ℝ =>
      Tendsto (fun n : ℕ => realCorrelation T μ
        (SimpleFunc.piecewise s hs (SimpleFunc.const A c) (SimpleFunc.const A 0)) g n) atTop (𝓝 0)) ?_ ?_ g
    · intro d t ht
      simpa only [SimpleFunc.coe_piecewise,SimpleFunc.coe_const,piecewise_eq_indicator] using
        indicator_correlation_tendsto hT.measurable hmix s t hs ht c d
    · intro g₁ g₂ hdis h₁ h₂
      have hh := h₁.add h₂
      have heq (n : ℕ) : realCorrelation T μ
          (SimpleFunc.piecewise s hs (SimpleFunc.const A c) (SimpleFunc.const A 0)) (g₁+g₂) n=
          realCorrelation T μ (SimpleFunc.piecewise s hs (SimpleFunc.const A c) (SimpleFunc.const A 0)) g₁ n+
          realCorrelation T μ (SimpleFunc.piecewise s hs (SimpleFunc.const A c) (SimpleFunc.const A 0)) g₂ n :=
        realCorrelation_add_right hT (SimpleFunc.memLp_of_isFiniteMeasure _ _ _)
          (SimpleFunc.memLp_of_isFiniteMeasure _ _ _) (SimpleFunc.memLp_of_isFiniteMeasure _ _ _) n
      apply (tendsto_congr heq).mpr
      simpa only [add_zero] using hh
  · intro f₁ f₂ hdis h₁ h₂ g
    have hh := (h₁ g).add (h₂ g)
    have heq (n : ℕ) : realCorrelation T μ (f₁+f₂) g n=
        realCorrelation T μ f₁ g n+realCorrelation T μ f₂ g n :=
      realCorrelation_add_left hT (SimpleFunc.memLp_of_isFiniteMeasure _ _ _)
        (SimpleFunc.memLp_of_isFiniteMeasure _ _ _) (SimpleFunc.memLp_of_isFiniteMeasure _ _ _) n
    apply (tendsto_congr heq).mpr
    simpa only [add_zero] using hh

/-- Set mixing gives every real L2 correlation, by genuine simple-function L2 approximation. -/
theorem strongMixingL2_of_strongMixing {A : Type*} [MeasurableSpace A] {μ : Measure A} [IsProbabilityMeasure μ]
    {T : A → A} (hT : MeasurePreserving T μ μ) (hmix : StrongMixing T μ) : StrongMixingL2 T μ := by
  intro f g hf hg
  have hc : Tendsto (fun n : ℕ => realCorrelation T μ f g n) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    let G := (eLpNorm g 2 μ).toReal
    let δ := ε/(16*(G+1))
    have hG : 0≤G := ENNReal.toReal_nonneg
    have hδ : 0<δ := by dsimp [δ]; positivity
    obtain ⟨f₀,hferr,hf₀⟩ := hf.exists_simpleFunc_eLpNorm_sub_lt (by norm_num) (ENNReal.ofReal_ne_zero_iff.mpr hδ)
    have hfe : (eLpNorm (f-⇑f₀) 2 μ).toReal≤δ :=
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top hferr.le).trans_eq (ENNReal.toReal_ofReal hδ.le)
    let F := (eLpNorm f₀ 2 μ).toReal
    let ζ := ε/(16*(F+1))
    have hF : 0≤F := ENNReal.toReal_nonneg
    have hζ : 0<ζ := by dsimp [ζ]; positivity
    obtain ⟨g₀,hgerr,hg₀⟩ := hg.exists_simpleFunc_eLpNorm_sub_lt (by norm_num) (ENNReal.ofReal_ne_zero_iff.mpr hζ)
    have hge : (eLpNorm (g-⇑g₀) 2 μ).toReal≤ζ :=
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top hgerr.le).trans_eq (ENNReal.toReal_ofReal hζ.le)
    have hidδ : (16*(G+1))*δ=ε := mul_div_cancel₀ _ (by positivity)
    have hidζ : (16*(F+1))*ζ=ε := mul_div_cancel₀ _ (by positivity)
    have hterm₁ : (eLpNorm (f-⇑f₀) 2 μ).toReal*G≤ε/16 := by
      have hh := mul_le_mul_of_nonneg_right hfe hG
      nlinarith
    have hterm₂ : F*(eLpNorm (g-⇑g₀) 2 μ).toReal≤ε/16 := by
      have hh := mul_le_mul_of_nonneg_left hge hF
      nlinarith
    have herr (n : ℕ) : |realCorrelation T μ f g n-realCorrelation T μ f₀ g₀ n|≤ε/4 :=
      (realCorrelation_approximation hT hf hf₀ hg hg₀ n).trans (by
        change 2*((eLpNorm (f-⇑f₀) 2 μ).toReal*G+F*(eLpNorm (g-⇑g₀) 2 μ).toReal)≤ε/4
        linarith)
    obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (simple_correlation_tendsto hT hmix f₀ g₀) (ε/2) (by positivity)
    refine ⟨N,fun n hn => ?_⟩
    have hsmall : |realCorrelation T μ f₀ g₀ n|<ε/2 := by
      simpa only [Real.dist_eq,sub_zero] using hN n hn
    rw [Real.dist_eq,sub_zero]
    have htri : |realCorrelation T μ f g n|≤
        |realCorrelation T μ f g n-realCorrelation T μ f₀ g₀ n|+|realCorrelation T μ f₀ g₀ n| := by
      have hh := abs_add_le (realCorrelation T μ f g n-realCorrelation T μ f₀ g₀ n)
        (realCorrelation T μ f₀ g₀ n)
      simpa only [sub_add_cancel] using hh
    linarith [herr n]
  have ht := hc.add_const ((∫ x,f x ∂μ)*(∫ x,g x ∂μ))
  simpa only [realCorrelation,sub_add_cancel,zero_add] using ht

/-- The complete set/L2 formulation equivalence in the original introduction. -/
theorem strongMixing_iff_L2 {A : Type*} [MeasurableSpace A] {μ : Measure A} [IsProbabilityMeasure μ]
    {T : A → A} (hT : MeasurePreserving T μ μ) : StrongMixing T μ↔StrongMixingL2 T μ :=
  ⟨strongMixingL2_of_strongMixing hT,strongMixing_of_L2 hT.measurable⟩

end
end Paper14
