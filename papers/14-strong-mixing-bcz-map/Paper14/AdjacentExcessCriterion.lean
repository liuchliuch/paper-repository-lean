import Paper14.ExcessMarginalLimits
import Paper14.DominatedProductLimits
import Paper14.ProductInducedError
import Paper14.LevelPairError

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal
namespace Paper14
noncomputable section

/-- Positive adjacent excess levels imply weak mixing, using only ergodicity,
actual self-induction, and near-identity maps. -/
theorem weakMixing_of_adjacent_excess_levels {E : Type*} [MeasurableSpace E] [MetricSpace E]
    [CompactSpace E] [BorelSpace E] [Nonempty E] {μ : Measure E} [IsProbabilityMeasure μ]
    {T : E → E} (hT : Ergodic T μ) (Y : ℕ → Set E) (φ : ℕ → E → E)
    (hY : ∀ n,MeasurableSet (Y n)) (hp : ∀ n,0<μ (Y n))
    (hφ : ∀ n,MeasurePreserving (φ n) μ (normalizedRestriction μ (Y n)))
    (hc : ∀ n,∀ᵐ x ∂μ,inducedMap T (Y n) (φ n x)=φ n (T x))
    (hpoint : ∀ᵐ x ∂μ,Tendsto (fun n => φ n x) atTop (𝓝 x))
    (hρ : Tendsto (fun n => μ.real (Y n)) atTop (𝓝 1))
    (B : ℝ≥0) (hrec : ∀ n,(μ (Y n))⁻¹≤(B : ℝ≥0∞)) (a : ℕ → ℕ)
    (c₀ c₁ : ℝ≥0) (hc₀ : 0<c₀) (hc₁ : 0<c₁)
    (hlower₀ : ∀ n,c₀≤(excessGraphFinite T μ (Y n) (a n) 0).mass)
    (hlower₁ : ∀ n,c₁≤(excessGraphFinite T μ (Y n) (a n) 1).mass) : WeakMixing T μ := by
  classical
  have hdom (n : ℕ) : normalizedRestriction μ (Y n)≤B • μ := by
    rw [normalizedRestriction]
    apply Measure.le_iff.mpr
    intro A hA
    simp only [Measure.smul_apply,ENNReal.smul_def,smul_eq_mul]
    exact (mul_le_mul_left' (Measure.restrict_le_self A) _).trans (mul_le_mul_right' (hrec n) _)
  have hB₁ : (1 : ℝ≥0)≤B := by
    letI := normalizedRestriction_probability (hp 0).ne'
    have hh := hdom 0 univ
    apply ENNReal.coe_le_coe.mp
    simpa only [ENNReal.coe_one,measure_univ,Measure.smul_apply,ENNReal.smul_def,smul_eq_mul,mul_one] using hh
  let c : ℕ → ℝ≥0 := fun j => if j=0 then c₀ else if j=1 then c₁ else 0
  have hlow (n j : ℕ) : c j≤(excessGraphFinite T μ (Y n) (a n) j).mass := by
    by_cases hj0 : j=0
    · simpa [c,hj0] using hlower₀ n
    · by_cases hj1 : j=1
      · simpa [c,hj1] using hlower₁ n
      · simp [c,hj0,hj1]
  obtain ⟨γ,s,hs,hγ,hlim⟩ := excessMarginal_scalar_subsequence hT Y φ hY hp hφ hc hρ B hrec a c hlow
  let L : ℕ → FiniteMeasure E := fun j => ⟨γ j • μ,inferInstance⟩
  have hLdom (j : ℕ) : (L j : Measure E)≤B • μ := by
    apply Measure.le_iff.mpr
    intro A hA
    change (γ j • μ) A≤(B • μ) A
    simp only [Measure.smul_apply,ENNReal.smul_def,smul_eq_mul]
    exact mul_le_mul_right' (ENNReal.coe_le_coe.mpr ((hγ j).2.trans hB₁)) _
  let M : ℕ → ℕ → FiniteMeasure E := fun n j => excessMarginalFinite T μ (Y (s n)) (a (s n)) j
  have hMdom (n j : ℕ) : (M n j : Measure E)≤B • μ := by
    rw [show (M n j : Measure E)=(normalizedRestriction μ (Y (s n))).restrict
      (excessLevel T (Y (s n)) (a (s n)) j) from excessMarginalFinite_coe hT.measurable μ _ _ _]
    exact Measure.restrict_le_self.trans (hdom (s n))
  have hprod := dominated_finiteMeasure_prod_tendsto (hlim 0) (hlim 1) B
    (fun n => hMdom n 0) (fun n => hMdom n 1) (hLdom 0) (hLdom 1)
  refine ⟨hT.toMeasurePreserving,⟨hT.toMeasurePreserving.prod hT.toMeasurePreserving,⟨?_⟩⟩⟩
  intro A hA hAinv
  let F : E × E → ℝ := A.indicator (fun _ => 1)
  let W : E × E → E × E := fun p => (p.1,T p.2)
  let H : E × E → ℝ := fun p => ‖F (W p)-F p‖
  have hF : Measurable F := measurable_const.indicator hA
  have hFb (p : E × E) : ‖F p‖≤1 := by by_cases hp : p∈A <;> simp [F,hp]
  have hinv (p : E × E) : F (T p.1,T p.2)=F p := by
    have heq : (T p.1,T p.2)∈A ↔ p∈A := by
      change p∈(fun q : E × E => (T q.1,T q.2)) ⁻¹' A ↔ p∈A
      rw [hAinv]
    simp only [F,indicator_apply,heq]
  have hW : MeasurePreserving W (μ.prod μ) (μ.prod μ) := (MeasurePreserving.id μ).prod hT.toMeasurePreserving
  have hH : Measurable H := ((hF.comp hW.measurable).sub hF).norm
  have hHb (p : E × E) : ‖H p‖≤2 := by
    change ‖‖F (W p)-F p‖‖≤2
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (by nlinarith [hFb (W p),hFb p])
  have hHt := weak_limit_bounded_measurable hprod (B*B)
    (fun n => product_domination (hMdom n 0) (hMdom n 1)) (product_domination (hLdom 0) (hLdom 1)) hH 2 hHb
  have hDt := product_induced_invariant_error hT.toMeasurePreserving Y φ hY hφ hc hpoint B hdom a hF hFb hinv
  have hH0 : Tendsto (fun n => ∫ p,H p ∂((M n 0).prod (M n 1) : Measure (E × E))) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hDt.comp hs.tendsto_atTop)
      (fun n => integral_nonneg (fun p => norm_nonneg _))
    intro n
    exact level01_product_integral_le hT.toMeasurePreserving (hY (s n)) (hp (s n)) (hφ (s n))
      (hc (s n)) (a (s n)) hF hFb hinv
  have hz : (∫ p,H p ∂((L 0).prod (L 1) : Measure (E × E)))=0 := tendsto_nhds_unique hHt hH0
  have hPL : ((L 0).prod (L 1) : Measure (E × E))=(γ 0*γ 1) • μ.prod μ := by
    change (γ 0 • μ).prod (γ 1 • μ)=_
    simp only [ENNReal.smul_def,Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,ENNReal.coe_mul,mul_comm]
  rw [hPL,integral_smul_nnreal_measure] at hz
  have hγ₀ : (0 : ℝ)<γ 0 := by
    exact_mod_cast (lt_of_lt_of_le hc₀ (by simpa [c] using (hγ 0).1))
  have hγ₁ : (0 : ℝ)<γ 1 := by
    exact_mod_cast (lt_of_lt_of_le hc₁ (by simpa [c] using (hγ 1).1))
  have hHzero : (∫ p,H p ∂μ.prod μ)=0 := by
    have hh : ((γ 0 : ℝ)*(γ 1 : ℝ))*(∫ p,H p ∂μ.prod μ)=0 := by simpa only [NNReal.coe_mul,smul_eq_mul] using hz
    exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero hγ₀.ne' hγ₁.ne')
  have hAEH := (integral_eq_zero_iff_of_nonneg (fun p => norm_nonneg (F (W p)-F p))
    (integrable_of_measurable_bound hH 2 hHb)).mp hHzero
  have hset : W ⁻¹' A=ᵐ[μ.prod μ] A := by
    filter_upwards [hAEH] with p hp
    have hh : F (W p)=F p := sub_eq_zero.mp (norm_eq_zero.mp hp)
    apply propext
    change W p∈A ↔ p∈A
    by_cases h₁ : W p∈A <;> by_cases h₂ : p∈A <;> simp_all [F]
  let ν := (μ.prod μ).restrict A
  have hνV : MeasurePreserving (Prod.map T T) ν ν := by
    have hh := (hT.toMeasurePreserving.prod hT.toMeasurePreserving).restrict_preimage hA
    have hpre : Prod.map T T ⁻¹' A=A := hAinv
    rw [hpre] at hh
    exact hh
  have hνW : MeasurePreserving W ν ν := by
    have hh := hW.restrict_preimage hA
    rw [Measure.restrict_congr_set hset] at hh
    exact hh
  have hfstd : ν.fst≤μ := by
    have hh := Measure.fst_mono (show ν≤μ.prod μ from Measure.restrict_le_self)
    simpa only [Measure.fst,Measure.map_fst_prod,measure_univ,one_smul] using hh
  have hsndd : ν.snd≤μ := by
    have hh := Measure.snd_mono (show ν≤μ.prod μ from Measure.restrict_le_self)
    simpa only [Measure.snd,Measure.map_snd_prod,measure_univ,one_smul] using hh
  obtain ⟨hfst,hsnd⟩ := invariant_component_marginals hT ν hνV hfstd hsndd
  have hνeq := product_of_second_invariant hT ν hfst hsnd hνW.map_eq
  have hzero := congrArg (fun ρ : Measure (E × E) => ρ Aᶜ) hνeq
  change (μ.prod μ).restrict A Aᶜ=ν univ*(μ.prod μ) Aᶜ at hzero
  rw [Measure.restrict_apply hA.compl,compl_inter_self,measure_empty] at hzero
  have hzeroOr : (μ.prod μ) A=0 ∨ (μ.prod μ) Aᶜ=0 := by
    simpa only [ν,Measure.restrict_apply_univ] using mul_eq_zero.mp hzero.symm
  apply eventuallyConst_set'.mpr
  simpa using hzeroOr

end
end Paper14
