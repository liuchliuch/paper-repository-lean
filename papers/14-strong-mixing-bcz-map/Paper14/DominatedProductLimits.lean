import Paper14.DominatedWeakLimits
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal BoundedContinuousFunction
namespace Paper14
noncomputable section

lemma measure_prod_mono {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {μ μ' : Measure E} {ν ν' : Measure F} [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (hμ : μ≤μ') (hν : ν≤ν') : μ.prod ν≤μ'.prod ν' := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.prod_apply hS,Measure.prod_apply hS]
  exact (lintegral_mono (fun x => hν _)).trans (lintegral_mono' hμ le_rfl)

lemma product_domination {E : Type*} [MeasurableSpace E] {μ ν ζ : Measure E}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ζ] {C : ℝ≥0}
    (hν : ν≤C • μ) (hζ : ζ≤C • μ) : ν.prod ζ≤(C*C) • μ.prod μ := by
  have hh := measure_prod_mono hν hζ
  simpa only [ENNReal.smul_def,Measure.prod_smul_left,Measure.prod_smul_right,
    smul_smul,ENNReal.coe_mul] using hh

lemma product_domination_marginals {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
    {ν : Measure (E × E)} {D : ℝ≥0} (hν : ν≤D • μ.prod μ) : ν.fst≤D • μ ∧ ν.snd≤D • μ := by
  constructor
  · have hh := Measure.fst_mono hν
    change Measure.map Prod.fst ν≤Measure.map Prod.fst (D • μ.prod μ) at hh
    simpa only [Measure.map_smul,Measure.map_fst_prod,measure_univ,one_smul] using hh
  · have hh := Measure.snd_mono hν
    change Measure.map Prod.snd ν≤Measure.map Prod.snd (D • μ.prod μ) at hh
    simpa only [Measure.map_smul,Measure.map_snd_prod,measure_univ,one_smul] using hh

/-- Products of uniformly dominated finite measures preserve simultaneous weak limits. -/
theorem dominated_finiteMeasure_prod_tendsto {E : Type*} [MeasurableSpace E] [MetricSpace E]
    [CompactSpace E] [BorelSpace E] [Nonempty E] {μ : Measure E} [IsProbabilityMeasure μ]
    {νn ζn : ℕ → FiniteMeasure E} {ν ζ : FiniteMeasure E}
    (hν : Tendsto νn atTop (𝓝 ν)) (hζ : Tendsto ζn atTop (𝓝 ζ))
    (C : ℝ≥0) (hνn : ∀ n,(νn n : Measure E)≤C • μ) (hζn : ∀ n,(ζn n : Measure E)≤C • μ)
    (hνd : (ν : Measure E)≤C • μ) (hζd : (ζ : Measure E)≤C • μ) :
    Tendsto (fun n => (νn n).prod (ζn n)) atTop (𝓝 (ν.prod ζ)) := by
  let P := ν.prod ζ
  have hPd : (P : Measure (E × E))≤(C*C) • μ.prod μ := product_domination hνd hζd
  have hd (n : ℕ) : ((νn n).prod (ζn n) : Measure (E × E))≤(C*C) • μ.prod μ :=
    product_domination (hνn n) (hζn n)
  have hmass (n : ℕ) : ((νn n).prod (ζn n)).mass≤C*C := by
    apply ENNReal.coe_le_coe.mp
    rw [FiniteMeasure.ennreal_mass]
    simpa only [Measure.smul_apply,ENNReal.smul_def,smul_eq_mul,Measure.prod_prod,measure_univ,mul_one] using hd n univ
  apply tendsto_of_subseq_tendsto
  intro a ha
  obtain ⟨θ,s,hs,hθ,_⟩ := finiteMeasure_simultaneous_subsequence
    (fun n (_ : Unit) => (νn (a n)).prod (ζn (a n))) (C*C) (fun n _ => hmass (a n))
  have hθdom : (θ () : Measure (E × E))≤(C*C) • μ.prod μ := by
    let R : FiniteMeasure (E × E) := ⟨(C*C) • μ.prod μ,inferInstance⟩
    exact finiteMeasure_le_of_tendsto (show Tendsto (fun _ : ℕ => R) atTop (𝓝 R) from tendsto_const_nhds)
      (hθ ()) R.mass (fun _ => le_rfl) (fun n => hd (a (s n)))
  have hθeq : θ ()=P := by
    obtain ⟨hθf,hθg⟩ := product_domination_marginals hθdom
    obtain ⟨hPf,hPg⟩ := product_domination_marginals hPd
    apply finiteMeasure_eq_of_continuous_products (θ ()) P (C*C) hθf hθg hPf hPg
    intro f g
    let F : (E × E) →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨fun z => f z.1*g z.2,by fun_prop⟩
    have hleft := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp (hθ ()) F
    change Tendsto (fun k => ∫ z,f z.1*g z.2 ∂((νn (a (s k))).prod (ζn (a (s k))) : Measure (E × E)))
      atTop (𝓝 (∫ z,f z.1*g z.2 ∂(θ () : Measure (E × E)))) at hleft
    have hnν := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp
      (hν.comp (ha.comp hs.tendsto_atTop)) f
    have hnζ := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp
      (hζ.comp (ha.comp hs.tendsto_atTop)) g
    have hright : Tendsto (fun k => ∫ z,f z.1*g z.2 ∂((νn (a (s k))).prod (ζn (a (s k))) : Measure (E × E)))
        atTop (𝓝 (∫ z,f z.1*g z.2 ∂(P : Measure (E × E)))) := by
      simpa only [P,FiniteMeasure.toMeasure_prod,integral_prod_mul,Function.comp_apply] using hnν.mul hnζ
    exact tendsto_nhds_unique hleft hright
  refine ⟨s,?_⟩
  simpa only [hθeq] using hθ ()

end
end Paper14
