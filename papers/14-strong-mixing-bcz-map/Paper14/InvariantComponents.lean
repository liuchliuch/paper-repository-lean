import Paper14.GraphDecomposition
import Mathlib.Dynamics.Ergodic.Extreme

/-! The product-identification steps in the proof of Theorem 4, (10)--(11). -/
open MeasureTheory Measure Set Function
open scoped ENNReal
namespace Paper14
noncomputable section

/-- The scalar in an invariant absolutely continuous measure is its mass,
when the reference measure is a probability measure. -/
theorem invariant_ac_eq_mass_smul {α : Type*} [MeasurableSpace α]
    {T : α → α} {μ ν : Measure α} [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    (hT : Ergodic T μ) (hν : MeasurePreserving T ν ν) (hac : ν ≪ μ) :
    ν = ν univ • μ := by
  obtain ⟨c, hc⟩ := hT.eq_smul_of_absolutelyContinuous hν hac
  have hmass : ν univ = c := by rw [hc]; simp
  rw [hmass]
  exact hc

/-- A finite measure with equal scalar marginals and invariance under
`id × T` is a product, provided `T` is ergodic. This proves the product claim
for the intermediate measure in paper S3.p9. -/
theorem product_of_second_invariant {α : Type*} [MeasurableSpace α]
    {T : α → α} {μ : Measure α} [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (F : Measure (α × α)) [IsFiniteMeasure F]
    {γ : ℝ≥0∞} (hfst : F.fst = γ • μ) (hsnd : F.snd = γ • μ)
    (hF : Measure.map (fun p : α × α => (p.1, T p.2)) F = F) :
    F = γ • μ.prod μ := by
  let W : α × α → α × α := fun p => (p.1, T p.2)
  have hW : Measurable W := measurable_fst.prodMk (hT.measurable.comp measurable_snd)
  have hWmp : MeasurePreserving W F F := ⟨hW, hF⟩
  apply Measure.ext_prod
  intro A C hA hC
  let S : Set (α × α) := Prod.fst ⁻¹' A
  let η : Measure α := Measure.map Prod.snd (F.restrict S)
  have hS : MeasurableSet S := measurable_fst hA
  have hSpre : W ⁻¹' S = S := rfl
  have hSW : MeasurePreserving W (F.restrict S) (F.restrict S) := by
    simpa only [hSpre] using hWmp.restrict_preimage hS
  have hη : MeasurePreserving T η η := by
    refine ⟨hT.measurable, ?_⟩
    change Measure.map T (Measure.map Prod.snd (F.restrict S)) = _
    rw [Measure.map_map hT.measurable measurable_snd]
    have heq : T ∘ Prod.snd = Prod.snd ∘ W := rfl
    rw [heq, ← Measure.map_map measurable_snd hW, hSW.map_eq]
  have hηle : η ≤ γ • μ := by
    rw [← hsnd]
    exact Measure.map_mono Measure.restrict_le_self measurable_snd
  have hηac : η ≪ μ :=
    (Measure.absolutelyContinuous_of_le hηle).trans Measure.smul_absolutelyContinuous
  have hηeq := invariant_ac_eq_mass_smul hT hη hηac
  have hmass : η univ = γ * μ A := by
    simp only [η, Measure.map_apply measurable_snd MeasurableSet.univ,
      preimage_univ, Measure.restrict_apply_univ]
    rw [← Measure.fst_apply (ρ := F) hA, hfst, Measure.smul_apply, smul_eq_mul]
  have hrect : F (A ×ˢ C) = η C := by
    change F (A ×ˢ C) = Measure.map Prod.snd (F.restrict S) C
    rw [Measure.map_apply measurable_snd hC, Measure.restrict_apply (measurable_snd hC)]
    congr 1
    ext p
    simp only [S, mem_inter_iff, mem_preimage, mem_prod, and_comm]
  rw [hrect, hηeq, Measure.smul_apply, hmass, smul_eq_mul,
    Measure.smul_apply, Measure.prod_prod, smul_eq_mul, mul_assoc]

/-- The density argument in (11) for any invariant component dominated by
the intermediate product measure. -/
theorem dominated_product_component {α : Type*} [MeasurableSpace α]
    {T : α → α} {μ : Measure α} [IsProbabilityMeasure μ]
    (hweak : WeakMixing T μ) (ν : Measure (α × α)) [IsFiniteMeasure ν]
    (hν : MeasurePreserving (fun p : α × α => (T p.1, T p.2)) ν ν)
    {γ : ℝ≥0∞} (hdom : ν ≤ γ • μ.prod μ) :
    ν = ν univ • μ.prod μ := by
  apply invariant_ac_eq_mass_smul hweak.2 hν
  exact (Measure.absolutelyContinuous_of_le hdom).trans Measure.smul_absolutelyContinuous

/-- Every positive-excess component is dominated by the intermediate measure
because the summand with intermediate shift zero occurs in (10). -/
lemma component_le_intermediate {α : Type*} [MeasurableSpace α]
    (W : α → α) (ν : ℕ → Measure α) {j : ℕ} (hj : 0 < j) :
    ν j ≤ intermediateMeasure W ν := by
  have hterm : ν j ≤ ∑ k ∈ Finset.range j, Measure.map (W^[k]) (ν j) := by
    apply Measure.le_iff.mpr
    intro s hs
    rw [Measure.finset_sum_apply]
    calc
      ν j s = Measure.map (W^[0]) (ν j) s := by simp
      _ ≤ ∑ k ∈ Finset.range j, Measure.map (W^[k]) (ν j) s :=
        Finset.single_le_sum (f := fun k : ℕ => Measure.map (W^[k]) (ν j) s)
          (fun k _ => zero_le _) (Finset.mem_range.mpr hj)
  exact hterm.trans (Measure.le_sum (fun i => ∑ k ∈ Finset.range i,
    Measure.map (W^[k]) (ν i)) j)

/-- The algebraic-measure core of (9)--(11), once the limiting components
and their marginal bounds have been constructed. This is explicitly a
conditional core lemma, not the compactness/limit construction of Theorem 4. -/
theorem positive_components_of_decomposition {α : Type*} [MeasurableSpace α]
    {T : α → α} {μ : Measure α} [IsProbabilityMeasure μ]
    (hweak : WeakMixing T μ) (ν : ℕ → Measure (α × α))
    [IsFiniteMeasure (Measure.sum ν)]
    (hdecomp : Measure.sum ν = Measure.sum (fun j =>
      Measure.map ((fun p : α × α => (p.1, T p.2))^[j]) (ν j)))
    (hmoment : (∑' j : ℕ, (j : ℝ≥0∞) * ν j univ) < ⊤)
    {γ : ℝ≥0∞}
    (hfst : (intermediateMeasure (fun p : α × α => (p.1, T p.2)) ν).fst = γ • μ)
    (hsnd : (intermediateMeasure (fun p : α × α => (p.1, T p.2)) ν).snd = γ • μ)
    (hV : ∀ j, MeasurePreserving (fun p : α × α => (T p.1, T p.2)) (ν j) (ν j)) :
    ∀ j : ℕ, 0 < j → ν j = ν j univ • μ.prod μ := by
  let W : α × α → α × α := fun p => (p.1, T p.2)
  have hW : Measurable W := measurable_fst.prodMk (hweak.1.measurable.comp measurable_snd)
  have hT : Ergodic T μ := ⟨hweak.1,
    (measurePreserving_fst (μ := μ) (ν := μ)).preErgodic_of_preErgodic_conjugate
      hweak.2.toPreErgodic (fun p => rfl)⟩
  let F := intermediateMeasure W ν
  haveI : IsFiniteMeasure F := ⟨by
    rw [show F univ = ∑' j : ℕ, (j : ℝ≥0∞) * ν j univ from intermediateMeasure_mass W hW ν]
    exact hmoment⟩
  have hprod : F = γ • μ.prod μ :=
    product_of_second_invariant hT F hfst hsnd (intermediateMeasure_invariant W hW ν hdecomp)
  intro j hj
  have hdom : ν j ≤ F := component_le_intermediate W ν hj
  haveI : IsFiniteMeasure (ν j) := isFiniteMeasure_of_le _ hdom
  exact dominated_product_component hweak (ν j) (hV j) (hprod ▸ hdom)

end
end Paper14
