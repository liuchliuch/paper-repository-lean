import Paper14.MeasureSubsequence
import Mathlib.MeasureTheory.Measure.Sub

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
namespace Paper14
noncomputable section

lemma finiteMeasure_coe_sum {E ι : Type*} [MeasurableSpace E]
    (s : Finset ι) (ν : ι → FiniteMeasure E) :
    ((∑ j ∈ s, ν j : FiniteMeasure E) : Measure E) = ∑ j ∈ s, (ν j : Measure E) :=
  map_sum FiniteMeasure.toMeasureAddMonoidHom ν s

lemma finiteMeasure_tendsto_add {E ι : Type*} [MeasurableSpace E]
    [TopologicalSpace E] [OpensMeasurableSpace E] {l : Filter ι}
    {μn νn : ι → FiniteMeasure E} {μ ν : FiniteMeasure E}
    (hμ : Tendsto μn l (𝓝 μ)) (hν : Tendsto νn l (𝓝 ν)) :
    Tendsto (fun n => μn n + νn n) l (𝓝 (μ + ν)) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  have hm := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hμ f
  have hn := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hν f
  simpa only [FiniteMeasure.toMeasure_add,integral_add_measure (f.integrable _) (f.integrable _)] using hm.add hn

lemma finiteMeasure_tendsto_smul {E ι : Type*} [MeasurableSpace E]
    [TopologicalSpace E] [OpensMeasurableSpace E] {l : Filter ι}
    {cn : ι → ℝ≥0} {c : ℝ≥0} {νn : ι → FiniteMeasure E} {ν : FiniteMeasure E}
    (hc : Tendsto cn l (𝓝 c)) (hν : Tendsto νn l (𝓝 ν)) :
    Tendsto (fun n => cn n • νn n) l (𝓝 (c • ν)) := by
  rw [FiniteMeasure.tendsto_iff_forall_testAgainstNN_tendsto]
  intro f
  simp only [FiniteMeasure.smul_testAgainstNN_apply,smul_eq_mul]
  exact hc.mul ((FiniteMeasure.tendsto_iff_forall_testAgainstNN_tendsto.mp hν) f)

/-- Domination passes to simultaneous weak limits on a compact metric
space. The difference measures are compactly extracted, avoiding any
continuity assumption on measurable indicator functions. -/
theorem finiteMeasure_le_of_tendsto {E : Type*} [MeasurableSpace E]
    [MetricSpace E] [CompactSpace E] [BorelSpace E] [Nonempty E]
    {μn νn : ℕ → FiniteMeasure E} {μ ν : FiniteMeasure E}
    (hμ : Tendsto μn atTop (𝓝 μ)) (hν : Tendsto νn atTop (𝓝 ν))
    (C : ℝ≥0) (hbound : ∀ n, (μn n).mass ≤ C)
    (hle : ∀ n, (νn n : Measure E) ≤ μn n) : (ν : Measure E) ≤ μ := by
  let d : ℕ → Unit → FiniteMeasure E := fun n _ =>
    ⟨(μn n : Measure E) - νn n, inferInstance⟩
  have hd : ∀ n j, (d n j).mass ≤ C := by
    intro n j
    apply le_trans ?_ (hbound n)
    apply ENNReal.coe_le_coe.mp
    simpa only [FiniteMeasure.ennreal_mass] using
      (show ((d n j : FiniteMeasure E) : Measure E) univ ≤ (μn n : Measure E) univ from Measure.sub_le univ)
  obtain ⟨δ,s,hs,hδ,_⟩ := finiteMeasure_simultaneous_subsequence d C hd
  have heq (n : ℕ) : d n () + νn n = μn n := by
    apply FiniteMeasure.toMeasure_injective
    exact Measure.sub_add_cancel_of_le (hle n)
  have hsum := finiteMeasure_tendsto_add (hδ ()) (hν.comp hs.tendsto_atTop)
  have hμs := hμ.comp hs.tendsto_atTop
  have heqsum : δ () + ν = μ := by
    apply tendsto_nhds_unique hsum
    simpa only [Function.comp_apply,heq] using hμs
  rw [← heqsum,FiniteMeasure.toMeasure_add]
  apply Measure.le_iff.mpr
  intro A hA
  exact le_add_of_nonneg_left (zero_le _)

lemma finiteMeasure_tendsto_sum {E ι : Type*} [MeasurableSpace E]
    [TopologicalSpace E] [OpensMeasurableSpace E] {νn : ℕ → ι → FiniteMeasure E}
    {ν : ι → FiniteMeasure E} (hν : ∀ j, Tendsto (fun n => νn n j) atTop (𝓝 (ν j)))
    (s : Finset ι) : Tendsto (fun n => ∑ j ∈ s, νn n j) atTop (𝓝 (∑ j ∈ s, ν j)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : FiniteMeasure E)) atTop (𝓝 0))
  | @insert j s hj ih => simpa only [Finset.sum_insert hj] using finiteMeasure_tendsto_add (hν j) ih

/-- Uniform control of the mass in the tails permits passage from all
finite-time decompositions to the full infinite limiting decomposition. -/
theorem measure_sum_eq_of_weak_limits_and_tail {E : Type*} [MeasurableSpace E]
    [MetricSpace E] [CompactSpace E] [BorelSpace E] [Nonempty E]
    (νn : ℕ → ℕ → FiniteMeasure E) (η : ℕ → FiniteMeasure E)
    (Mn : ℕ → FiniteMeasure E) (M : FiniteMeasure E)
    (hν : ∀ j, Tendsto (fun n => νn n j) atTop (𝓝 (η j)))
    (hM : Tendsto Mn atTop (𝓝 M))
    (B C : ℝ≥0) (hbound : ∀ n, (Mn n).mass ≤ B)
    (hfinite : ∀ n J, ((∑ j ∈ Finset.range J, νn n j : FiniteMeasure E) : Measure E) ≤ Mn n)
    (htail : ∀ n J, (Mn n).mass ≤
      (∑ j ∈ Finset.range (J+1), νn n j : FiniteMeasure E).mass + C / ((J+1 : ℕ) : ℝ≥0)) :
    Measure.sum (fun j => (η j : Measure E)) = M := by
  have hpartial (J : ℕ) :
      ((∑ j ∈ Finset.range J, η j : FiniteMeasure E) : Measure E) ≤ M :=
    finiteMeasure_le_of_tendsto hM (finiteMeasure_tendsto_sum hν _) B hbound (fun n => hfinite n J)
  have hle : Measure.sum (fun j => (η j : Measure E)) ≤ M := by
    apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.sum_apply _ hA, ENNReal.tsum_eq_iSup_nat]
    apply iSup_le
    intro J
    simpa only [finiteMeasure_coe_sum,Measure.finset_sum_apply] using hpartial J A
  letI : IsFiniteMeasure (Measure.sum (fun j => (η j : Measure E))) := isFiniteMeasure_of_le _ hle
  let S : FiniteMeasure E := ⟨Measure.sum (fun j => (η j : Measure E)),inferInstance⟩
  have hlow (J : ℕ) : M.mass ≤ (∑ j ∈ Finset.range (J+1), η j : FiniteMeasure E).mass +
      C / ((J+1 : ℕ) : ℝ≥0) := by
    apply le_of_tendsto_of_tendsto' hM.mass
      ((finiteMeasure_tendsto_sum hν (Finset.range (J+1))).mass.add_const _) (fun n => htail n J)
  have hsumle (J : ℕ) : (∑ j ∈ Finset.range (J+1), η j : FiniteMeasure E).mass ≤ S.mass := by
    apply ENNReal.coe_le_coe.mp
    rw [FiniteMeasure.ennreal_mass,FiniteMeasure.ennreal_mass,finiteMeasure_coe_sum]
    change (∑ j ∈ Finset.range (J+1), (η j : Measure E)) univ ≤ Measure.sum (fun j => (η j : Measure E)) univ
    rw [Measure.finset_sum_apply,Measure.sum_apply _ MeasurableSet.univ]
    exact ENNReal.sum_le_tsum (Finset.range (J+1))
  have hzero : Tendsto (fun J : ℕ => C / ((J+1 : ℕ) : ℝ≥0)) atTop (𝓝 0) :=
    (NNReal.tendsto_const_div_atTop_nhds_zero_nat C).comp (tendsto_add_atTop_nat 1)
  have hmass : M.mass ≤ S.mass := by
    apply ge_of_tendsto (show Tendsto (fun J : ℕ => S.mass + C / ((J+1 : ℕ) : ℝ≥0))
      atTop (𝓝 S.mass) by simpa using tendsto_const_nhds.add hzero)
    exact Eventually.of_forall (fun J => (hlow J).trans (add_le_add_right (hsumle J) _))
  apply Measure.eq_of_le_of_measure_univ_eq hle
  apply le_antisymm (hle univ)
  change (M : Measure E) univ ≤ (S : Measure E) univ
  simpa only [← FiniteMeasure.ennreal_mass] using ENNReal.coe_le_coe.mpr hmass

end
end Paper14
