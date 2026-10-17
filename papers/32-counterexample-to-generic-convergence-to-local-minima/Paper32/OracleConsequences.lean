import Paper32.Counterexample

open Set Filter Topology MeasureTheory ProbabilityTheory
namespace Paper32

/-- Remark 2.4 for every admissible pre-noise oracle, allowing a random
initialization in the basin outside the null singular arrangement. -/
theorem all_oracles_ordinaryGradient_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ℕ → MeasurableSpace Ω) (hm : ∀ k, m k ≤ mΩ)
    {v : Point} {γ : ℝ} (hv : U v) (hγlo : (1/2:ℝ) < γ) (hγhi : γ < 1)
    (z w ν : ℕ → Ω → Point)
    (hzmeas : ∀ k, Measurable[m k] (z k)) (hwmeas : ∀ k, Measurable[m k] (w k))
    (hνmeas : ∀ k, Measurable (ν k))
    (hinit : ∀ᵐ ω ∂μ, Dstar (z 0 ω) ∧ z 0 ω ∉ singularArrangement)
    (hw : ∀ k, ∀ᵐ ω ∂μ, w k ω ∈ clarkeSubdiff (tilt v) (z k ω))
    (hν : ∀ k, ∀ᵐ ω ∂μ, |(ν k ω).1| ≤ 1/100 ∧ |(ν k ω).2| ≤ 1/100)
    (hac : ∀ k, ∀ᵐ ω ∂μ,
      condDistrib (ν k) (preNoiseObservation (m k)) μ (preNoiseObservation (m k) ω) ≪
        (volume : Measure Point))
    (hrec : ∀ k, ∀ᵐ ω ∂μ, z (k+1) ω=z k ω-powerStep γ k • (w k ω+ν k ω)) :
    ∀ᵐ ω ∂μ, (∀ k,
      HasFDerivAt (tilt v) (linCLM (gradCore (z k ω)-v)) (z k ω) ∧
      w k ω=gradCore (z k ω)-v) ∧ Tendsto (fun k => z k ω) atTop (𝓝 0) := by
  have ht := (coercive_trapping_ae μ m hm hv hγlo hγhi z w ν hzmeas hwmeas hνmeas
    (hinit.mono fun _ h => h.1) hw hν hac hrec).1
  have ha := ae_forall_positive_avoidance_adapted μ m hm z w ν (powerStep γ)
    hzmeas hwmeas hνmeas (fun k => (powerStep_pos γ k).ne') hac hrec
  filter_upwards [ht,ha,hinit,ae_all_iff.mpr hw] with ω htrap hav hi hmem
  refine ⟨?_,htrap.2⟩
  intro k
  have hnon : z k ω ∉ singularArrangement := by
    cases k with
    | zero => exact hi.2
    | succ k => exact hav (k+1) (by omega)
  have hlocal : l1 (z k ω) < 4 := by
    cases k with
    | zero => unfold l1; linarith [hi.1.1,hi.1.2]
    | succ k =>
      have hb := htrap.1 k
      have hα := powerStep_antitone (by linarith : 0 ≤ γ) (Nat.zero_le k)
      have hα0 := powerStep_initial_upper hγlo
      unfold l1
      nlinarith [hb.1,hb.2]
  have hx : (z k ω).1 ≠ 0 := fun h => hnon (Or.inl h)
  have hy : (z k ω).2 ≠ 0 := fun h => hnon (Or.inr (Or.inl h))
  have hb : |(z k ω).2| ≠ 2*|(z k ω).1| := fun h => hnon (Or.inr (Or.inr h))
  refine ⟨hasFDerivAt_tilt hlocal hx hy hb,?_⟩
  have h := hmem k
  rw [clarke_tilt_off_singular hlocal hx hy hb] at h
  exact mem_singleton_iff.mp h

/-- A genuine uniform basin initialization lies in the basin and avoids N a.s.
Thus it is an admissible random initialization for the preceding theorem and Main.
The result does not rely on conditioning separately at each deterministic point. -/
theorem uniform_basin_initialization_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (x0 : Ω → Point)
    (hx0 : Measurable x0) (hu : pdf.IsUniform x0 initialRectangle μ volume) :
    ∀ᵐ ω ∂μ, Dstar (x0 ω) ∧ x0 ω ∉ singularArrangement := by
  have hrect : MeasurableSet initialRectangle := measurableSet_Ioo.prod measurableSet_Ioo
  have hmem : ∀ᵐ u ∂μ.map x0, u ∈ initialRectangle := by
    rw [hu]
    exact ae_cond_mem hrect
  have hnull : μ.map x0 singularArrangement=0 := by
    have hac : μ.map x0 ≪ (volume : Measure Point) := by rw [hu]; exact cond_absolutelyContinuous
    exact hac volume_singularArrangement
  have havoid : ∀ᵐ u ∂μ.map x0, u ∉ singularArrangement := by
    exact ae_iff.mpr (by simpa only [not_not] using hnull)
  filter_upwards [ae_of_ae_map hx0.aemeasurable hmem,ae_of_ae_map hx0.aemeasurable havoid]
    with ω hω hN
  exact ⟨(mem_initialRectangle (x0 ω)).mp hω,hN⟩

end Paper32
