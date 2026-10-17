import Paper32.VariationalBridge
import Paper32.Avoidance
import Paper32.Dynamics
import Paper32.Steps
import Paper32.FirstStep
import Paper32.LimitEvents

open Set Filter Topology MeasureTheory ProbabilityTheory
namespace Paper32
open TrapParameters

private noncomputable def coreStep_of_actual_update {v z z' w ν : Point} {a : ℝ}
    (hv : U v) (hz : l1 z < 4) (havoid : z ∉ singularArrangement)
    (hw : w ∈ clarkeSubdiff (tilt v) z)
    (hν : |ν.1| ≤ 1/100 ∧ |ν.2| ≤ 1/100)
    (hrec : z' = z-a • (w+ν)) :
    numericalParameters.CoreStep a z.1 z.2 z'.1 z'.2 := by
  classical
  have hx : z.1 ≠ 0 := fun h => havoid (Or.inl h)
  have hy : z.2 ≠ 0 := fun h => havoid (Or.inr (Or.inl h))
  have hb : |z.2| ≠ 2*|z.1| := fun h => havoid (Or.inr (Or.inr h))
  have hweq : w = gradCore z-v := by
    rw [clarke_tilt_off_singular hz hx hy hb] at hw
    exact mem_singleton_iff.mp hw
  refine { x_ne := hx
           y_ne := hy
           sector_ne := by norm_num [TrapParameters.slope,numericalParameters]; exact hb
           ex := ν.1-v.1
           ey := ν.2-v.2
           ex_bound := by norm_num [numericalParameters]; exact (effective_noise_bound hv.1 hν.1).le
           ey_bound := by norm_num [numericalParameters]; exact (effective_noise_bound hv.2 hν.2).le
           x_update := ?_
           y_update := ?_ }
  · have h := congrArg Prod.fst hrec
    rw [hweq] at h
    simp only [Prod.fst_sub, Prod.smul_fst, Prod.fst_add, smul_eq_mul] at h
    rw [quadrantSign_eq_sign hx]
    norm_num [Horizontal,TrapParameters.slope,numericalParameters]
    by_cases hh : |z.2| < 2*|z.1|
    · simp only [gradCore,hh,if_true] at h ⊢
      nlinarith [h]
    · simp only [gradCore,hh,if_false] at h ⊢
      nlinarith [h]
  · have h := congrArg Prod.snd hrec
    rw [hweq] at h
    simp only [Prod.snd_sub, Prod.smul_snd, Prod.snd_add, smul_eq_mul] at h
    rw [quadrantSign_eq_sign hy]
    norm_num [Horizontal,TrapParameters.slope,numericalParameters]
    by_cases hh : |z.2| < 2*|z.1|
    · simp only [gradCore,hh,if_true] at h ⊢
      nlinarith [h]
    · simp only [gradCore,hh,if_false] at h ⊢
      nlinarith [h]

private lemma numerical_state_bounds {r x y : ℝ} (hr : 0 < r)
    (hs : numericalParameters.Tight r x y ∨ numericalParameters.Recovery r x y) :
    |x| ≤ (36/5)*r ∧ |y| ≤ (39/10)*r := by
  rcases hs with ht | ht
  · norm_num [Tight,numericalParameters] at ht
    exact ⟨ht.1,by nlinarith [ht.2]⟩
  · norm_num [Recovery,numericalParameters] at ht
    exact ⟨ht.1,ht.2.1⟩

/-- The local-to-global pathwise assembly of Theorem 2.2.
No envelope or convergence conclusion is among its hypotheses. -/
theorem pathwise_coercive_trapping {v : Point} {γ : ℝ} (hv : U v)
    (hγlo : (1/2:ℝ) < γ) (hγhi : γ < 1)
    (z w ν : ℕ → Point) (hinit : Dstar (z 0))
    (hw : ∀ k, w k ∈ clarkeSubdiff (tilt v) (z k))
    (hν : ∀ k, |(ν k).1| ≤ 1/100 ∧ |(ν k).2| ≤ 1/100)
    (hrec : ∀ k, z (k+1) = z k-powerStep γ k • (w k+ν k))
    (havoid : ∀ k ≥ 1, z k ∉ singularArrangement) :
    (∀ k, |(z (k+1)).1| ≤ (36/5)*powerStep γ k ∧
      |(z (k+1)).2| ≤ (39/10)*powerStep γ k) ∧
    Tendsto z atTop (𝓝 0) := by
  have hγpos : 0 < γ := by linarith
  have hz0 : l1 (z 0) < 4 := by unfold l1; linarith [hinit.1,hinit.2]
  have hw0 := clarke_tilt_coordinate_bound hz0 (hw 0)
  have hfirst := first_step_capture (powerStep_initial_lower hγhi)
    hinit.1 hinit.2 hv.1 hv.2 hw0.1 hw0.2 (hν 0).1 (hν 0).2
  have hfirst' : numericalParameters.Tight (powerStep γ 0) (z 1).1 (z 1).2 := by
    have hrx := congrArg Prod.fst (hrec 0)
    have hry := congrArg Prod.snd (hrec 0)
    simp only [Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,Prod.fst_add,Prod.snd_add,
      smul_eq_mul,Nat.zero_add] at hrx hry
    norm_num [Tight,numericalParameters]
    constructor
    · simpa only [hrx,← mul_add] using hfirst.1.le
    · simpa only [hry,← mul_add] using hfirst.2.le
  have hlocal : ∀ k,
      (numericalParameters.Tight (powerStep γ k) (z (k+1)).1 (z (k+1)).2 ∨
       numericalParameters.Recovery (powerStep γ k) (z (k+1)).1 (z (k+1)).2) →
      numericalParameters.CoreStep (powerStep γ (k+1)) (z (k+1)).1 (z (k+1)).2
        (z (k+2)).1 (z (k+2)).2 := by
    intro k hs
    have hbnd : |(z (k+1)).1| ≤ (36/5)*powerStep γ k ∧
        |(z (k+1)).2| ≤ (39/10)*powerStep γ k := by
      exact numerical_state_bounds (powerStep_pos γ k) hs
    have hzlocal : l1 (z (k+1)) < 4 := by
      have hle := powerStep_antitone hγpos.le (Nat.zero_le k)
      have hup := powerStep_initial_upper hγlo
      unfold l1
      nlinarith [hbnd.1,hbnd.2]
    exact coreStep_of_actual_update hv hzlocal (havoid (k+1) (by omega)) (hw (k+1))
      (hν (k+1)) (by simpa [Nat.add_assoc] using hrec (k+1))
  have hstates := parameterized_invariant_local numericalParameters (powerStep γ)
    (fun k => (z k).1) (fun k => (z k).2) (powerStep_pos γ)
    (by norm_num [numericalParameters]; exact powerStep_ratio_bound hγhi) hlocal hfirst'
  have hbounds : ∀ k, |(z (k+1)).1| ≤ (36/5)*powerStep γ k ∧
      |(z (k+1)).2| ≤ (39/10)*powerStep γ k := by
    intro k
    exact numerical_state_bounds (powerStep_pos γ k) (hstates k)
  have hxlim : Tendsto (fun k => (z (k+1)).1) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k => ?_)
      (show Tendsto (fun k => (36/5:ℝ)*powerStep γ k) atTop (𝓝 0) by
        simpa using (powerStep_tendsto_zero hγpos).const_mul (36/5))
    simpa using (hbounds k).1
  have hylim : Tendsto (fun k => (z (k+1)).2) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k => ?_)
      (show Tendsto (fun k => (39/10:ℝ)*powerStep γ k) atTop (𝓝 0) by
        simpa using (powerStep_tendsto_zero hγpos).const_mul (39/10))
    simpa using (hbounds k).2
  exact ⟨hbounds,(tendsto_add_atTop_iff_nat 1).mp (hxlim.prodMk_nhds hylim)⟩

/-- Theorem 2.2 with the actual pre-noise sigma fields and conditional laws.
The event quantifiers are for one fixed oracle process, as in the paper. -/
theorem coercive_trapping_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ℕ → MeasurableSpace Ω) (hm : ∀ k, m k ≤ mΩ)
    {v : Point} {γ : ℝ} (hv : U v) (hγlo : (1/2:ℝ) < γ) (hγhi : γ < 1)
    (z w ν : ℕ → Ω → Point)
    (hzmeas : ∀ k, Measurable[m k] (z k)) (hwmeas : ∀ k, Measurable[m k] (w k))
    (hνmeas : ∀ k, Measurable (ν k))
    (hinit : ∀ᵐ ω ∂μ, Dstar (z 0 ω))
    (hw : ∀ k, ∀ᵐ ω ∂μ, w k ω ∈ clarkeSubdiff (tilt v) (z k ω))
    (hν : ∀ k, ∀ᵐ ω ∂μ, |(ν k ω).1| ≤ 1/100 ∧ |(ν k ω).2| ≤ 1/100)
    (hac : ∀ k, ∀ᵐ ω ∂μ,
      condDistrib (ν k) (preNoiseObservation (m k)) μ
        (preNoiseObservation (m k) ω) ≪ (volume : Measure Point))
    (hrec : ∀ k, ∀ᵐ ω ∂μ, z (k+1) ω=z k ω-powerStep γ k • (w k ω+ν k ω)) :
    (∀ᵐ ω ∂μ, (∀ k, |(z (k+1) ω).1| ≤ (36/5)*powerStep γ k ∧
      |(z (k+1) ω).2| ≤ (39/10)*powerStep γ k) ∧
      Tendsto (fun k => z k ω) atTop (𝓝 0)) ∧
    μ (boundedOrbitEvent z \ localMinLimitEvent (tilt v) z)=1 := by
  have havoid := ae_forall_positive_avoidance_adapted μ m hm z w ν (powerStep γ)
    hzmeas hwmeas hνmeas (fun k => ne_of_gt (powerStep_pos γ k)) hac hrec
  have hall : ∀ᵐ ω ∂μ, (∀ k, |(z (k+1) ω).1| ≤ (36/5)*powerStep γ k ∧
      |(z (k+1) ω).2| ≤ (39/10)*powerStep γ k) ∧
      Tendsto (fun k => z k ω) atTop (𝓝 0) := by
    filter_upwards [hinit,ae_all_iff.mpr hw,ae_all_iff.mpr hν,ae_all_iff.mpr hrec,havoid]
      with ω hω0 hωw hων hωrec hωavoid
    exact pathwise_coercive_trapping hv hγlo hγhi (fun k => z k ω) (fun k => w k ω)
      (fun k => ν k ω) hω0 hωw hων hωrec hωavoid
  exact ⟨hall,measure_bad_limit_eq_one μ (not_localMin_tilt hv) (hall.mono fun _ h => h.2)⟩

end Paper32
