import Paper09.UpperParameters
import Paper09.CoarseClusters

open Real Filter MeasureTheory Classical
open scoped Topology
noncomputable section
namespace Paper09.UpperProbability

/-- The actual Gaussian field cutoff event (3.16), with no restriction on
fields outside the finite physical volume. -/
def fieldEvent (d n : ℕ) (σ : ℝ) : Set (LatticeGeometry.Point d → ℝ) :=
  {h | ∀ x : ↥(RFIM.volumeBox d n),
    |h x.val| ≤ σ*sqrt (8*log (((2*n+1)^d:ℕ):ℝ))}

/-- The actual small-coarse-cluster event at the selected integer scales. -/
def clusterEvent (d : ℕ) (κ K ρ : ℝ) (n : ℕ) : Set (LatticeGeometry.Point d → ℝ) :=
  {h | BlockCovering.SmallClusters
    (Percolation.goodLabel K ρ (8*UpperParameters.sourceS κ n)
      (Percolation.initialRadius (8*UpperParameters.sourceS κ n))
      (UpperParameters.sourceS κ n) h)
    n (UpperParameters.sourceS κ n) (UpperScale.clusterCutoff κ n)}

/-- Both environmental inputs to the deterministic upper-bound proof. -/
def goodEvent (d : ℕ) (κ K ρ σ : ℝ) (n : ℕ) : Set (LatticeGeometry.Point d → ℝ) :=
  clusterEvent d κ K ρ n ∩ fieldEvent d n σ

lemma measurableSet_fieldEvent (d n : ℕ) (σ : ℝ) : MeasurableSet (fieldEvent d n σ) := by
  simpa only [fieldEvent, Set.setOf_forall] using
    MeasurableSet.iInter (fun x : ↥(RFIM.volumeBox d n) =>
      measurableSet_le (measurable_pi_apply x.val).abs
        (measurable_const (a := σ*sqrt (8*log (((2*n+1)^d:ℕ):ℝ)))))

lemma physical_volume_ge (d : ℕ) (hd : 1 ≤ d) (n : ℕ) :
    2*n+1 ≤ (2*n+1)^d := by
  simpa using pow_le_pow_right₀ (show 1≤2*n+1 by omega) hd

/-- Gaussian maximal inequality for the actual infinite environment, obtained
from its one-coordinate pushforwards rather than assumed marginal laws. -/
lemma field_failure_bound (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (σ : ℝ) (hσ : 0 < σ) :
    (RFIM.environmentLaw d σ).real (fieldEvent d n σ)ᶜ ≤
      ((((2*n+1)^d:ℕ):ℝ)⁻¹)^2 := by
  let V := ↥(RFIM.volumeBox d n)
  have hcard : Fintype.card V = (2*n+1)^d := by simp [V]
  have hcard2 : 2 ≤ Fintype.card V := by rw [hcard]; have hh := physical_volume_ge d hd n; omega
  have hlaw : ∀ x : V, (RFIM.environmentLaw d σ).map (fun h => h x.val) = Gaussian.law σ := by
    intro x
    exact (measurePreserving_eval_infinitePi (μ := fun _ : RFIM.Point d => Gaussian.law σ) x.val).map_eq
  have hmax := Gaussian.maximum_field (RFIM.environmentLaw d σ) (fun (x : V) h => h x.val)
    (fun x => measurable_pi_apply x.val) σ hσ hlaw hcard2
  rw [hcard] at hmax
  change 1-((((2*n+1)^d:ℕ):ℝ)⁻¹)^2 ≤ (RFIM.environmentLaw d σ).real (fieldEvent d n σ) at hmax
  rw [measureReal_compl (measurableSet_fieldEvent d n σ), measureReal_univ_eq_one]
  linarith

/-- The actual maximum-field event has vanishing complement probability. -/
theorem field_failure_tendsto (d : ℕ) (hd : 1 ≤ d) (σ : ℝ) (hσ : 0 < σ) :
    Tendsto (fun n : ℕ => (RFIM.environmentLaw d σ) (fieldEvent d n σ)ᶜ) atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ => (((2*n+1)^d:ℕ):ℝ)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_natCast_atTop_atTop
    exact Eventually.of_forall (fun n => by
      change (n:ℝ) ≤ (((2*n+1)^d:ℕ):ℝ)
      exact_mod_cast (show n≤(2*n+1)^d from (by omega : n≤2*n+1).trans (physical_volume_ge d hd n)))
  have hinv := hN.inv_tendsto_atTop
  have hbound : Tendsto (fun n : ℕ => (((((2*n+1)^d:ℕ):ℝ)⁻¹)^2)) atTop (𝓝 0) := by
    simpa using hinv.pow 2
  have hreal : Tendsto (fun n : ℕ => (RFIM.environmentLaw d σ).real (fieldEvent d n σ)ᶜ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
      (Eventually.of_forall (fun _ => measureReal_nonneg))
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    exact field_failure_bound d n hd hn σ hσ
  have hh := ENNReal.tendsto_ofReal hreal
  simp only [ENNReal.ofReal_zero] at hh
  convert hh using 1
  ext n
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

/-- Strong disorder supplies one fixed admissible `κ`, simultaneously large
enough for the source cluster estimate and the deterministic scale bounds.
Both actual environmental events then hold with probability tending to one. -/
theorem exists_good_event_scales (d : ℕ) (hd : 2 ≤ d) (σ K ρ : ℝ)
    (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hρsmall : ρ < 1/(40*(d:ℝ)))
    (hweak : (Gaussian.law σ).real {x | |x| ≤ K} < 1/(40*(d:ℝ))) :
    ∃ κ : ℝ, 1 ≤ κ ∧ 4*(d:ℝ) ≤ κ ∧
      Tendsto (fun n : ℕ => (RFIM.environmentLaw d σ) (goodEvent d κ K ρ σ n)ᶜ) atTop (𝓝 0) := by
  obtain ⟨R₀, κ₀, hκ₀, hcluster⟩ := Percolation.lemma_3_2_failure (by omega : 0<d) σ K ρ hρ hρsmall hweak
  let κ : ℝ := max κ₀ (max 1 (4*(d:ℝ)))
  have hκge : κ₀ ≤ κ := le_max_left _ _
  have hκ : 1 ≤ κ := (le_max_left _ _).trans (le_max_right _ _)
  have hκd : 4*(d:ℝ) ≤ κ := (le_max_right _ _).trans (le_max_right _ _)
  have hκp : 0 < κ := by linarith
  have hLtop := UpperScale.clusterCutoff_tendsto hκp
  have hexp : Tendsto (fun n : ℕ => exp (-(UpperScale.clusterCutoff κ n:ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hLtop)
  have hcreal : Tendsto (fun n : ℕ => (RFIM.environmentLaw d σ).real (clusterEvent d κ K ρ n)ᶜ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp
      (Eventually.of_forall (fun _ => measureReal_nonneg))
    filter_upwards [UpperScale.scales_admissible d hd κ hκ hκd R₀,
      eventually_ge_atTop (1:ℕ)] with n hn hn1
    have hlog : 0 ≤ log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    have hL : κ₀*log n ≤ (UpperScale.clusterCutoff κ n:ℝ) :=
      (mul_le_mul_of_nonneg_right hκge hlog).trans (Nat.le_ceil _)
    have hsdiv : (8*UpperParameters.sourceS κ n)/8 = UpperParameters.sourceS κ n := by omega
    have hbound := hcluster (8*UpperParameters.sourceS κ n) n (UpperScale.clusterCutoff κ n)
      hn.1 hn.2.1 hn.2.2.1 hL
    simpa only [hsdiv, clusterEvent, Set.compl_setOf] using hbound
  have hc : Tendsto (fun n : ℕ => (RFIM.environmentLaw d σ) (clusterEvent d κ K ρ n)ᶜ) atTop (𝓝 0) := by
    have hh := ENNReal.tendsto_ofReal hcreal
    simp only [ENNReal.ofReal_zero] at hh
    convert hh using 1
    ext n
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  refine ⟨κ, hκ, hκd, ?_⟩
  exact failure_intersection_tendsto_zero (RFIM.environmentLaw d σ)
    (clusterEvent d κ K ρ) (fun n => fieldEvent d n σ) hc
    (field_failure_tendsto d (by omega) σ hσ)

/-- The exponent scale in the final upper bound diverges, so any fixed
multiplicative prefactor can be absorbed by enlarging its constant. -/
theorem upper_shape_tendsto (d : ℕ) (hd : 2 ≤ d) :
    Tendsto (fun n : ℕ => (log (n:ℝ))^exponentA d*(log (log (n:ℝ)))^(d-1)) atTop atTop := by
  have hln := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbase := (tendsto_rpow_atTop (exponentA_pos hd)).comp hln
  apply tendsto_atTop_mono' atTop _ hbase
  filter_upwards [(Real.tendsto_log_atTop.comp hln).eventually (eventually_ge_atTop 1),
    hln.eventually (eventually_ge_atTop 0)] with n hll hlog
  have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ (n := d-1) hll)
    (Real.rpow_nonneg hlog (exponentA d))
  simpa only [mul_one] using hh

end Paper09.UpperProbability
