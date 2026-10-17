/-
Copyright (c) 2026. The actual strong-disorder upper bound.
-/
import Paper09.LowerBound
import Paper09.RFIMBlocks
import Paper09.CensoredMixing
import Paper09.UpperParameters
import Paper09.SimulatedContraction
import Paper09.UpperProbability

open Finset BigOperators Classical Real Filter MeasureTheory
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Paper09.RFIM
set_option maxHeartbeats 0
set_option maxRecDepth 4000
open Paper09.BlockCovering Paper09.BlockColoring Paper09.BlockDynamics
open Paper09.IdealContraction

local instance (priority := 2000) upperSiteDecEq {d : ℕ} (A : Finset (Point d)) :
    DecidableEq ↥A := Classical.decEq _

/-- Appendix A.1 converts an actual RFIM mixing bound to a simultaneous
relaxation and mixing bound, retaining the fixed `log 2` factor explicitly. -/
theorem max_times_le_of_mixing_bound (d n : ℕ) (β : ℝ) (h : Point d → ℝ)
    (E : ℝ) (hmix : mixingTime d n β h ≤ exp E) :
    max (relaxationTime d n β h) (mixingTime d n β h) ≤
      exp (E - log (log 2)) := by
  let p := freeGibbs (volumeBox d n) h β
  let x : ↥(volumeBox d n) := ⟨(fun _ => 0),mem_volumeBox.mpr (by
    intro j; constructor <;> omega)⟩
  have hp : ∀ η, 0 < p.w η := by
    intro η
    exact div_pos (isingWeight_pos _ _ _ _ _ _ _) (isingZ_pos _ _ _ _ _ _)
  have hlog : 0 < log (2:ℝ) := Real.log_pos (by norm_num)
  have hlog1 : log (2:ℝ) ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hlower := heatBath_mixing_lower p hp x
  have hgap : 0 < spectralGap p := heatBath_gap_pos p hp x
  have hm0 : 0 ≤ mixingTime d n β h :=
    (mul_nonneg hlog.le (inv_nonneg.mpr hgap.le)).trans hlower
  have hinv : 1 ≤ (log (2:ℝ))⁻¹ := (one_le_inv₀ hlog).mpr hlog1
  have hrel : relaxationTime d n β h ≤ (log (2:ℝ))⁻¹ * exp E := by
    have hh : log 2 * relaxationTime d n β h ≤ exp E := hlower.trans hmix
    have ht := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hlog.le)
    simpa only [← mul_assoc,inv_mul_cancel₀ hlog.ne',one_mul] using ht
  have hm : mixingTime d n β h ≤ (log (2:ℝ))⁻¹ * exp E :=
    hmix.trans (le_mul_of_one_le_left (Real.exp_nonneg E) hinv)
  have hexp : (log (2:ℝ))⁻¹ * exp E = exp (E-log (log 2)) := by
    rw [Real.exp_sub,Real.exp_log hlog]
    ring
  rw [← hexp]
  exact max_le hrel hm

/-- On the actual cluster and field events, the simulated physical block
kernel, path coupling and censoring give the source exponential mixing bound.
The same constant and volume threshold work for every field in that event. -/
theorem mixing_bound_on_good_event (d : ℕ) (K β σ κ : ℝ)
    (hd : 2 ≤ d) (hβ : 0 < β) (hσ : 0 ≤ σ)
    (hκ : 1 ≤ κ) (hκd : 4*(d:ℝ) ≤ κ) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∀ h : Point d → ℝ,
      h ∈ UpperProbability.goodEvent d κ K (rho K d β) σ n →
      mixingTime d n β h ≤
        exp (C*(log (n:ℝ))^exponentA d*(log (log (n:ℝ)))^(d-1)) := by
  obtain ⟨C,hC,hCr,hcontract⟩ :=
    SimulatedContraction.lemma_3_6 d K β σ κ hd hβ hσ hκ
  obtain ⟨C',hC',htime⟩ :=
    UpperScale.final_physical_time_bound d hd κ C hκ hκd hC
  have hparam := UpperParameters.covering_parameters d hd κ (rho K d β) hκ (rho_pos K d β)
  have hrate : coveringRate d ≤ 1 := by
    have hcol : (1:ℝ) ≤ (coloringConstant d:ℝ) := by
      exact_mod_cast (show 1 ≤ coloringConstant d from Nat.succ_le_iff.mpr (by
        unfold coloringConstant
        positivity))
    have hpow : (1:ℝ) ≤ (4:ℝ)^d := one_le_pow₀ (by norm_num)
    have hden : (1:ℝ) ≤ 4*(4:ℝ)^d*(coloringConstant d:ℝ) := by nlinarith
    exact (div_le_one (by positivity)).mpr hden
  refine ⟨C',hC',?_⟩
  filter_upwards [hcontract,htime,hparam] with n hn htime hparam
  obtain ⟨hs,hcontract⟩ := hn
  intro h hgood
  have hevent : SmallClusters (sourceGood K β (UpperParameters.sourceS κ n) h)
      n (UpperParameters.sourceS κ n) (UpperScale.clusterCutoff κ n) := hgood.1
  have hfield : ∀ x ∈ volume n,
      |h x| ≤ σ*sqrt (8*log (((2*n+1)^d:ℕ):ℝ)) := by
    intro x hx
    apply hgood.2 ⟨x,?_⟩
    rwa [RFIMBlocks.volume_eq_volumeBox] at hx
  obtain ⟨hT,hW⟩ := hcontract h hevent hfield
  let s := UpperParameters.sourceS κ n
  let good := sourceGood K β s h
  let M : ℝ := maxBlockSize good n s
  let N : ℝ := (((2*n+1)^d:ℕ):ℝ)
  let T := UpperScale.stepTime d C (8*s) (UpperScale.clusterCutoff κ n) M N
  have hpar := hparam good hevent
  have hM : 1 ≤ M := by
    dsimp only [M,s]
    exact_mod_cast hpar.2.2.1
  have hMb : M ≤ (UpperScale.clusterCutoff κ n:ℝ)*
      (UpperScale.roundedRadius (UpperScale.clusterCutoff κ n):ℝ)^d := by
    change (maxBlockSize good n s:ℝ) ≤ _
    rw [← UpperParameters.source_radius]
    exact_mod_cast hpar.2.2.2.1
  have hN : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast (one_le_pow₀ (by omega : 1 ≤ 2*n+1) : 1 ≤ (2*n+1)^d)
  have hcard : (Fintype.card ↥(volume (d := d) n):ℝ) ≤ N := by
    simp [N,RFIMBlocks.volume_eq_volumeBox]
  have hratio : coveringRate d/M ≤ 1 :=
    (div_le_one (by linarith : 0 < M)).mpr (hrate.trans hM)
  have hmix := CensoredMixing.mixingTime_from_one_site
    (domainLattice (volume (d := d) n)) (fun x => h x.val) β hβ.le ∅ (fun _ => 0)
    (RFIMBlocks.uniformColors (colorCount good n s) (colorCount_pos hs hevent))
    (RFIMBlocks.retainedSites (coloring hs hevent))
    T hT C M N (coveringRate d) hM hN hcard (coveringRate_pos d) hCr hratio
    (by
      intro η ξ hdist
      have hh := hW η ξ
      simpa only [hammingR,hdist,Nat.cast_one,mul_one,
        SimulatedContraction.canonicalKernel,RFIMBlocks.volumeLaw,freeGibbs] using hh)
  have hmix' : mixingTime d n β h ≤ (UpperScale.stepCount C M N:ℝ)*T := by
    unfold mixingTime
    rw [← RFIMBlocks.volume_eq_volumeBox d n]
    exact hmix
  have hR : (8:ℝ)*(s:ℝ) =
      (UpperScale.roundedRadius (UpperScale.clusterCutoff κ n):ℝ) := by
    exact_mod_cast (show 8*s = UpperScale.roundedRadius (UpperScale.clusterCutoff κ n)
      from UpperParameters.source_radius κ n)
  apply hmix'.trans
  simpa only [T,N,hR] using htime M hM hMb

/-- Proposition 3.1 for the actual free-boundary RFIM and its actual
continuous-time heat-bath relaxation and mixing times. Only strong Gaussian
disorder is assumed; the good-event inputs and all dynamical estimates are
proved upstream. -/
theorem proposition_3_1 (d : ℕ) (β σ : ℝ) (hd : 2 ≤ d) (hβ : 0 < β)
    (hσ : 0 < σ) (hstrong : StrongGaussianDisorder d β σ) :
    ∃ C > 0, Tendsto (fun n : ℕ => (environmentLaw d σ)
      {h | ¬ max (relaxationTime d n β h) (mixingTime d n β h) ≤
        exp (C*(log (n:ℝ))^exponentA d*(log (log (n:ℝ)))^(d-1))}) atTop (𝓝 0) := by
  obtain ⟨K,hK,hρsmall,hweak⟩ := hstrong
  obtain ⟨κ,hκ,hκd,hprob⟩ := UpperProbability.exists_good_event_scales d hd σ K
    (rho K d β) hσ (rho_pos K d β).le hρsmall hweak
  obtain ⟨C,hC,hmix⟩ := mixing_bound_on_good_event d K β σ κ hd hβ hσ.le hκ hκd
  have hshape := (UpperProbability.upper_shape_tendsto d hd).eventually
    (eventually_ge_atTop (-log (log (2:ℝ))))
  refine ⟨C+1,by linarith,?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hprob
    (Eventually.of_forall (fun _ => zero_le _))
  filter_upwards [hmix,hshape] with n hn hshape
  apply measure_mono
  intro h hbad hgood
  apply hbad
  have hh := max_times_le_of_mixing_bound d n β h _ (hn h hgood)
  apply hh.trans
  apply Real.exp_le_exp.mpr
  nlinarith only [hshape]

end Paper09.RFIM
