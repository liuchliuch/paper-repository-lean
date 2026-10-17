import Paper09.RareScale
import Paper09.IslandGap
import Paper09.MixingTimes

open Finset BigOperators Classical Real Filter MeasureTheory
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Paper09.RFIM
set_option maxHeartbeats 0
set_option maxRecDepth 4000
local instance (priority := 2000) lowerPointDecEq (d : ℕ) : DecidableEq (Point d) := Classical.decEq _
local instance (priority := 2000) lowerSiteDecEq {d : ℕ} (A : Finset (Point d)) : DecidableEq ↥A := Classical.decEq _

/-- Worst-initial-state mixing time at error `1/4` for the actual continuous
rate-one heat-bath RFIM dynamics. -/
def mixingTime (d n : ℕ) (β : ℝ) (h : Point d → ℝ) : ℝ :=
  tMix (freeGibbs (volumeBox d n) h β)
    (heatBathTransition (freeGibbs (volumeBox d n) h β)) (1/4)

/-- A fixed shell threshold consumes at most a quarter of the surface
barrier; it does not depend on the island size. -/
lemma exists_shell_threshold (d : ℕ) (β c₀ : ℝ) (hβ : 0 ≤ β) (hc₀ : 0 < c₀) :
    ∃ H > 0, 2*(d:ℝ)*qH H d β*(exp (8*(d:ℝ)*β)-1+8*(d:ℝ)*β) ≤ c₀/4 := by
  let F : ℝ := exp (8*(d:ℝ)*β)-1+8*(d:ℝ)*β
  have hF : 0 ≤ F := by
    have hh : 0 ≤ 8*(d:ℝ)*β := by positivity
    dsimp [F]
    linarith [Real.one_le_exp_iff.mpr hh]
  let T : ℝ := 8*(d:ℝ)*F/c₀
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let H : ℝ := 1 + 2*(d:ℝ)*β + (1/2)*log (1+T)
  have hlog : 0 ≤ log (1+T) := Real.log_nonneg (by linarith)
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨H, hH, ?_⟩
  have harg : 2*(H-2*(d:ℝ)*β) = 2+log (1+T) := by dsimp [H]; ring
  have hq : qH H d β ≤ 1/(2+T) := by
    unfold qH
    rw [harg, Real.exp_add, Real.exp_log (by linarith : 0 < 1+T)]
    apply one_div_le_one_div_of_le (by positivity)
    have he : 1 ≤ exp (2:ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hq (show 0 ≤ 2*(d:ℝ)*F by positivity)
  have hlast : 2*(d:ℝ)*F*(1/(2+T)) ≤ c₀/4 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    rw [show 2*(d:ℝ)*F*(1/(2+T))*4 = (8*(d:ℝ)*F)/(2+T) by ring]
    apply (div_le_iff₀ (show 0 < 2+T by positivity)).mpr
    dsimp [T]
    field_simp
    nlinarith
  change 2*(d:ℝ)*qH H d β*F ≤ c₀/4
  nlinarith

/-- A genuine small spectral gap yields the lower bound simultaneously for
relaxation and worst-start mixing; the fixed `log 2` factor is absorbed. -/
lemma times_lower_of_gap {d n : ℕ} (β : ℝ) (h : Point d → ℝ) {A L : ℝ}
    (hL : 0 ≤ L) (hLA : 2*L ≤ A) (habsorb : -log (log 2) ≤ L)
    (hgap : spectralGap (freeGibbs (volumeBox d n) h β) ≤ exp (-A)) :
    exp L ≤ min (relaxationTime d n β h) (mixingTime d n β h) := by
  let p := freeGibbs (volumeBox d n) h β
  let x : ↥(volumeBox d n) := ⟨(fun _ => 0), mem_volumeBox.mpr (by intro j; constructor <;> omega)⟩
  have hp : ∀ η, 0 < p.w η := by
    intro η
    exact div_pos (isingWeight_pos _ _ _ _ _ _ _) (isingZ_pos _ _ _ _ _ _)
  have hg : 0 < spectralGap p := heatBath_gap_pos p hp x
  have hrel : exp A ≤ (spectralGap p)⁻¹ := by
    have hh := one_div_le_one_div_of_le hg hgap
    simpa only [one_div, ← Real.exp_neg, neg_neg] using hh
  have hmix := heatBath_mixing_lower p hp x
  apply le_min
  · exact (Real.exp_le_exp.mpr (by linarith : L ≤ A)).trans hrel
  · have he : exp L ≤ log 2 * exp A := by
      calc
        exp L ≤ exp (log (log 2)+A) := Real.exp_le_exp.mpr (by linarith)
        _ = _ := by rw [Real.exp_add, Real.exp_log (Real.log_pos (by norm_num : (1:ℝ)<2))]
    apply he.trans
    exact (mul_le_mul_of_nonneg_left hrel (Real.log_nonneg (by norm_num))).trans hmix

/-- The packed-candidate cost is polynomially small while their number is
polynomially large. This retains the actual floor in the packing. -/
lemma candidate_error_bound {d n m : ℕ} {C γ : ℝ} (hd : 0 < d)
    (hC : 0 ≤ C) (hγ : 0 < γ) (hγC : C*γ ≤ (d:ℝ)/4)
    (hn : 0 < (n:ℝ)) (hm : 1 ≤ m) (hll : 0 < log (log n))
    (hb : 0 < RareScale.base n) (hmr : (m:ℝ) ≤ RareScale.radius γ d n)
    (hrlog : RareScale.radius γ d n ≤ log n)
    (hpack : Real.sqrt n ≤ (n/(m+2):ℕ)) :
    exp (-((n/(m+2):ℕ):ℝ)^d * exp (-C*(m:ℝ)^d*log m)) ≤
      exp (-exp ((d:ℝ)/4*log n)) := by
  have hcost := RareScale.cost_le hγ hC hd hm hll hb hmr hrlog
  have hln : 0 ≤ log n := by
    have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    exact (hm0.trans_le (hmr.trans hrlog)).le
  have hcost' : C*(m:ℝ)^d*log m ≤ (d:ℝ)/4*log n :=
    hcost.trans (mul_le_mul_of_nonneg_right hγC hln)
  have hq := pow_le_pow_left₀ (Real.sqrt_nonneg (n:ℝ)) hpack d
  have hsqrt : Real.sqrt (n:ℝ) = exp (log n/2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn]
    congr 1
    ring
  rw [hsqrt, ← Real.exp_nat_mul] at hq
  have hp := Real.exp_le_exp.mpr (neg_le_neg hcost')
  have hprod := mul_le_mul hq hp (Real.exp_nonneg _) (by positivity)
  rw [← Real.exp_add] at hprod
  have heq : (d:ℝ)*(log n/2) + -((d:ℝ)/4*log n) = (d:ℝ)/4*log n := by ring
  rw [heq] at hprod
  apply Real.exp_le_exp.mpr
  simpa only [neg_mul] using neg_le_neg hprod

/-- Proposition 2.1: under only the paper's pure-system input, every positive
Gaussian variance produces the Griffiths lower bound for both actual times. -/
theorem proposition_2_1 (d : ℕ) (β σ : ℝ) (hd : 2 ≤ d) (hβ : 0 < β)
    (hσ : 0 < σ) (hslow : SurfaceSlowPureBoxes d β) :
    ∃ c > 0, Tendsto (fun n : ℕ => (environmentLaw d σ)
      {h | ¬ exp (c * (log (n:ℝ) / log (log (n:ℝ))) ^ exponentA d) ≤
        min (relaxationTime d n β h) (mixingTime d n β h)}) atTop (𝓝 0) := by
  obtain ⟨c₀, seq, hc₀, hseq, hratio, hslow⟩ := hslow.exists_slow_sequence
  obtain ⟨K, hK⟩ := eventually_atTop.mp hslow
  obtain ⟨H, hH, hthreshold⟩ := exists_shell_threshold d β c₀ hβ.le hc₀
  let ε : ℝ := c₀/16
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C, hC, hno⟩ := no_lattice_island_bound d σ ε H hσ hε
  let γ : ℝ := min 1 ((d:ℝ)/(4*C))
  have hd0 : 0 < d := by omega
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγ1 : γ ≤ 1 := min_le_left _ _
  have hγC : C*γ ≤ (d:ℝ)/4 := by
    have hh : γ ≤ (d:ℝ)/(4*C) := min_le_right _ _
    have hh' := mul_le_mul_of_nonneg_left hh hC.le
    have heq : C*((d:ℝ)/(4*C)) = (d:ℝ)/4 := by field_simp
    linarith
  let b : ℝ := γ ^ exponentA d / 2 ^ (d-1)
  have hb : 0 < b := by dsimp [b]; positivity
  let c : ℝ := c₀/4*b
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  letI : IsProbabilityMeasure (environmentLaw d σ) := by unfold environmentLaw; infer_instance
  have hreal : Tendsto (fun n : ℕ => (environmentLaw d σ).real
      {h | ¬ exp (c * (log (n:ℝ) / log (log (n:ℝ))) ^ exponentA d) ≤
        min (relaxationTime d n β h) (mixingTime d n β h)}) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (RareScale.failure_tendsto d hd0) (Eventually.of_forall (fun _ => measureReal_nonneg))
    obtain ⟨R, hscale⟩ := dense_sequence_scale seq hseq hratio (max K 2)
    have hrad := (RareScale.radius_tendsto hγ hd0).eventually (eventually_ge_atTop R)
    have hprops := RareScale.radius_le_log hγ hγ1 (by omega : 1 ≤ d)
    have hbase : Tendsto (fun n : ℝ => c * RareScale.base n ^ exponentA d) atTop atTop :=
      ((tendsto_rpow_atTop (exponentA_pos hd)).comp RareScale.base_tendsto).const_mul_atTop hc
    have habs := hbase.eventually (eventually_ge_atTop (-log (log 2)))
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hrad,
      tendsto_natCast_atTop_atTop.eventually hprops,
      tendsto_natCast_atTop_atTop.eventually habs,
      RareScale.packing_sqrt, eventually_ge_atTop (3:ℕ)] with n hnrad hnprops hnabs hnpack hn3
    obtain ⟨k, hk, hm1, hmr, hrm⟩ := hscale (RareScale.radius γ d n) hnrad
    obtain ⟨ζ, hpure⟩ := hK k ((le_max_left K 2).trans hk)
    have hm2 : 2 ≤ seq k := ((le_max_right K 2).trans hk).trans (hseq.id_le k)
    let m := seq k
    have hbarrier := RareScale.barrier_le hγ (by omega : 1 ≤ d) hnprops.1 hrm
    have hll : 0 < log (log (n:ℝ)) := Real.log_pos (one_lt_log_of_three_le (by exact_mod_cast hn3))
    have hnpos : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hbad : {h | ¬ exp (c * (log (n:ℝ)/log (log (n:ℝ))) ^ exponentA d) ≤
        min (relaxationTime d n β h) (mixingTime d n β h)} ⊆
        {h | ∀ j : Candidate d n m, h ∉ islandOccurs (islandSigns ζ) (ε/m) H j} := by
      intro h hbad j hj
      apply hbad
      have hgap := gap_on_candidate_island (by omega : 1 ≤ d) (by omega : 1 ≤ m)
        h β H c₀ ε hβ.le hc₀ ζ rfl hpure hthreshold j hj
      apply times_lower_of_gap (d := d) (n := n) β h
        (A := c₀/2*(m:ℝ)^(d-1)) (L := c*RareScale.base n ^ exponentA d)
        (mul_nonneg hc.le (Real.rpow_nonneg hnprops.1.le _))
        ?_ hnabs (by simpa only [neg_mul] using hgap)
      change 2*(c₀/4*b*RareScale.base n ^ exponentA d) ≤ c₀/2*(m:ℝ)^(d-1)
      have hh := mul_le_mul_of_nonneg_left hbarrier (by positivity : 0 ≤ c₀/2)
      change b * RareScale.base n ^ exponentA d ≤ (m:ℝ)^(d-1) at hbarrier
      nlinarith only [hh]
    exact (measureReal_mono hbad).trans ((hno n m (islandSigns ζ) hm2).trans
      (candidate_error_bound hd0 hC.le hγ hγC hnpos hm1 hll hnprops.1 hmr hnprops.2.2
        (hnpack m (hmr.trans hnprops.2.2))))
  have hh := ENNReal.tendsto_ofReal hreal
  simp only [ENNReal.ofReal_zero] at hh
  convert hh using 1
  ext n
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

end Paper09.RFIM
