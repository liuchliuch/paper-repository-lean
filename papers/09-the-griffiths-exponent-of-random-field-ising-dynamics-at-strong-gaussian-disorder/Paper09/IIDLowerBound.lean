import Paper09.LowerBound
import Paper09.IIDIslands

/-! The general i.i.d. real-field extension in source paragraph S2.p14.
The tails are assumed only at one threshold H associated with the very same
pure-box barrier witness c₀; no all-threshold tail assumption is made. -/

open Finset BigOperators Classical Real Filter MeasureTheory
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Paper09.RFIM
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
local instance (priority := 2000) iidLowerPointDecEq (d : ℕ) : DecidableEq (Point d) := Classical.decEq _
local instance (priority := 2000) iidLowerSiteDecEq {d : ℕ} (A : Finset (Point d)) : DecidableEq ↥A := Classical.decEq _

/-- Proposition 2.1 for a general i.i.d. real field law, with an explicit
source pure-system witness and its single compatible shell threshold.
Only polynomial small-ball mass near zero and the two tails at this H enter
the disorder hypothesis, as stipulated in source paragraph S2.p14. -/
theorem proposition_2_1_iid_of_witness (d : ℕ) (β : ℝ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hd : 2 ≤ d) (hβ : 0 < β)
    (c₀ : ℝ) (seq : ℕ → ℕ) (hc₀ : 0 < c₀) (hseq : StrictMono seq)
    (hratio : Tendsto (fun k => (seq (k+1):ℝ)/(seq k:ℝ)) atTop (𝓝 1))
    (hslow : ∀ᶠ k in atTop, ∃ ζ : Point d → Spin,
      pureBoxGap d (seq k) β ζ ≤ exp (-c₀*(seq k:ℝ)^(d-1)))
    (H : ℝ) (hH : 0 < H)
    (hthreshold : 2*(d:ℝ)*qH H d β*(exp (8*(d:ℝ)*β)-1+8*(d:ℝ)*β) ≤ c₀/4)
    (hsmall : PolynomialSmallBall ν)
    (htailPos : 0 < ν.real (Set.Ici H)) (htailNeg : 0 < ν.real (Set.Iic (-H))) :
    ∃ c > 0, Tendsto (fun n : ℕ => (iidEnvironmentLaw d ν)
      {h | ¬ exp (c*(log (n:ℝ)/log (log (n:ℝ)))^exponentA d) ≤
        min (relaxationTime d n β h) (mixingTime d n β h)}) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp hslow
  let ε : ℝ := c₀/16
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C, hC, m₀, hno⟩ := no_iid_lattice_island_bound ν d ε H hε hsmall htailPos htailNeg
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
  letI : IsProbabilityMeasure (iidEnvironmentLaw d ν) := by unfold iidEnvironmentLaw; infer_instance
  have hreal : Tendsto (fun n : ℕ => (iidEnvironmentLaw d ν).real
      {h | ¬ exp (c * (log (n:ℝ) / log (log (n:ℝ))) ^ exponentA d) ≤
        min (relaxationTime d n β h) (mixingTime d n β h)}) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (RareScale.failure_tendsto d hd0) (Eventually.of_forall (fun _ => measureReal_nonneg))
    obtain ⟨R, hscale⟩ := dense_sequence_scale seq hseq hratio (max K (max 2 m₀))
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
    obtain ⟨ζ, hpure⟩ := hK k ((le_max_left K (max 2 m₀)).trans hk)
    have hm2 : 2 ≤ seq k := ((le_max_left 2 m₀).trans ((le_max_right K (max 2 m₀)).trans hk)).trans (hseq.id_le k)
    have hmm₀ : m₀ ≤ seq k :=
      ((le_max_right 2 m₀).trans ((le_max_right K (max 2 m₀)).trans hk)).trans (hseq.id_le k)
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
    exact (measureReal_mono hbad).trans ((hno n m (islandSigns ζ) hm2 hmm₀).trans
      (candidate_error_bound hd0 hC.le hγ hγC hnpos hm1 hll hnprops.1 hmr hnprops.2.2
        (hnpack m (hmr.trans hnprops.2.2))))
  have hh := ENNReal.tendsto_ofReal hreal
  simp only [ENNReal.ofReal_zero] at hh
  convert hh using 1
  ext n
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm


/-- The source-context packaging of S2.p14. The existential quantifiers bind
one common c₀, slow sequence, and H, so the tail hypothesis is never
strengthened to unbounded tails or to tails for every pure-box witness. -/
theorem proposition_2_1_iid (d : ℕ) (β : ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hd : 2 ≤ d) (hβ : 0 < β)
    (hsmall : PolynomialSmallBall ν)
    (hsource : ∃ (c₀ : ℝ) (seq : ℕ → ℕ) (H : ℝ),
      0 < c₀ ∧ StrictMono seq ∧
      Tendsto (fun k => (seq (k+1):ℝ)/(seq k:ℝ)) atTop (𝓝 1) ∧
      (∀ᶠ k in atTop, ∃ ζ : Point d → Spin,
        pureBoxGap d (seq k) β ζ ≤ exp (-c₀*(seq k:ℝ)^(d-1))) ∧
      0 < H ∧
      2*(d:ℝ)*qH H d β*(exp (8*(d:ℝ)*β)-1+8*(d:ℝ)*β) ≤ c₀/4 ∧
      0 < ν.real (Set.Ici H) ∧ 0 < ν.real (Set.Iic (-H))) :
    ∃ c > 0, Tendsto (fun n : ℕ => (iidEnvironmentLaw d ν)
      {h | ¬ exp (c*(log (n:ℝ)/log (log (n:ℝ)))^exponentA d) ≤
        min (relaxationTime d n β h) (mixingTime d n β h)}) atTop (𝓝 0) := by
  obtain ⟨c₀, seq, H, hc₀, hseq, hratio, hslow, hH, hthreshold, htailPos, htailNeg⟩ := hsource
  exact proposition_2_1_iid_of_witness d β ν hd hβ c₀ seq hc₀ hseq hratio hslow
    H hH hthreshold hsmall htailPos htailNeg

end Paper09.RFIM
