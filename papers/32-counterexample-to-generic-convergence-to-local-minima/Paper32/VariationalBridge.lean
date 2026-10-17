import Paper32.ClarkeBridge

open Set Filter Topology
namespace Paper32

/-- Locality of the actual regular-subgradient inequality. -/
lemma frechetSubgradient_congr_of_eventuallyEq {f h : Point → ℝ} {z w : Point}
    (heq : f =ᶠ[𝓝 z] h) : FrechetSubgradient f z w ↔ FrechetSubgradient h z w := by
  have impl : ∀ f h : Point → ℝ, f =ᶠ[𝓝 z] h →
      FrechetSubgradient f z w → FrechetSubgradient h z w := by
    intro f h heq hw ε hε
    obtain ⟨δ,hδ,hδbound⟩ := hw ε hε
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp heq
    refine ⟨min δ r, lt_min hδ hr, ?_⟩
    intro u hu
    have huδ : ‖u‖ < δ := lt_of_lt_of_le hu (min_le_left _ _)
    have hur : ‖u‖ < r := lt_of_lt_of_le hu (min_le_right _ _)
    have hval : f (z+u) = h (z+u) := hball (by simpa [dist_eq_norm] using hur)
    rw [← heq.self_of_nhds, ← hval]
    exact hδbound u huδ
  exact ⟨impl f h heq, impl h f heq.symm⟩

lemma limitingSubdiff_congr_of_eventuallyEq {f h : Point → ℝ} {z : Point}
    (heq : f =ᶠ[𝓝 z] h) : limitingSubdiff f z = limitingSubdiff h z := by
  have incl : ∀ f h : Point → ℝ, f =ᶠ[𝓝 z] h → limitingSubdiff f z ⊆ limitingSubdiff h z := by
    intro f h heq w hw
    obtain ⟨a,b,ha,hfa,hb,hd⟩ := hw
    have hlocal : ∀ᶠ n in atTop, f =ᶠ[𝓝 (a n)] h := ha.eventually heq.eventually_nhds
    obtain ⟨N,hN⟩ := eventually_atTop.mp hlocal
    have hfeq : (fun n => f (a (n+N))) =ᶠ[atTop] (fun n => h (a (n+N))) := by
      exact Filter.Eventually.of_forall (fun n => (hN (n+N) (by omega)).self_of_nhds)
    refine ⟨fun n => a (n+N), fun n => b (n+N),
      ha.comp (tendsto_add_atTop_nat N), ?_, hb.comp (tendsto_add_atTop_nat N), ?_⟩
    · have hf := (hfa.comp (tendsto_add_atTop_nat N)).congr' hfeq
      simpa only [Function.comp_apply, heq.self_of_nhds] using hf
    · intro n
      exact (frechetSubgradient_congr_of_eventuallyEq (hN (n+N) (by omega))).mp (hd (n+N))
  exact Subset.antisymm (incl f h heq) (incl h f heq.symm)

lemma frechet_sub_lin {f : Point → ℝ} {z w v : Point} :
    FrechetSubgradient (fun q => f q - lin v q) z w ↔
      FrechetSubgradient f z (w + v) := by
  have halg : ∀ u ε, f z - lin v z + lin w u - ε * ‖u‖ ≤ f (z+u) - lin v (z+u) ↔
      f z + lin (w+v) u - ε * ‖u‖ ≤ f (z+u) := by
    intro u ε
    simp only [lin, Prod.fst_add, Prod.snd_add]
    constructor <;> intro h <;> nlinarith [h]
  unfold FrechetSubgradient
  simp only [halg]

lemma limiting_sub_lin {f : Point → ℝ} {z w v : Point} :
    w ∈ limitingSubdiff (fun q => f q - lin v q) z ↔
      w + v ∈ limitingSubdiff f z := by
  have hc : Continuous (lin v) := by unfold lin; fun_prop
  constructor
  · rintro ⟨a,b,ha,hfa,hb,hd⟩
    refine ⟨a,fun n => b n+v,ha,?_,?_,fun n => frechet_sub_lin.mp (hd n)⟩
    · have hf := hfa.add (hc.continuousAt.tendsto.comp ha)
      simpa only [Function.comp_apply, sub_add_cancel] using hf
    · simpa using hb.add_const v
  · rintro ⟨a,b,ha,hfa,hb,hd⟩
    refine ⟨a,fun n => b n-v,ha,?_,?_,?_⟩
    · exact hfa.sub (hc.continuousAt.tendsto.comp ha)
    · simpa using hb.sub_const v
    · intro n
      apply frechet_sub_lin.mpr
      simpa using hd n

/-- Translation of genuine gradient-limit values by a linear tilt. -/
lemma gradientLimits_sub_lin_mem {f : Point → ℝ} {z w v : Point}
    (hw : w ∈ gradientLimits f z) :
    w-v ∈ gradientLimits (fun q => f q-lin v q) z := by
  obtain ⟨a,b,ha,hb,hd⟩ := hw
  refine ⟨a,fun n => b n-v,ha,hb.sub_const v,?_⟩
  intro n
  have hlin : linCLM (b n-v) = linCLM (b n)-linCLM v := by
    apply ContinuousLinearMap.ext
    intro q
    change lin (b n-v) q = lin (b n) q-lin v q
    simp only [lin, Prod.fst_sub, Prod.snd_sub]
    ring
  rw [hlin]
  exact (hd n).sub ((linCLM v).hasFDerivAt)

/-- Tilting translates the standard Clarke subdifferential (forward inclusion). -/
theorem clarke_sub_lin_mem {f : Point → ℝ} {z w v : Point}
    (hw : w ∈ clarkeSubdiff f z) :
    w-v ∈ clarkeSubdiff (fun q => f q-lin v q) z := by
  let S : Set Point := {u | u-v ∈ clarkeSubdiff (fun q => f q-lin v q) z}
  have hclosed : IsClosed S := isClosed_closure.preimage (continuous_id.sub continuous_const)
  have hconv : Convex ℝ S := by
    intro a ha b hb s t hs ht hst
    change s • a + t • b - v ∈ clarkeSubdiff (fun q => f q-lin v q) z
    have halg : s • a+t • b-v = s • (a-v)+t • (b-v) := by
      ext
      · simp only [Prod.fst_add,Prod.fst_sub,Prod.smul_fst,smul_eq_mul]
        nlinarith [congrArg (fun r : ℝ => r*v.1) hst]
      · simp only [Prod.snd_add,Prod.snd_sub,Prod.smul_snd,smul_eq_mul]
        nlinarith [congrArg (fun r : ℝ => r*v.2) hst]
    rw [halg]
    exact (convex_convexHull ℝ (gradientLimits (fun q => f q-lin v q) z)).closure ha hb hs ht hst
  have hbase : gradientLimits f z ⊆ S := by
    intro u hu
    exact subset_closure (subset_convexHull ℝ _ (gradientLimits_sub_lin_mem hu))
  exact closure_minimal (convexHull_min hbase hconv) hclosed hw

end Paper32

namespace Paper32
open Set Filter Topology

lemma frechet_add_const {f : Point → ℝ} {z w : Point} (c : ℝ) :
    FrechetSubgradient (fun q => f q+c) z w ↔ FrechetSubgradient f z w := by
  unfold FrechetSubgradient
  simp only [add_le_add_iff_right, show ∀ a b d : ℝ, a+c+b-d=(a+b-d)+c by intros; ring]

lemma limitingSubdiff_add_const (f : Point → ℝ) (c : ℝ) (z : Point) :
    limitingSubdiff (fun q => f q+c) z = limitingSubdiff f z := by
  ext w
  constructor
  · rintro ⟨a,b,ha,hfa,hb,hd⟩
    refine ⟨a,b,ha,?_,hb,fun n => (frechet_add_const c).mp (hd n)⟩
    simpa using hfa.sub_const c
  · rintro ⟨a,b,ha,hfa,hb,hd⟩
    exact ⟨a,b,ha,hfa.add_const c,hb,fun n => (frechet_add_const c).mpr (hd n)⟩

/-- Exact limiting geometry for the coercive extension, as standard subdifferentials. -/
theorem limiting_F_zero : limitingSubdiff F 0 = limitingSegments := by
  rw [limitingSubdiff_congr_of_eventuallyEq (F_eventually_eq_core (by norm_num)),
    limitingSubdiff_add_const, limiting_g_zero]

theorem clarke_F_zero : clarkeSubdiff F 0 = convexHull ℝ sectorGradients := by
  rw [clarkeSubdiff_congr_of_eventuallyEq (F_eventually_eq_core (by norm_num)),
    clarkeSubdiff_add_const, clarke_g_zero]

/-- The exact open-tilt criticality gap, with a true local-minimum predicate. -/
theorem criticality_gap {v : Point} (hv : U v) :
    (0 : Point) ∈ clarkeSubdiff (tilt v) 0 ∧
    (0 : Point) ∉ limitingSubdiff (tilt v) 0 ∧ ¬ IsLocalMin (tilt v) 0 := by
  have hcv : v ∈ clarkeSubdiff F 0 := by
    rw [clarkeSubdiff_congr_of_eventuallyEq (F_eventually_eq_core (by norm_num)), clarkeSubdiff_add_const]
    exact rectangle_subset_clarke_g_zero (by linarith [hv.1]) (by linarith [hv.2])
  refine ⟨?_,?_,not_localMin_tilt hv⟩
  · simpa only [tilt, sub_self] using (clarke_sub_lin_mem (v := v) hcv)
  · intro h
    have hc : v ∈ limitingSubdiff F 0 := by
      simpa only [zero_add] using (limiting_sub_lin.mp h)
    rw [limiting_F_zero] at hc
    rcases hc with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · linarith [hv.1]
    · linarith [hv.2]

/-- Every local Clarke value has the explicit coordinate bounds needed at time zero. -/
theorem clarke_tilt_coordinate_bound {v z w : Point} (hz : l1 z < 4)
    (hw : w ∈ clarkeSubdiff (tilt v) z) : |w.1+v.1| ≤ 7 ∧ |w.2+v.2| ≤ 2 := by
  have hh := clarke_sub_lin_mem (v := -v) hw
  have heq : (fun q => tilt v q-lin (-v) q) = F := by
    funext q
    simp [tilt,lin]
    ring
  rw [heq, clarkeSubdiff_congr_of_eventuallyEq (F_eventually_eq_core hz), clarkeSubdiff_add_const] at hh
  simpa using clarke_g_coordinate_bound hh

end Paper32
