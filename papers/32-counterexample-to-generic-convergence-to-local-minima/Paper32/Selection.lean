import Paper32.Subdifferential
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.Compact

open Set Filter Topology MeasureTheory Metric
open scoped NNReal

noncomputable section
namespace Paper32

/-- Coefficients of a continuous real differential in the paper's coordinate basis. -/
def differentialCoefficients (p : Point →L[ℝ] ℝ) : Point := (p (1,0), p (0,1))

theorem linCLM_differentialCoefficients (p : Point →L[ℝ] ℝ) :
    linCLM (differentialCoefficients p) = p := by
  apply ContinuousLinearMap.ext
  intro q
  have heq : q = q.1 • ((1,0) : Point) + q.2 • ((0,1) : Point) := by ext <;> simp
  change p (1,0) * q.1 + p (0,1) * q.2 = p q
  have hp : p q = q.1 * p (1,0) + q.2 * p (0,1) := by
    calc
      p q = p (q.1 • ((1,0) : Point) + q.2 • ((0,1) : Point)) := congrArg p heq
      _ = _ := by rw [map_add, map_smul, map_smul]; rfl
  linarith


theorem gradient_norm_le_lipschitz {f : Point → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) {z w : Point} (hw : HasFDerivAt f (linCLM w) z) :
    ‖w‖ ≤ C := by
  have hn := hw.le_of_lipschitz hf
  have h1 := (linCLM w).le_opNorm ((1,0) : Point)
  have h2 := (linCLM w).le_opNorm ((0,1) : Point)
  norm_num [linCLM, lin, Prod.norm_def, Real.norm_eq_abs] at h1 h2 ⊢
  exact ⟨h1.trans hn, h2.trans hn⟩

/-- Every point has a reachable gradient, using Rademacher and a bounded-gradient subsequence. -/
theorem gradientLimits_nonempty_of_lipschitz {f : Point → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (z : Point) : (gradientLimits f z).Nonempty := by
  have hdense : Dense {q | DifferentiableAt ℝ f q} :=
    Measure.dense_of_ae (hf.ae_differentiableAt (μ := (Measure.addHaar : Measure Point)))
  obtain ⟨a, ha, haz⟩ := mem_closure_iff_seq_limit.mp (hdense z)
  let b : ℕ → Point := fun n => differentialCoefficients (fderiv ℝ f (a n))
  have hb : ∀ n, HasFDerivAt f (linCLM (b n)) (a n) := by
    intro n
    rw [show linCLM (b n) = fderiv ℝ f (a n) from linCLM_differentialCoefficients _]
    exact (ha n).hasFDerivAt
  obtain ⟨w, hw, φ, hφ, hbw⟩ := tendsto_subseq_of_bounded
    (Metric.isBounded_closedBall (x := (0:Point)) (r := (C:ℝ)))
    (fun n => show b n ∈ Metric.closedBall (0:Point) C by
      simpa [Metric.mem_closedBall, dist_zero_right] using gradient_norm_le_lipschitz hf (hb n))
  refine ⟨w, a ∘ φ, b ∘ φ, haz.comp hφ.tendsto_atTop, hbw, ?_⟩
  exact fun n => hb (φ n)

theorem gradientLimits_subset_closedBall {f : Point → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (z : Point) :
    gradientLimits f z ⊆ Metric.closedBall (0:Point) C := by
  rintro w ⟨a,b,ha,hb,hd⟩
  apply isClosed_closedBall.mem_of_tendsto hb
  exact Eventually.of_forall fun n => by
    simpa [Metric.mem_closedBall, dist_zero_right] using gradient_norm_le_lipschitz hf (hd n)

theorem clarke_nonempty_of_lipschitz {f : Point → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (z : Point) : (clarkeSubdiff f z).Nonempty := by
  obtain ⟨w,hw⟩ := gradientLimits_nonempty_of_lipschitz hf z
  exact ⟨w, subset_closure (subset_convexHull ℝ _ hw)⟩

theorem clarke_convex (f : Point → ℝ) (z : Point) : Convex ℝ (clarkeSubdiff f z) :=
  (convex_convexHull ℝ _).closure

theorem clarke_compact_of_lipschitz {f : Point → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (z : Point) : IsCompact (clarkeSubdiff f z) := by
  have hb : Bornology.IsBounded (gradientLimits f z) :=
    (Metric.isBounded_closedBall (x := (0:Point)) (r := (C:ℝ))).subset
      (gradientLimits_subset_closedBall hf z)
  exact (isBounded_convexHull.mpr hb).isCompact_closure

/-- Squared Euclidean norm, independent of the ambient product norm convention. -/
def euclideanNormSq (w : Point) : ℝ := w.1 ^ 2 + w.2 ^ 2

theorem continuous_euclideanNormSq : Continuous euclideanNormSq := by unfold euclideanNormSq; fun_prop

theorem unique_euclideanMin_of_compact_convex {s : Set Point} (hs : IsCompact s)
    (hne : s.Nonempty) (hc : Convex ℝ s) :
    ∃! w : Point, w ∈ s ∧ ∀ u ∈ s, euclideanNormSq w ≤ euclideanNormSq u := by
  obtain ⟨w,hw,hm⟩ := hs.exists_isMinOn hne continuous_euclideanNormSq.continuousOn
  refine ⟨w, ⟨hw, hm⟩, ?_⟩
  rintro u ⟨hu, hmu⟩
  have hmid : (1/2:ℝ) • w + (1/2:ℝ) • u ∈ s := hc hw hu (by norm_num) (by norm_num) (by norm_num)
  have heq := le_antisymm (hm hu) (hmu w hw)
  have hineq := hm hmid
  change euclideanNormSq w ≤ euclideanNormSq ((1/2:ℝ) • w + (1/2:ℝ) • u) at hineq
  simp only [euclideanNormSq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at heq hineq
  have hsq : (w.1 - u.1)^2 + (w.2 - u.2)^2 ≤ 0 := by nlinarith
  have h1 : w.1 = u.1 := by nlinarith [sq_nonneg (w.2-u.2), sq_nonneg (w.1-u.1)]
  have h2 : w.2 = u.2 := by nlinarith [sq_nonneg (w.2-u.2), sq_nonneg (w.1-u.1)]
  exact Prod.ext h1.symm h2.symm

theorem lipschitz_tilt (v : Point) : LipschitzWith (8 + ‖v.1‖₊ + ‖v.2‖₊) (tilt v) := by
  have h1 : LipschitzWith ‖v.1‖₊ (fun q : Point => v.1*q.1) := by
    simpa using (lipschitzWith_smul v.1 (β := ℝ)).comp (LipschitzWith.prod_fst (α := ℝ) (β := ℝ))
  have h2 : LipschitzWith ‖v.2‖₊ (fun q : Point => v.2*q.2) := by
    simpa using (lipschitzWith_smul v.2 (β := ℝ)).comp (LipschitzWith.prod_snd (α := ℝ) (β := ℝ))
  simpa [tilt,lin, add_assoc] using lipschitz_F.sub (h1.add h2)

theorem clarke_tilt_nonempty (v z : Point) : (clarkeSubdiff (tilt v) z).Nonempty :=
  clarke_nonempty_of_lipschitz (lipschitz_tilt v) z

theorem clarke_tilt_compact (v z : Point) : IsCompact (clarkeSubdiff (tilt v) z) :=
  clarke_compact_of_lipschitz (lipschitz_tilt v) z

theorem clarke_tilt_unique_euclideanMin (v z : Point) :
    ∃! w : Point, w ∈ clarkeSubdiff (tilt v) z ∧
      ∀ u ∈ clarkeSubdiff (tilt v) z, euclideanNormSq w ≤ euclideanNormSq u :=
  unique_euclideanMin_of_compact_convex (clarke_tilt_compact v z)
    (clarke_tilt_nonempty v z) (clarke_convex _ _)

/-- The paper's concrete minimum-Euclidean-norm Clarke selection, defined at every point. -/
def minimumNormSelection (v z : Point) : Point :=
  Classical.choose (clarke_tilt_unique_euclideanMin v z).exists

theorem minimumNormSelection_mem (v z : Point) :
    minimumNormSelection v z ∈ clarkeSubdiff (tilt v) z :=
  (Classical.choose_spec (clarke_tilt_unique_euclideanMin v z).exists).1

theorem minimumNormSelection_min (v z u : Point) (hu : u ∈ clarkeSubdiff (tilt v) z) :
    euclideanNormSq (minimumNormSelection v z) ≤ euclideanNormSq u :=
  (Classical.choose_spec (clarke_tilt_unique_euclideanMin v z).exists).2 u hu

theorem euclideanNormSq_nonneg (w : Point) : 0 ≤ euclideanNormSq w :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem euclideanNorm_le_iff (u w : Point) :
    euclideanNorm u ≤ euclideanNorm w ↔ euclideanNormSq u ≤ euclideanNormSq w :=
  Real.sqrt_le_sqrt_iff (euclideanNormSq_nonneg w)

theorem minimumNormSelection_min_norm (v z u : Point) (hu : u ∈ clarkeSubdiff (tilt v) z) :
    euclideanNorm (minimumNormSelection v z) ≤ euclideanNorm u :=
  (euclideanNorm_le_iff _ _).mpr (minimumNormSelection_min v z u hu)

theorem minimumNormSelection_unique_norm (v z u : Point)
    (hu : u ∈ clarkeSubdiff (tilt v) z)
    (hmin : ∀ w ∈ clarkeSubdiff (tilt v) z, euclideanNorm u ≤ euclideanNorm w) :
    u = minimumNormSelection v z := by
  apply (clarke_tilt_unique_euclideanMin v z).unique
  · exact ⟨hu, fun w hw => (euclideanNorm_le_iff _ _).mp (hmin w hw)⟩
  · exact ⟨minimumNormSelection_mem v z, minimumNormSelection_min v z⟩

end Paper32
