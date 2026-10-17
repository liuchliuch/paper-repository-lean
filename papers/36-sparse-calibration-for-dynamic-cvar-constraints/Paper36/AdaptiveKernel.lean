import Paper36.AdaptiveTapes
import Paper36.InfiniteTapes
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-! Adaptive row-stack equivalence with arbitrary measurable random choices.
The choice kernel may sample a continuous posterior model and retain it in the
history before choosing the next physical row. Thus this layer does not restrict
the learner to finitely many posterior models or deterministic policy choices. -/
namespace Paper36.AdaptiveKernel
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories Paper36.AdaptiveTapes

variable {S Row Hist : Type*} [Fintype S] [Fintype Row] [DecidableEq Row]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace Row] [DiscreteMeasurableSpace Row] [MeasurableSpace Hist]

/-- A random choice may retain arbitrary auxiliary information in the history.
In particular it may retain the episode's sampled continuous model and policy. -/
def tapedLValue (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    (update : Hist × (Row × S) → Hist) (payoff : Hist → ℝ≥0∞) :
    (n : ℕ) → Hist → Stack Row S n → ℝ≥0∞
  | 0, h, _ => payoff h
  | n+1, h, tape => ∫⁻ rh, tapedLValue choose update payoff n
      (update (rh.2, (rh.1, head rh.1 tape))) (remaining rh.1 tape) ∂choose h

/-- The corresponding original online experiment draws each transition from the
chosen true row, after all the learner's measurable random choices have occurred. -/
def onlineLValue (P : Row → Law S) (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    (update : Hist × (Row × S) → Hist) (payoff : Hist → ℝ≥0∞) : ℕ → Hist → ℝ≥0∞
  | 0, h => payoff h
  | n+1, h => ∫⁻ rh, ∫⁻ y, onlineLValue P choose update payoff n
      (update (rh.2, (rh.1, y))) ∂lawMeasure (P rh.1) ∂choose h

lemma measurable_tapedLValue (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    [IsSFiniteKernel choose] (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (payoff : Hist → ℝ≥0∞) (hpayoff : Measurable payoff) (n : ℕ) :
    Measurable (fun x : Hist × Stack Row S n => tapedLValue choose update payoff n x.1 x.2) := by
  induction n with
  | zero => exact hpayoff.comp measurable_fst
  | succ n ih =>
    let κ : ProbabilityTheory.Kernel (Hist × Stack Row S (n+1)) (Row × Hist) := choose.comap (Prod.fst : Hist × Stack Row S (n+1) → Hist) measurable_fst
    have hfinite : Measurable (fun x : (Hist × Stack Row S (n+1)) × (Row × Hist) =>
        (x.2.1, x.1.2)) := measurable_snd.fst.prodMk measurable_fst.snd
    have hh : Measurable (fun x : (Hist × Stack Row S (n+1)) × (Row × Hist) =>
        head x.2.1 x.1.2) := (measurable_of_countable (fun z : Row × Stack Row S (n+1) => head z.1 z.2)).comp hfinite
    have hr : Measurable (fun x : (Hist × Stack Row S (n+1)) × (Row × Hist) =>
        remaining x.2.1 x.1.2) := (measurable_of_countable (fun z : Row × Stack Row S (n+1) => remaining z.1 z.2)).comp hfinite
    have hu := hupdate.comp (measurable_snd.snd.prodMk (measurable_snd.fst.prodMk hh))
    have hf := ih.comp (hu.prodMk hr)
    have hfm : Measurable (Function.uncurry (fun (x : Hist × Stack Row S (n+1)) (rh : Row × Hist) =>
        tapedLValue choose update payoff n (update (rh.2, (rh.1, head rh.1 x.2))) (remaining rh.1 x.2))) := by
      simpa only [Function.comp_def] using hf
    exact hfm.lintegral_kernel_prod_right (κ := κ)

/-- The independent-head/unused-stack identity, for all measurable nonnegative
payoffs, including payoffs of continuous retained learner information. -/
theorem pop_lintegral (P : Row → Law S) (r : Row) (n : ℕ)
    (f : S → Stack Row S n → ℝ≥0∞)
    (hf : Measurable (fun z : Stack Row S n × S => f z.2 z.1)) :
    (∫⁻ tape, f (head r tape) (remaining r tape) ∂lawMeasure (stackLaw P (n+1))) =
      ∫⁻ y, ∫⁻ tape, f y tape ∂lawMeasure (stackLaw P n) ∂lawMeasure (P r) := by
  have hpop : Measurable (fun tape : Stack Row S (n+1) => (remaining r tape, head r tape)) :=
    measurable_of_countable _
  calc
    _ = ∫⁻ z, f z.2 z.1 ∂(lawMeasure (stackLaw P (n+1))).map
        (fun tape => (remaining r tape, head r tape)) := (lintegral_map hf hpop).symm
    _ = _ := by
      rw [pop_law]
      exact lintegral_prod_symm' _ hf

/-- Full finite adaptive coupling for arbitrary history kernels. Only the online
Markov transition rows and the actual raw product stacks enter this theorem. -/
theorem adaptive_kernel_coupling (P : Row → Law S)
    (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsSFiniteKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (payoff : Hist → ℝ≥0∞) (hpayoff : Measurable payoff) (n : ℕ) (h : Hist) :
    (∫⁻ tape, tapedLValue choose update payoff n h tape ∂lawMeasure (stackLaw P n)) =
      onlineLValue P choose update payoff n h := by
  induction n generalizing h with
  | zero => simp only [tapedLValue, onlineLValue, lintegral_const, measure_univ, mul_one]
  | succ n ih =>
    have hfinite : Measurable (fun x : Stack Row S (n+1) × (Row × Hist) => (x.2.1, x.1)) :=
      measurable_snd.fst.prodMk measurable_fst
    have hh := (measurable_of_countable (fun z : Row × Stack Row S (n+1) => head z.1 z.2)).comp hfinite
    have hr := (measurable_of_countable (fun z : Row × Stack Row S (n+1) => remaining z.1 z.2)).comp hfinite
    have hu := hupdate.comp (measurable_snd.snd.prodMk (measurable_snd.fst.prodMk hh))
    have hf := (measurable_tapedLValue choose update hupdate payoff hpayoff n).comp (hu.prodMk hr)
    change (∫⁻ tape, ∫⁻ rh, tapedLValue choose update payoff n
      (update (rh.2, (rh.1, head rh.1 tape))) (remaining rh.1 tape) ∂choose h
      ∂lawMeasure (stackLaw P (n+1))) = _
    rw [lintegral_lintegral_swap (μ := lawMeasure (stackLaw P (n+1))) (ν := choose h)
      (f := fun tape rh => tapedLValue choose update payoff n
        (update (rh.2, (rh.1, head rh.1 tape))) (remaining rh.1 tape)) hf.aemeasurable]
    change (∫⁻ rh, ∫⁻ tape, tapedLValue choose update payoff n
      (update (rh.2, (rh.1, head rh.1 tape))) (remaining rh.1 tape)
      ∂lawMeasure (stackLaw P (n+1)) ∂choose h) = _
    unfold onlineLValue
    apply lintegral_congr_ae
    apply ae_of_all
    intro rh
    have hinner : Measurable (fun z : Stack Row S n × S =>
        tapedLValue choose update payoff n (update (rh.2, (rh.1, z.2))) z.1) := by
      have hh : Measurable (fun z : Stack Row S n × S => (update (rh.2, (rh.1, z.2)), z.1)) :=
        (hupdate.comp (measurable_const.prodMk (measurable_const.prodMk measurable_snd))).prodMk measurable_fst
      simpa only [Function.comp_def] using
        (measurable_tapedLValue choose update hupdate payoff hpayoff n).comp hh
    dsimp only
    rw [pop_lintegral P rh.1 n
      (fun y tape => tapedLValue choose update payoff n (update (rh.2, (rh.1, y))) tape) hinner]
    apply lintegral_congr_ae
    exact ae_of_all _ fun y => ih (update (rh.2, (rh.1, y)))

/-- The retained learner history and the complete unused stacks are tested jointly. -/
def residualLValue (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    (update : Hist × (Row × S) → Hist) (L : ℕ) (payoff : Hist × Stack Row S L → ℝ≥0∞) :
    (n : ℕ) → Hist → Stack Row S (L+n) → ℝ≥0∞
  | 0, h, tape => payoff (h,tape)
  | n+1, h, tape => ∫⁻ rh, residualLValue choose update L payoff n
      (update (rh.2, (rh.1, head rh.1 tape))) (remaining rh.1 tape) ∂choose h

lemma measurable_residualLValue (choose : ProbabilityTheory.Kernel Hist (Row × Hist))
    [IsSFiniteKernel choose] (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (L : ℕ) (payoff : Hist × Stack Row S L → ℝ≥0∞) (hpayoff : Measurable payoff) (n : ℕ) :
    Measurable (fun x : Hist × Stack Row S (L+n) => residualLValue choose update L payoff n x.1 x.2) := by
  induction n with
  | zero => exact hpayoff
  | succ n ih =>
    let κ : ProbabilityTheory.Kernel (Hist × Stack Row S (L+n+1)) (Row × Hist) := choose.comap (Prod.fst : Hist × Stack Row S (L+n+1) → Hist) measurable_fst
    have hfinite : Measurable (fun x : (Hist × Stack Row S (L+n+1)) × (Row × Hist) =>
        (x.2.1, x.1.2)) := measurable_snd.fst.prodMk measurable_fst.snd
    have hh : Measurable (fun x : (Hist × Stack Row S (L+n+1)) × (Row × Hist) =>
        head x.2.1 x.1.2) := (measurable_of_countable (fun z : Row × Stack Row S (L+n+1) => head z.1 z.2)).comp hfinite
    have hr : Measurable (fun x : (Hist × Stack Row S (L+n+1)) × (Row × Hist) =>
        remaining x.2.1 x.1.2) := (measurable_of_countable (fun z : Row × Stack Row S (L+n+1) => remaining z.1 z.2)).comp hfinite
    have hu := hupdate.comp (measurable_snd.snd.prodMk (measurable_snd.fst.prodMk hh))
    have hf := ih.comp (hu.prodMk hr)
    have hfm : Measurable (Function.uncurry (fun (x : Hist × Stack Row S (L+n+1)) (rh : Row × Hist) =>
        residualLValue choose update L payoff n (update (rh.2, (rh.1, head rh.1 x.2))) (remaining rh.1 x.2))) := by
      simpa only [Function.comp_def] using hf
    exact hfm.lintegral_kernel_prod_right (κ := κ)

/-- Arbitrary measurable learner choices preserve the exact joint law of all
unused rows: terminal history has the online law and residual rows retain their
independent original product law. -/
theorem adaptive_kernel_unused_independent (P : Row → Law S)
    (choose : ProbabilityTheory.Kernel Hist (Row × Hist)) [IsSFiniteKernel choose]
    (update : Hist × (Row × S) → Hist) (hupdate : Measurable update)
    (L : ℕ) (payoff : Hist × Stack Row S L → ℝ≥0∞) (hpayoff : Measurable payoff) (n : ℕ) (h : Hist) :
    (∫⁻ tape, residualLValue choose update L payoff n h tape ∂lawMeasure (stackLaw P (L+n))) =
      onlineLValue P choose update (fun h => ∫⁻ tape, payoff (h,tape) ∂lawMeasure (stackLaw P L)) n h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    have hfinite : Measurable (fun x : Stack Row S (L+n+1) × (Row × Hist) => (x.2.1, x.1)) :=
      measurable_snd.fst.prodMk measurable_fst
    have hh := (measurable_of_countable (fun z : Row × Stack Row S (L+n+1) => head z.1 z.2)).comp hfinite
    have hr := (measurable_of_countable (fun z : Row × Stack Row S (L+n+1) => remaining z.1 z.2)).comp hfinite
    have hu := hupdate.comp (measurable_snd.snd.prodMk (measurable_snd.fst.prodMk hh))
    have hf := (measurable_residualLValue choose update hupdate L payoff hpayoff n).comp (hu.prodMk hr)
    change (∫⁻ tape, ∫⁻ rh, residualLValue choose update L payoff n
      (update (rh.2, (rh.1, head rh.1 tape))) (remaining rh.1 tape) ∂choose h
      ∂lawMeasure (stackLaw P (L+n+1))) = _
    rw [lintegral_lintegral_swap (μ := lawMeasure (stackLaw P (L+n+1))) (ν := choose h)
      (f := fun tape rh => residualLValue choose update L payoff n
        (update (rh.2, (rh.1, head rh.1 tape))) (remaining rh.1 tape)) hf.aemeasurable]
    change (∫⁻ rh, ∫⁻ tape, residualLValue choose update L payoff n
      (update (rh.2, (rh.1, head rh.1 tape))) (remaining rh.1 tape)
      ∂lawMeasure (stackLaw P (L+n+1)) ∂choose h) = _
    unfold onlineLValue
    apply lintegral_congr_ae
    apply ae_of_all
    intro rh
    have hinner : Measurable (fun z : Stack Row S (L+n) × S =>
        residualLValue choose update L payoff n (update (rh.2, (rh.1, z.2))) z.1) := by
      have hh : Measurable (fun z : Stack Row S (L+n) × S => (update (rh.2, (rh.1, z.2)), z.1)) :=
        (hupdate.comp (measurable_const.prodMk (measurable_const.prodMk measurable_snd))).prodMk measurable_fst
      simpa only [Function.comp_def] using
        (measurable_residualLValue choose update hupdate L payoff hpayoff n).comp hh
    dsimp only
    rw [pop_lintegral P rh.1 (L+n)
      (fun y tape => residualLValue choose update L payoff n (update (rh.2, (rh.1, y))) tape) hinner]
    apply lintegral_congr_ae
    exact ae_of_all _ fun y => ih (update (rh.2, (rh.1, y)))

end
end Paper36.AdaptiveKernel
