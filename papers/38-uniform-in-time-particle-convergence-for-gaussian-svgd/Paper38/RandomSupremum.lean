import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.NormNum

/-!
# Countable realization of the physical-time supremum

This proves the precise measurability reduction (2.6). The error is allowed to
be extended valued, so the argument does not silently assume integrability.
-/
namespace Paper38.RandomSupremum

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable def timeSup (f : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ t : {t : ℝ // 0 ≤ t}, f t

noncomputable def rationalSup (f : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ q : {q : ℚ // 0 ≤ q}, f q

/-- The supremum over all physical times is the supremum over nonnegative
rational times, using only continuity on the actual time domain. -/
theorem timeSup_eq_rationalSup {f : ℝ → ℝ≥0∞} (hf : ContinuousOn f (Ici 0)) :
    timeSup f = rationalSup f := by
  apply le_antisymm
  · apply iSup_le
    intro t
    obtain ⟨u, _hu, htu, hlim⟩ := Real.exists_seq_rat_strictAnti_tendsto t.val
    have hnonneg : ∀ n, (0 : ℚ) ≤ u n := by
      intro n
      have h : (0 : ℝ) ≤ (u n : ℝ) := t.property.trans (htu n).le
      exact_mod_cast h
    have hlim' : Tendsto (fun n => (u n : ℝ)) atTop (𝓝[Ici 0] t.val) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall (fun n =>
        t.property.trans (htu n).le)⟩
    apply le_of_tendsto (Filter.Tendsto.comp (hf t.val t.property) hlim')
    exact Eventually.of_forall fun n => le_iSup (fun q : {q : ℚ // 0 ≤ q} => f q)
      ⟨u n, hnonneg n⟩
  · apply iSup_le
    intro q
    have hq : (0 : ℝ) ≤ (q.val : ℝ) := by exact_mod_cast q.property
    exact le_iSup (fun t : {t : ℝ // 0 ≤ t} => f t) ⟨q.val, hq⟩

/-- Countably many measurable evaluations suffice for measurability of the
uncountable all-time supremum. -/
theorem measurable_timeSup {Ω : Type*} [MeasurableSpace Ω]
    {f : ℝ → Ω → ℝ≥0∞}
    (hcont : ∀ ω, ContinuousOn (fun t => f t ω) (Ici 0))
    (hmeas : ∀ q : {q : ℚ // 0 ≤ q}, Measurable (f q)) :
    Measurable (fun ω => timeSup (fun t => f t ω)) := by
  have heq : (fun ω => timeSup (fun t => f t ω)) =
      (fun ω => rationalSup (fun t => f t ω)) := by
    funext ω
    exact timeSup_eq_rationalSup (hcont ω)
  rw [heq]
  exact Measurable.iSup hmeas

/-- The 'in particular' interchange in Theorem 2.2 is always in this direction;
it needs no unjustified equality between expectation and supremum. -/
theorem supremum_lintegral_le_lintegral_supremum
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : ℝ → Ω → ℝ≥0∞) :
    (⨆ t : {t : ℝ // 0 ≤ t}, ∫⁻ ω, f t ω ∂P) ≤
      ∫⁻ ω, timeSup (fun t => f t ω) ∂P := by
  apply iSup_le
  intro t
  exact lintegral_mono fun ω => le_iSup (fun s : {s : ℝ // 0 ≤ s} => f s ω) t

end Paper38.RandomSupremum
