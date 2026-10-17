import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.Linarith

/-! Joint continuity of an approximation homotopy at time zero (Theorem 4.4). -/
noncomputable section
open scoped Topology
namespace Paper17

/-- A continuous positive-time approximation with error less than time extends
continuously by the identity at nonpositive times. -/
theorem extend_positive_time {X : Type*} [MetricSpace X]
    (g : X × Set.Ioi (0 : ℝ) → X) (hg : Continuous g)
    (herr : ∀ p, dist (g p) p.1 < p.2.val) :
    ∃ H : X × ℝ → X, Continuous H ∧ (∀ x, H (x, 0) = x) ∧
      (∀ x t (ht : 0 < t), H (x,t) = g (x, ⟨t,ht⟩)) := by
  classical
  let H : X × ℝ → X := fun p => if ht : 0 < p.2 then g (p.1, ⟨p.2, ht⟩) else p.1
  have hposOn : ContinuousOn H {p | 0 < p.2} := by
    apply continuousOn_iff_continuous_restrict.mpr
    let e : {p : X × ℝ | 0 < p.2} → X × Set.Ioi (0 : ℝ) :=
      fun p => (p.val.1, ⟨p.val.2, p.property⟩)
    have he : Continuous e := (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
    have hc := hg.comp he
    convert hc using 1
    ext p
    change (if h : 0 < p.val.2 then g (p.val.1, ⟨p.val.2, h⟩) else p.val.1) = _
    exact dif_pos (show 0 < p.val.2 from p.property)
  have hnegOn : ContinuousOn H {p | p.2 < 0} := by
    apply continuous_fst.continuousOn.congr
    intro p hp
    change p.2 < 0 at hp
    simp only [H, dif_neg (not_lt_of_ge hp.le)]
  have hcont : Continuous H := by
    apply continuous_iff_continuousAt.mpr
    intro p
    rcases lt_trichotomy 0 p.2 with hp | hp | hp
    · exact hposOn.continuousAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)
    · have hp0 : p.2 = 0 := hp.symm
      rw [Metric.continuousAt_iff]
      intro ε hε
      refine ⟨ε / 3, by positivity, ?_⟩
      intro q hq
      have hx : dist q.1 p.1 ≤ dist q p := le_max_left _ _
      have ht : |q.2| ≤ dist q p := by
        simpa only [hp0, Real.dist_eq, sub_zero] using (show dist q.2 p.2 ≤ dist q p from le_max_right _ _)
      have hbound : dist (H q) q.1 ≤ |q.2| := by
        dsimp [H]
        split_ifs with hqt
        · exact (herr (q.1, ⟨q.2, hqt⟩)).le.trans (le_abs_self q.2)
        · simpa using abs_nonneg q.2
      have hHp : H p = p.1 := by simp [H, hp0]
      rw [hHp]
      calc dist (H q) p.1 ≤ dist (H q) q.1 + dist q.1 p.1 := dist_triangle _ _ _
        _ ≤ |q.2| + dist q.1 p.1 := add_le_add_right hbound _
        _ ≤ dist q p + dist q p := add_le_add ht hx
        _ < ε := by linarith
    · exact hnegOn.continuousAt ((isOpen_lt continuous_snd continuous_const).mem_nhds hp)
  exact ⟨H, hcont, fun x => by simp [H], fun x t ht => by simp [H, ht]⟩

end Paper17
