import Paper29.ProcessTools
import Paper29.Leverage
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
open scoped BigOperators Classical
namespace Paper29.WeightConstruction
open ProcessTools

def PositiveWeights (n : ℕ) := {w : Fin n → ℝ // ∀ i, 0 < w i}

instance {n : ℕ} : CoeFun (PositiveWeights n) (fun _ => Fin n → ℝ) := ⟨Subtype.val⟩

def logDist {n : ℕ} (u w : PositiveWeights n) : ℝ :=
  supremum (fun i => |Real.log (u i) - Real.log (w i)|)

theorem logDist_bdd {n : ℕ} (u w : PositiveWeights n) :
    BddAbove (Set.range (fun i => |Real.log (u i) - Real.log (w i)|)) :=
  (Set.finite_range _).bddAbove

theorem coordinate_le_logDist {n : ℕ} (u w : PositiveWeights n) (i : Fin n) :
    |Real.log (u i) - Real.log (w i)| ≤ logDist u w := le_supremum _ (logDist_bdd u w) i

theorem logDist_le {n : ℕ} [Nonempty (Fin n)] (u w : PositiveWeights n) {b : ℝ}
    (h : ∀ i, |Real.log (u i) - Real.log (w i)| ≤ b) : logDist u w ≤ b :=
  supremum_le _ h

theorem logDist_nonneg {n : ℕ} [Nonempty (Fin n)] (u w : PositiveWeights n) :
    0 ≤ logDist u w := supremum_nonneg _ (logDist_bdd u w) (fun _ => abs_nonneg _)

theorem logDist_symm {n : ℕ} (u w : PositiveWeights n) : logDist u w = logDist w u := by
  unfold logDist
  congr 1
  funext i
  exact abs_sub_comm _ _

theorem logDist_triangle {n : ℕ} [Nonempty (Fin n)] (u v w : PositiveWeights n) :
    logDist u w ≤ logDist u v + logDist v w := by
  apply logDist_le
  intro i
  exact (abs_sub_le (Real.log (u i)) (Real.log (v i)) (Real.log (w i))).trans
    (add_le_add (coordinate_le_logDist u v i) (coordinate_le_logDist v w i))

def rescale {n : ℕ} (c : ℝ) (hc : 0 < c) (w : PositiveWeights n) : PositiveWeights n :=
  ⟨fun i => c * w i, fun i => mul_pos hc (w.property i)⟩

theorem logDist_rescale_left {n : ℕ} [Nonempty (Fin n)]
    (c : ℝ) (hc : 0 < c) (u w : PositiveWeights n) :
    logDist (rescale c hc u) w ≤ logDist u w + |Real.log c| := by
  apply logDist_le
  intro i
  change |Real.log (c*u i) - Real.log (w i)| ≤ _
  rw [Real.log_mul (ne_of_gt hc) (ne_of_gt (u.property i))]
  have he : Real.log c + Real.log (u i) - Real.log (w i) =
      (Real.log (u i) - Real.log (w i)) + Real.log c := by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add_right (coordinate_le_logDist u w i) _)

/-- Precisely disclosed external input: Jambulapati–Lee–Liu–Sidford,
arXiv:2311.18145v1, Lemma2.6 (Loewner inverse monotonicity). This is the
loss-independent radius-squared stability statement. It assumes no Huber
iteration, finite stopping, scale scheme, scores or covering conclusion. -/
def RadiusLogNonexpansive : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin n) (Fin d) ℝ), A.rank = d →
    (∀ i, A i ≠ 0) → ∀ u w : PositiveWeights n, ∀ i,
      |Real.log (Leverage.radiusSq A u i) - Real.log (Leverage.radiusSq A w i)| ≤ logDist u w

end Paper29.WeightConstruction
