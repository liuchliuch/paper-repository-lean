import Paper08.ZeroFreeRatio
import Paper08.ComplexPathLog

/-! # A proved bound for an actual one-factor replacement path

The path data in the intermediate theorem below are differentiation and
integral identities. All phase and non-vanishing conclusions are derived from
the cardinality induction and the actual weighted-integral estimate.
-/
noncomputable section
namespace Paper08.ZeroFreeInduction
open Integral CubeMarginal ComplexSector

variable {n m r c : ℕ} {q θ : ℝ} {z : ℂ}

/-- Integrating the logarithmic derivative of one actual replacement gives
 phase change at most `2*|z|*q`. -/
theorem replacement_phase_of_path {k : ℕ} (ih : Good n m r c q z θ k)
    (hnz : ∀ N : Model n m r c q, ∀ U : Finset (Fin n), U.card ≤ k+1 →
      ∀ y ∈ cube n, N.partial U z y ≠ 0)
    (hq : 0 ≤ q) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hpow : (1 : ℝ)/2 ≤ Real.cos θ ^ (r-1))
    (M : Model n m r c q) (S : Finset (Fin n)) (hS : S.card ≤ k+1)
    {x : Fin n → ℝ} (hx : x ∈ cube n) (j : Fin n)
    (A : Finset (Fin m)) (e : Fin m) (heI : e ∈ M.incident j)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (P D : ℝ → ℂ) (hD : ContinuousOn D (Set.Icc 0 1))
    (hP : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt P (D t) t)
    (hPEq : ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1),
      P t = (M.replacement j A e ha hb t ht).partial S z x)
    (hDEq : ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1),
      D t = z * avg S (fun y => (M.delta j a b e y : ℂ) *
        (M.replacement j A e ha hb t ht).exponential z y) x)
    (hzero : P 0 = (M.freezeSet j A ha hb).partial S z x)
    (hone : P 1 = (M.freezeSet j (insert e A) ha hb).partial S z x) :
    Phase ((M.freezeSet j A ha hb).partial S z x)
      ((M.freezeSet j (insert e A) ha hb).partial S z x) (2 * ‖z‖ * q) := by
  have hpathnz : ∀ t ∈ Set.Icc (0 : ℝ) 1, P t ≠ 0 := by
    intro t ht
    rw [hPEq t ht]
    exact hnz _ S hS x hx
  have hratio : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖D t / P t‖ ≤ 2 * ‖z‖ * q := by
    intro t ht
    rw [hPEq t ht, hDEq t ht]
    exact weighted_ratio_le ih hq hθ0 hθ1 hpow
      (M.replacement j A e ha hb t ht) S ((M.scope e).erase j) hS
      (M.frozen_arity_le_sub_one j e heI) (M.continuous_delta j ha hb e)
      (fun y hy => M.abs_delta_le j ha hb e hy)
      (fun y hy w hw hyw => M.delta_depends j ha hb e hy hw hyw)
      hx (hnz _ S hS x hx)
  obtain ⟨w, hw, hwbound⟩ := ComplexPathLog.path_log_change hD hP hpathnz hratio
  apply phase_of_norm_log (w := w) _ hwbound
  simpa only [hzero, hone] using hw

end Paper08.ZeroFreeInduction
