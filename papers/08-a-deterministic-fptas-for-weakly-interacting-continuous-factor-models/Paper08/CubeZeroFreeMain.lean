import Paper08.ZeroFreeInduction
import Paper08.CubeZeroFreeParameters
import Paper08.FPTASCorrectness

/-! # Nonvanishing from the original finite-cube model promises

The induction is uniform over actual bounded continuous scoped potentials.
Its intermediate non-cancellation and phase assertions are proved here,
rather than supplied as model or algorithm input certificates.
-/
noncomputable section
open scoped BigOperators
namespace Paper08.ZeroFreeInduction
open Integral CubeMarginal ComplexSector

variable {n m r c : ℕ} {q θ : ℝ} {z : ℂ}

lemma good_zero (hq : 0 ≤ q) (hbudget : 2*(c:ℝ)*‖z‖*q ≤ θ) :
    Good n m r c q z θ 0 := by
  intro M S hS
  have hS0 : S = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hS)
  subst S
  constructor
  · intro x hx
    simpa [Model.partial] using M.exponential_ne_zero z x
  · intro x hx j hj a ha b hb
    have h := M.phase_exponential_update hq z hx j ha hb
    have hn : 0 ≤ (c:ℝ)*‖z‖*q :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) hq
    have hbnd : ‖z‖*((c:ℝ)*q) ≤ θ := by nlinarith
    simpa [Model.partial] using h.mono hbnd

/-- Every partial expectation is nonzero and has the coordinate phase bound.
The successor first proves nonzero uniformly in the whole model class, then
uses that fact along the actual interpolation paths to prove the phase bound. -/
theorem good_all (hq : 0 ≤ q) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hpow : (1:ℝ)/2 ≤ Real.cos θ ^ (r-1))
    (hbudget : 2*(c:ℝ)*‖z‖*q ≤ θ) (k : ℕ) :
    Good n m r c q z θ k := by
  induction k with
  | zero => exact good_zero hq hbudget
  | succ k ih =>
      have hnz := nonzero_succ ih hθ0 hθ1
      intro M S hS
      exact ⟨hnz M S hS,
        coordinatePhase_of_good ih hnz hq hθ0 hθ1 hpow hbudget M S hS⟩

/-- A genuine integral nonvanishing theorem for bounded continuous real
potentials on the finite product cube. -/
theorem integral_nonzero (M : Model n m r c q)
    (hq : 0 ≤ q) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hpow : (1:ℝ)/2 ≤ Real.cos θ ^ (r-1))
    (hbudget : 2*(c:ℝ)*‖z‖*q ≤ θ) :
    (∫ x in cube n, M.exponential z x) ≠ 0 := by
  have hg := good_all (n := n) (m := m) hq hθ0 hθ1 hpow hbudget n
  have hx : (fun _ : Fin n => (0:ℝ)) ∈ cube n := mem_cube.mpr (by simp)
  have hnz := (hg M Finset.univ (by simp)).1 _ hx
  simpa only [Model.partial, avg_univ] using hnz

end Paper08.ZeroFreeInduction

namespace Paper08.CubeZeroFreeMain
open Integral ZeroFreeInduction ComplexSector

/-- Lemma 2.1 for every labelled factor subcollection, on the original closed
β-disk. All hypotheses are original model or fixed-parameter promises. -/
theorem original_closed_disk {n m : ℕ} (p : FPTAS.Params)
    (E : FactorFamily n p.r m) (hc : FamilyBoundedOccurrence E p.c)
    (hE : ∀ e, (E e).RangeOk p.q) (hLip : ∀ e, (E e).LipOk p.K)
    (B : Finset (Fin m)) {z : ℂ} (hz : ‖z‖ ≤ FPTAS.beta p) :
    ZeroFree.Q E B z ≠ 0 := by
  have hr : 1 ≤ p.r-1 := by have := p.r_ge; omega
  have h := ZeroFreeInduction.integral_nonzero (ofFactors E B p.q_pos.le hE hLip hc)
    p.q_pos.le (angle_nonneg (p.r-1)) (angle_le_one hr)
    (cos_angle_pow_ge_half hr) (CubeZeroFreeParameters.induction_budget p hz)
  simpa only [Model.exponential, ofFactors_total, ZeroFree.Q] using h

/-- The common nonvanishing property needed by the analytic algorithm is a
proved consequence of the original input conditions. -/
theorem common_nonvanishing {n m : ℕ} (p : FPTAS.Params)
    (E : FactorFamily n p.r m) (hc : FamilyBoundedOccurrence E p.c)
    (hE : ∀ e, (E e).RangeOk p.q) (hLip : ∀ e, (E e).LipOk p.K) :
    FPTASCorrectness.CommonNonvanishing p E := by
  intro B z hz
  apply original_closed_disk p E hc hE hLip B
  exact (by simpa only [Metric.mem_ball, dist_zero_right] using hz : ‖z‖ < FPTAS.beta p).le

end Paper08.CubeZeroFreeMain
