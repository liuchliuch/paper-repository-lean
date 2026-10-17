import Paper36.Bank
import Paper36.Target

/-! Instantiation of the deterministic bank by the source target (4.4)--(4.8).
The rare-event quantity `w` here is `W_{α,H}`; its MDP definition is independent
of these deterministic statements. -/
namespace Paper36.BankTarget

noncomputable section

/-- The original anytime target with every numerical constant expanded by (4.4). -/
def paperTarget (s a h w : ℝ) : ℕ → ℝ :=
  Target.target (Target.scale w s a) (Target.A0 s a h) (Target.nu s) (Target.M0 h)

/-- The exact residual formula R_* from (4.8). -/
def paperResidual (s a h w Δ : ℝ) : ℝ :=
  Target.residual (Target.scale w s a) (Target.A0 s a h) (Target.nu s) (Target.M0 h) Δ

/-- Every analytic property required by the bank is now proved for the actual target. -/
theorem actual_target_properties {s a h w Δ : ℝ}
    (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h) (hw : 0 ≤ w) (hΔ : 0 < Δ) :
    Monotone (paperTarget s a h w) ∧ paperTarget s a h w 0 = 0 ∧
    (∀ j n, paperTarget s a h w (j + n) ≤
      paperTarget s a h w j + paperTarget s a h w n) ∧
    (∀ n, paperTarget s a h w n - (n : ℝ) * Δ ≤ paperResidual s a h w Δ) ∧
    Filter.Tendsto (fun n : ℕ => paperTarget s a h w n / (n : ℝ))
      Filter.atTop (nhds 0) := by
  have hp := Target.parameter_bounds hs ha hh
  have hc := Target.scale_nonneg (s := s) (a := a) hw
  have hA : 0 < Target.A0 s a h := by linarith [hp.1, hp.2.1]
  have hM : 0 < Target.M0 h := by linarith [hp.2.2]
  refine ⟨Target.target_monotone hc hA.le hp.1.le hM.le, ?_,
    Target.target_subadditive hc hp.1.le hp.2.1 hp.2.2,
    Target.target_drift_bound hc hA hM hp.1.le hΔ,
    Target.target_sublinear hc hA hM hp.1.le⟩
  exact Target.target_zero _ _ _ _

/-- The literal calibration-count guarantee (4.12) for the target used by Algorithm 1. -/
theorem calibration_count {s a h w Δ τ : ℝ} (d : ℕ → ℝ)
    (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h) (hw : 0 ≤ w)
    (hΔ : 0 < Δ) (hτ : 0 ≤ τ)
    (hdeposit : ∀ n, Bank.calibrates (paperTarget s a h w) d n →
      Δ ≤ d (n + 1) ∧ d (n + 1) ≤ τ) (K : ℕ) :
    (Bank.count (paperTarget s a h w) d K : ℝ) ≤
      min (K : ℝ) ((paperTarget s a h w K + τ) / Δ) := by
  have hp := actual_target_properties hs ha hh hw hΔ
  exact Bank.calibration_count_bound _ d Δ τ hΔ hp.1
    (by rw [hp.2.1]; simpa using hτ)
    (fun n hn => (hdeposit n hn).1) (fun n hn => (hdeposit n hn).2) K

/-- The literal bank-deficit guarantee (5.17), using the explicit source R_*. -/
theorem bank_deficit {s a h w Δ : ℝ} (d : ℕ → ℝ)
    (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h) (hw : 0 ≤ w) (hΔ : 0 < Δ)
    (hdeposit : ∀ n, Bank.calibrates (paperTarget s a h w) d n → Δ ≤ d (n + 1))
    (K : ℕ) :
    paperTarget s a h w K - Bank.bank (paperTarget s a h w) d K ≤
      paperResidual s a h w Δ := by
  have hp := actual_target_properties hs ha hh hw hΔ
  exact Bank.deficit_le_residual _ d Δ _ hp.2.1 hdeposit hp.2.2.1 hp.2.2.2.1 K

/-- The calibration-frequency endpoint of Theorem 4.2 for the actual source target. -/
theorem calibration_sparse {s a h w Δ τ : ℝ} (d : ℕ → ℝ)
    (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h) (hw : 0 ≤ w)
    (hΔ : 0 < Δ) (hτ : 0 ≤ τ)
    (hdeposit : ∀ n, Bank.calibrates (paperTarget s a h w) d n →
      Δ ≤ d (n + 1) ∧ d (n + 1) ≤ τ) :
    Filter.Tendsto (fun K : ℕ => (Bank.count (paperTarget s a h w) d K : ℝ) / (K : ℝ))
      Filter.atTop (nhds 0) := by
  have hp := actual_target_properties hs ha hh hw hΔ
  exact Bank.calibration_sparse_of_target_sublinear _ d Δ τ hΔ hp.1
    (by rw [hp.2.1]; simpa using hτ)
    (fun n hn => (hdeposit n hn).1) (fun n hn => (hdeposit n hn).2) hp.2.2.2.2

end
end Paper36.BankTarget
