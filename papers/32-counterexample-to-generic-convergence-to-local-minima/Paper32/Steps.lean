import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # The explicit power-law schedule in P32

These lemmas verify every numerical step-size hypothesis used by the trapping
argument for the actual schedule `(k + 8) ^ (-γ)`.
-/

open Filter Topology

namespace Paper32

/-- The schedule from equation (2.7). -/
noncomputable def powerStep (γ : ℝ) (k : ℕ) : ℝ := ((k : ℝ) + 8) ^ (-γ)

theorem powerStep_pos (γ : ℝ) (k : ℕ) : 0 < powerStep γ k := by
  exact Real.rpow_pos_of_pos (by positivity) _

theorem powerStep_antitone {γ : ℝ} (hγ : 0 ≤ γ) : Antitone (powerStep γ) := by
  intro i j hij
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 8) (by linarith)

theorem powerStep_tendsto_zero {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (powerStep γ) atTop (𝓝 0) := by
  have ht : Tendsto (fun k : ℕ => (k : ℝ) + 8) atTop atTop :=
    tendsto_atTop_mono (fun k : ℕ => (show (k : ℝ) ≤ (k : ℝ) + 8 by linarith)) tendsto_natCast_atTop_atTop
  exact (tendsto_rpow_neg_atTop hγ).comp ht

/-- The ratio is the `γ`-th power of the ratio of the two bases. -/
theorem powerStep_ratio (γ : ℝ) (k : ℕ) :
    powerStep γ k / powerStep γ (k + 1) =
      (((k : ℝ) + 9) / ((k : ℝ) + 8)) ^ γ := by
  simp only [powerStep, Nat.cast_add, Nat.cast_one]
  rw [show (k : ℝ) + 1 + 8 = (k : ℝ) + 9 by ring]
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), inv_div_inv]
  exact (Real.div_rpow (by positivity) (by positivity) γ).symm

/-- Equation (6.1), with the strict paper bound `9/8 < 1.13`. -/
theorem powerStep_ratio_lt {γ : ℝ} (hγ : γ < 1) (k : ℕ) :
    powerStep γ k / powerStep γ (k + 1) < (113 / 100 : ℝ) := by
  rw [powerStep_ratio]
  have hb : 1 ≤ ((k : ℝ) + 9) / ((k : ℝ) + 8) := by
    apply (le_div_iff₀ (by positivity)).2
    linarith
  have he := Real.rpow_le_rpow_of_exponent_le hb (le_of_lt hγ)
  rw [Real.rpow_one] at he
  have hr : ((k : ℝ) + 9) / ((k : ℝ) + 8) ≤ (9 / 8 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  linarith

/-- The form of the ratio bound used directly by the invariant. -/
theorem powerStep_ratio_bound {γ : ℝ} (hγ : γ < 1) (k : ℕ) :
    powerStep γ k ≤ (113 / 100 : ℝ) * powerStep γ (k + 1) := by
  exact (div_le_iff₀ (powerStep_pos γ (k + 1))).1 (le_of_lt (powerStep_ratio_lt hγ k))

theorem powerStep_prev_bound {γ : ℝ} (hγ : γ < 1) {k : ℕ} (hk : 1 ≤ k) :
    powerStep γ (k - 1) ≤ (113 / 100 : ℝ) * powerStep γ k := by
  simpa [Nat.sub_add_cancel hk] using powerStep_ratio_bound hγ (k - 1)

/-- The initial step is uniformly larger than `1/8`; see Lemma 4.1. -/
theorem powerStep_initial_lower {γ : ℝ} (hγ : γ < 1) :
    (1 / 8 : ℝ) < powerStep γ 0 := by
  simpa [powerStep, Real.rpow_neg_one] using
    (Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 8)
      (show (-1 : ℝ) < -γ by linarith))

/-- The numerical neighborhood check in equation (6.2). -/
theorem powerStep_initial_upper {γ : ℝ} (hγ : (1 / 2 : ℝ) < γ) :
    (111 / 10 : ℝ) * powerStep γ 0 < 4 := by
  have hpow : powerStep γ 0 < (8 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    simpa [powerStep] using
      (Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 8)
        (show -γ < -(1 / 2 : ℝ) by linarith))
  have hs : (0 : ℝ) < (8 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hsq : ((8 : ℝ) ^ (-(1 / 2 : ℝ))) ^ (2 : ℕ) = (1 / 8 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8)]
    norm_num [Real.rpow_neg_one]
  nlinarith [powerStep_pos γ 0]

/-- The target-framework upper power-law bound. -/
theorem powerStep_upper {γ : ℝ} (hγ : 0 ≤ γ) (k : ℕ) :
    powerStep γ k ≤ ((k : ℝ) + 1) ^ (-γ) := by
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)

/-- The target-framework lower power-law bound, with `c₁ = 8^(-γ)`. -/
theorem powerStep_lower {γ : ℝ} (hγ : 0 ≤ γ) (k : ℕ) :
    (8 : ℝ) ^ (-γ) * ((k : ℝ) + 1) ^ (-γ) ≤ powerStep γ k := by
  rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [Nat.cast_nonneg (α := ℝ) k]) (by linarith)

/-- Complete step-size verification with the quantifiers of equation (2.7). -/
theorem powerStep_conditions {γ : ℝ} (hγlo : (1 / 2 : ℝ) < γ) (hγhi : γ < 1) :
    (∀ k, 0 < powerStep γ k) ∧ Antitone (powerStep γ) ∧
    Tendsto (powerStep γ) atTop (𝓝 0) ∧
    (∀ k, powerStep γ k ≤ (113 / 100 : ℝ) * powerStep γ (k + 1)) ∧
    (1 / 8 : ℝ) < powerStep γ 0 ∧ (111 / 10 : ℝ) * powerStep γ 0 < 4 ∧
    (∀ k : ℕ, (8 : ℝ) ^ (-γ) * ((k : ℝ) + 1) ^ (-γ) ≤ powerStep γ k ∧
      powerStep γ k ≤ ((k : ℝ) + 1) ^ (-γ)) := by
  have hp : 0 < γ := by linarith
  exact ⟨powerStep_pos γ, powerStep_antitone hp.le, powerStep_tendsto_zero hp,
    powerStep_ratio_bound hγhi, powerStep_initial_lower hγhi,
    powerStep_initial_upper hγlo, fun k => ⟨powerStep_lower hp.le k, powerStep_upper hp.le k⟩⟩

end Paper32
