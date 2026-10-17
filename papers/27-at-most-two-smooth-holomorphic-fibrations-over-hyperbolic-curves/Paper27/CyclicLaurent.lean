import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# The coefficient calculation in Lemma 3.3

This file proves the local algebra used in the cyclic averaging argument. A
coefficient sequence is a function `ℤ → ℂ`; no convergence or global geometric
claim is built into this representation. The cyclic pushforward multiplier for
`y^k ∂/∂y` is `ζ^(1-k)`. Averaging is the actual finite cyclic sum. The root of
unity assumptions below are Mathlib's `IsPrimitiveRoot`, and the character sum
and support restriction are proved from them.
-/

noncomputable section

open Finset

namespace Paper27.CyclicLaurent

/-- Formal vertical Laurent coefficient sequences. -/
abbrev Coefficients := ℤ → ℂ

/-- The coefficient action of the `j`th power of `(x,y) ↦ (x,ζy)`. -/
def pushforward (ζ : ℂ) (j : ℕ) (c : Coefficients) : Coefficients :=
  fun k => ζ ^ ((1 - k) * (j : ℤ)) * c k

/-- The finite cyclic average, coefficient by coefficient. -/
def average (n : ℕ) (ζ : ℂ) (c : Coefficients) : Coefficients :=
  fun k => (n : ℂ)⁻¹ * ∑ j ∈ range n, pushforward ζ j c k

/-- Pole order at most `n-1`, stated without making an analytic convergence claim. -/
def PoleBound (n : ℕ) (c : Coefficients) : Prop :=
  ∀ k : ℤ, k < 1 - (n : ℤ) → c k = 0

/-- The formal local condition `O(y) ∂/∂y`: all coefficients of degree at most
zero vanish. -/
def TangentRegular (c : Coefficients) : Prop :=
  ∀ k : ℤ, k ≤ 0 → c k = 0

/-- An actual cyclic character sum over a primitive complex root. -/
theorem character_sum {n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (e : ℤ) :
    (∑ j ∈ range n, ζ ^ (e * (j : ℤ))) =
      if (n : ℤ) ∣ e then (n : ℂ) else 0 := by
  simp_rw [zpow_mul, zpow_natCast]
  by_cases hd : (n : ℤ) ∣ e
  · have he : ζ ^ e = 1 := (hζ.zpow_eq_one_iff_dvd e).2 hd
    simp [hd, he]
  · have he : ζ ^ e ≠ 1 := mt (hζ.zpow_eq_one_iff_dvd e).1 hd
    have hp : (ζ ^ e) ^ n = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm e (n : ℤ), zpow_mul,
        hζ.zpow_eq_one, one_zpow]
    rw [if_neg hd, geom_sum_eq he, hp, sub_self, zero_div]

/-- Averaging projects onto the exponents congruent to `1` modulo `n`. -/
theorem average_coefficient {n : ℕ} {ζ : ℂ} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (c : Coefficients) (k : ℤ) :
    average n ζ c k = if (n : ℤ) ∣ 1 - k then c k else 0 := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold average pushforward
  rw [← Finset.sum_mul, character_sum hζ]
  split_ifs with hd
  · field_simp
  · simp

/-- The nontrivial characters have zero average. -/
theorem average_eq_zero_of_not_dvd {n : ℕ} {ζ : ℂ} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (c : Coefficients) (k : ℤ)
    (hd : ¬ (n : ℤ) ∣ 1 - k) : average n ζ c k = 0 := by
  simp [average_coefficient hn hζ, hd]

/-- The trivial characters survive with their original coefficient. -/
theorem average_eq_self_of_dvd {n : ℕ} {ζ : ℂ} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (c : Coefficients) (k : ℤ)
    (hd : (n : ℤ) ∣ 1 - k) : average n ζ c k = c k := by
  simp [average_coefficient hn hζ, hd]

/-- In the pole interval `[1-n,0]`, the only trivial character has degree `1-n`. -/
theorem unique_pole_exponent {n : ℕ} {k : ℤ}
    (hl : 1 - (n : ℤ) ≤ k) (hu : k ≤ 0) (hd : (n : ℤ) ∣ 1 - k) :
    k = 1 - (n : ℤ) := by
  have hp : 0 < 1 - k := by omega
  have hle : (n : ℤ) ≤ 1 - k := Int.le_of_dvd hp hd
  omega

/-- Cyclic averaging retains exactly the one possible principal coefficient. -/
theorem average_nonpositive {n : ℕ} {ζ : ℂ} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (c : Coefficients) (hc : PoleBound n c)
    (k : ℤ) (hk : k ≤ 0) :
    average n ζ c k = if k = 1 - (n : ℤ) then c k else 0 := by
  rw [average_coefficient hn hζ]
  by_cases he : k = 1 - (n : ℤ)
  · subst k
    simp
  · rw [if_neg he]
    by_cases hl : k < 1 - (n : ℤ)
    · simp [hc k hl]
    · have hd : ¬ (n : ℤ) ∣ 1 - k := by
        intro hd
        exact he (unique_pole_exponent (le_of_not_gt hl) hk hd)
      simp [hd]

/-- The leading principal coefficient is unchanged by averaging. -/
theorem average_leading {n : ℕ} {ζ : ℂ} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (c : Coefficients) :
    average n ζ c (1 - (n : ℤ)) = c (1 - (n : ℤ)) := by
  apply average_eq_self_of_dvd hn hζ
  simp

/-- Every averaged coefficient sequence is invariant under the generator. -/
theorem average_invariant {n : ℕ} {ζ : ℂ} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (c : Coefficients) :
    pushforward ζ 1 (average n ζ c) = average n ζ c := by
  funext k
  unfold pushforward
  rw [average_coefficient hn hζ]
  by_cases hd : (n : ℤ) ∣ 1 - k
  · simp [hd, (hζ.zpow_eq_one_iff_dvd (1 - k)).2 hd]
  · simp [hd]

/-- Averaging is an idempotent projection. -/
theorem average_idempotent {n : ℕ} {ζ : ℂ} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (c : Coefficients) :
    average n ζ (average n ζ c) = average n ζ c := by
  funext k
  simp only [average_coefficient hn hζ]
  split_ifs <;> rfl

/-- Vertical coefficients of the affine combination in equation (6). -/
def affineCombination (a : ℂ) (c₂ c₃ : Coefficients) : Coefficients :=
  fun k => (a * c₃ k - c₂ k) / (a - 1)

/-- The horizontal coefficients of two splittings still sum to one. -/
theorem affine_weights_sum_one {a : ℂ} (ha : a ≠ 1) :
    a / (a - 1) - 1 / (a - 1) = 1 := by
  rw [← sub_div, div_self (sub_ne_zero.mpr ha)]

/-- The remaining pole cancels and the constant vertical coefficient vanishes.
This is precisely the formal coefficient conclusion `∂x + O(y) ∂y` of equation
(6), under the two pole bounds and the principal coefficients displayed in the
paper. Analytic extension and gluing are separate geometric assertions. -/
theorem affine_average_tangent {n : ℕ} {ζ a : ℂ} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (ha0 : a ≠ 0)
    (c₂ c₃ : Coefficients) (h₃ : PoleBound n c₃)
    (hc₂ : ∀ k : ℤ, k ≤ 0 →
      c₂ k = if k = 1 - (n : ℤ) then -(1 / (n : ℂ)) else 0)
    (hc₃ : c₃ (1 - (n : ℤ)) = -(1 / (a * (n : ℂ)))) :
    TangentRegular (affineCombination a c₂ (average n ζ c₃)) := by
  intro k hk
  unfold affineCombination
  rw [average_nonpositive hn hζ c₃ h₃ k hk, hc₂ k hk]
  by_cases he : k = 1 - (n : ℤ)
  · subst k
    simp only [if_true, hc₃]
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp
    ring
  · simp [he]

/-- The exact vertical coefficient sequence of `σ₂(∂x) = ∂x - y^(1-n)∂y/n`. -/
def standardSplittingCoefficients (n : ℕ) : Coefficients :=
  fun k => if k = 1 - (n : ℤ) then -(1 / (n : ℂ)) else 0

/-- The standard second splitting satisfies the stated pole bound. -/
theorem standardSplitting_poleBound (n : ℕ) :
    PoleBound n (standardSplittingCoefficients n) := by
  intro k hk
  simp [standardSplittingCoefficients, ne_of_lt hk]

/-- The cyclic action fixes the exact second splitting in the normal form. -/
theorem standardSplitting_invariant {n : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) :
    pushforward ζ 1 (standardSplittingCoefficients n) =
      standardSplittingCoefficients n := by
  funext k
  by_cases hk : k = 1 - (n : ℤ)
  · subst k
    simp [pushforward, standardSplittingCoefficients, hζ.zpow_eq_one]
  · simp [pushforward, standardSplittingCoefficients, hk]

/-- An affine combination of invariant coefficient sequences is invariant. -/
theorem affineCombination_invariant {ζ a : ℂ} {c₂ c₃ : Coefficients}
    (h₂ : pushforward ζ 1 c₂ = c₂) (h₃ : pushforward ζ 1 c₃ = c₃) :
    pushforward ζ 1 (affineCombination a c₂ c₃) = affineCombination a c₂ c₃ := by
  funext k
  have h₂k := congrFun h₂ k
  have h₃k := congrFun h₃ k
  dsimp [pushforward] at h₂k h₃k
  dsimp [pushforward, affineCombination]
  calc
    ζ ^ ((1 - k) * (1 : ℤ)) * ((a * c₃ k - c₂ k) / (a - 1)) =
        (a * (ζ ^ ((1 - k) * (1 : ℤ)) * c₃ k) -
          ζ ^ ((1 - k) * (1 : ℤ)) * c₂ k) / (a - 1) := by ring
    _ = (a * c₃ k - c₂ k) / (a - 1) := by rw [h₂k, h₃k]

/-- The complete formal coefficient conclusion of equation (6): its weights
sum to one, the result has no nonpositive vertical coefficients, and it is
invariant. The assumptions are exactly the displayed principal coefficient of
`σ₃`, its pole bound, and the nonzero constants needed for the affine formula.
This theorem concerns local coefficients, not analytic extension or gluing. -/
theorem equation_six_local {n : ℕ} {ζ a : ℂ} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (c₃ : Coefficients) (h₃ : PoleBound n c₃)
    (hc₃ : c₃ (1 - (n : ℤ)) = -(1 / (a * (n : ℂ)))) :
    a / (a - 1) - 1 / (a - 1) = 1 ∧
    TangentRegular (affineCombination a (standardSplittingCoefficients n)
      (average n ζ c₃)) ∧
    pushforward ζ 1 (affineCombination a (standardSplittingCoefficients n)
      (average n ζ c₃)) =
      affineCombination a (standardSplittingCoefficients n) (average n ζ c₃) := by
  refine ⟨affine_weights_sum_one ha1, ?_, ?_⟩
  · apply affine_average_tangent hn hζ ha0 (standardSplittingCoefficients n) c₃ h₃
    · intro k hk
      rfl
    · exact hc₃
  · exact affineCombination_invariant (standardSplitting_invariant hζ)
      (average_invariant hn hζ c₃)

end Paper27.CyclicLaurent
