import Paper29.DyadicGrid

noncomputable section
open scoped BigOperators Classical
namespace Paper29.ProcessTools

def transitionLength (n : ℕ) : ℕ := ⌈4 * Real.log (2 * (n : ℝ))⌉₊ + 1

def transitionTop (n : ℕ) : ℤ := ⌈Real.logb 2 (2 * (n : ℝ))⌉

def transitionScales (n : ℕ) : Finset ℤ :=
  Finset.Icc (-2 - (transitionLength n : ℤ)) (2 + transitionTop n)

def radiusBlock (n : ℕ) (R : ℝ) : Finset ℤ :=
  Finset.Icc (⌈Real.logb 2 R⌉ - (transitionLength n : ℤ)) (⌈Real.logb 2 R⌉ - 1)

theorem transitionLength_pos (n : ℕ) : 0 < transitionLength n := by
  unfold transitionLength
  omega

theorem transitionLength_large (n : ℕ) : 4 * Real.log (2 * (n : ℝ)) ≤ transitionLength n := by
  exact (Nat.le_ceil _).trans (by simp [transitionLength])

theorem radiusBlock_nonempty (n : ℕ) (R : ℝ) : (radiusBlock n R).Nonempty := by
  apply Finset.nonempty_Icc.mpr
  have h := transitionLength_pos n
  omega

theorem radiusBlock_card (n : ℕ) (R : ℝ) : (radiusBlock n R).card = transitionLength n := by
  unfold radiusBlock
  rw [Int.card_Icc]
  have he : ⌈Real.logb 2 R⌉ - 1 + 1 - (⌈Real.logb 2 R⌉ - (transitionLength n : ℤ)) =
      (transitionLength n : ℤ) := by ring
  rw [he, Int.toNat_natCast]

theorem radiusBlock_subset {n : ℕ} {R : ℝ} (hlo : 1/2 ≤ R) (hhi : R ≤ (n:ℝ)/2) :
    radiusBlock n R ⊆ transitionScales n := by
  have hR : 0 < R := by linarith
  have hjlo : (-1 : ℤ) ≤ ⌈Real.logb 2 R⌉ := by
    have hl : (-1 : ℝ) ≤ Real.logb 2 R := by
      apply (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) hR).2
      norm_num
      exact hlo
    exact_mod_cast hl.trans (Int.le_ceil _)
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hjhi : ⌈Real.logb 2 R⌉ ≤ transitionTop n :=
    Int.ceil_mono (Real.logb_le_logb_of_le (by norm_num) hR (by linarith))
  intro j hj
  obtain ⟨hjl, hju⟩ := Finset.mem_Icc.mp hj
  apply Finset.mem_Icc.mpr
  constructor <;> omega

/-- Exact finite transition-window size, with an explicit universal logarithmic
constant. This is the paper's own window bookkeeping. -/
theorem transitionScales_card_le {n : ℕ} (hn : 1 ≤ n) :
    ((transitionScales n).card : ℝ) ≤
      (4 + 9 / Real.log 2) * Real.log (2 * (n : ℝ)) := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hln : Real.log 2 ≤ Real.log (2*(n:ℝ)) := Real.log_le_log (by norm_num) (by linarith)
  have hln0 : 0 ≤ Real.log (2*(n:ℝ)) := hl2.le.trans hln
  have hL : (transitionLength n : ℝ) < 4 * Real.log (2*(n:ℝ)) + 2 := by
    have h := Nat.ceil_lt_add_one (mul_nonneg (by norm_num : (0:ℝ)≤4) hln0)
    simp only [transitionLength, Nat.cast_add, Nat.cast_one]
    linarith only [h]
  have htop : (transitionTop n : ℝ) < Real.log (2*(n:ℝ))/Real.log 2 + 1 :=
    Int.ceil_lt_add_one _
  have htop0 : (0:ℤ) ≤ transitionTop n :=
    Int.ceil_nonneg (Real.logb_nonneg (by norm_num : (1:ℝ)<2) (by linarith))
  have hc : ((transitionScales n).card : ℝ) =
      (transitionTop n : ℝ) + (transitionLength n : ℝ) + 5 := by
    have he := Int.card_Icc_of_le (a := -2-(transitionLength n:ℤ))
      (b := 2+transitionTop n) (by omega)
    have he' : ((transitionScales n).card : ℤ) = transitionTop n + transitionLength n + 5 := by
      change ((Finset.Icc (-2-(transitionLength n:ℤ)) (2+transitionTop n)).card : ℤ) = _
      linarith only [he]
    exact_mod_cast he'
  have hr : 1 ≤ Real.log (2*(n:ℝ))/Real.log 2 := (le_div_iff₀ hl2).2 (by simpa using hln)
  rw [hc]
  calc
    _ ≤ 4*Real.log (2*(n:ℝ)) + 9*(Real.log (2*(n:ℝ))/Real.log 2) := by linarith
    _ = _ := by ring

end Paper29.ProcessTools
