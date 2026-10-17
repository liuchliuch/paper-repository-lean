import Paper29.PilotGrid
import Paper29.LogTransfer
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Int.Interval

noncomputable section
open scoped BigOperators Classical
namespace Paper29.ProcessTools

/-- Exact finite dyadic list used in (3.31). -/
def pilotGrid (n : ℕ) : Finset ℝ :=
  (Finset.Icc (-1 : ℤ) ⌈Real.logb 2 (8 * (n : ℝ)^3)⌉).image (fun j => (2 : ℝ)^j)

theorem pilotGrid_pos (n : ℕ) : ∀ S ∈ pilotGrid n, 0 < S := by
  intro S hS
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hS
  exact zpow_pos (by norm_num) j

/-- Ceiling a base-two logarithm supplies the desired radius within factor two. -/
theorem dyadic_ceiling {R : ℝ} (hR : 0 < R) :
    R ≤ (2 : ℝ)^⌈Real.logb 2 R⌉ ∧ (2 : ℝ)^⌈Real.logb 2 R⌉ < 2 * R := by
  have hlow := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hR).mp
    (Int.le_ceil (Real.logb 2 R))
  have hhigh := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
    (Int.ceil_lt_add_one (Real.logb 2 R))
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hR,
    Real.rpow_one] at hhigh
  simpa only [Real.rpow_intCast, mul_comm] using And.intro hlow hhigh

theorem pilotGrid_covers {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    PilotGridCovers A (pilotGrid n) := by
  intro h hlo hhi
  have hR : 0 < unshifted A h := by linarith
  have hl : (-1 : ℝ) ≤ Real.logb 2 (unshifted A h) := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hR).2
    norm_num
    exact hlo
  have hjlow : (-1 : ℤ) ≤ ⌈Real.logb 2 (unshifted A h)⌉ := by
    exact_mod_cast hl.trans (Int.le_ceil _)
  have hjhi : ⌈Real.logb 2 (unshifted A h)⌉ ≤ ⌈Real.logb 2 (8 * (n : ℝ)^3)⌉ :=
    Int.ceil_mono (Real.logb_le_logb_of_le (by norm_num) hR hhi)
  refine ⟨(2 : ℝ)^⌈Real.logb 2 (unshifted A h)⌉, ?_, (dyadic_ceiling hR).1,
    (dyadic_ceiling hR).2.le⟩
  exact Finset.mem_image.mpr ⟨_, Finset.mem_Icc.mpr ⟨hjlow, hjhi⟩, rfl⟩

theorem pilotGrid_nonempty {n : ℕ} (hn : 1 ≤ n) : (pilotGrid n).Nonempty := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ht : 1 ≤ 8 * (n : ℝ)^3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hnR 3]
  have hlog := Real.logb_nonneg (b := (2 : ℝ)) (by norm_num) ht
  have hj : (0 : ℤ) ≤ ⌈Real.logb 2 (8 * (n : ℝ)^3)⌉ := Int.ceil_nonneg hlog
  refine ⟨1, Finset.mem_image.mpr ⟨0, Finset.mem_Icc.mpr ⟨by norm_num, hj⟩, by simp⟩⟩

/-- A universal explicit O(log(2N)) bound, with no numerical certificate. -/
theorem pilotGrid_card_le {n : ℕ} (hn : 1 ≤ n) :
    ((pilotGrid n).card : ℝ) ≤ (6 / Real.log 2) * Real.log (2 * (n : ℝ)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hln : Real.log 2 ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hpow : 8 * (n : ℝ)^3 = (2 * (n : ℝ))^3 := by ring
  have hlog : Real.logb 2 (8 * (n : ℝ)^3) =
      3 * Real.log (2 * (n : ℝ)) / Real.log 2 := by
    rw [Real.logb, hpow, Real.log_pow]
    norm_num
  let u : ℤ := ⌈Real.logb 2 (8 * (n : ℝ)^3)⌉
  have hln0 : 0 < Real.log (2 * (n : ℝ)) := hl2.trans_le hln
  have hu0 : 0 ≤ u := Int.ceil_nonneg (by rw [hlog]; positivity)
  have hu : (u : ℝ) < Real.logb 2 (8 * (n : ℝ)^3) + 1 :=
    Int.ceil_lt_add_one _
  rw [hlog] at hu
  have hc := Finset.card_image_le (s := Finset.Icc (-1 : ℤ) u) (f := fun j => (2 : ℝ)^j)
  have hcard : ((Finset.Icc (-1 : ℤ) u).card : ℝ) = (u : ℝ) + 2 := by
    have h := Int.card_Icc_of_le (a := (-1 : ℤ)) (b := u) (by omega)
    have h' : ((Finset.Icc (-1 : ℤ) u).card : ℤ) = u + 2 := by omega
    exact_mod_cast h'
  have hcR : ((pilotGrid n).card : ℝ) ≤ (u : ℝ) + 2 := by
    have hc' : ((pilotGrid n).card : ℝ) ≤ ((Finset.Icc (-1 : ℤ) u).card : ℝ) := by
      exact_mod_cast hc
    exact hc'.trans_eq hcard
  have hr : 3 ≤ 3 * Real.log (2 * (n : ℝ)) / Real.log 2 := by
    apply (le_div_iff₀ hl2).2
    linarith
  calc
    _ ≤ (u : ℝ) + 2 := hcR
    _ ≤ 6 * Real.log (2 * (n : ℝ)) / Real.log 2 := by
      calc
        _ ≤ 2 * (3 * Real.log (2 * (n : ℝ)) / Real.log 2) := by linarith
        _ = _ := by ring
    _ = _ := by ring

end Paper29.ProcessTools
