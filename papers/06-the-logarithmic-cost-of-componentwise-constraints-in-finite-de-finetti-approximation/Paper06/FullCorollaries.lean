import Paper06.FullLowerBound
import Paper06.Asymptotics
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

set_option maxHeartbeats 800000

open Real Filter Asymptotics
open scoped Topology

namespace Paper06

/-- **Corollary 3.5.** No nonnegative sublogarithmic alphabet cost gives
the proposed uniform bound over all finite alphabets and all original
admissible data.  The optimum is taken over every Borel feasible mixing
measure, as in the paper. -/
theorem corollary_3_5 :
    ¬ ∃ C : ℝ, 0 < C ∧ ∃ h : ℕ → ℝ, (∀ d, 0 ≤ h d) ∧
      h =o[atTop] (fun d : ℕ => Real.log d) ∧
      ∀ (α : Type) [Fintype α] (n k : ℕ) (hkn : k ≤ n),
        1 < k → k < n → ∀ A : Admissible α n,
          constrainedError A.law A.slice k hkn ≤
            ((C * ((k : ℝ) * (k - 1) * h (Fintype.card α)) /
              (n - k + 1) : ℝ) : EReal) := by
  rintro ⟨C, hC, h, _hnonneg, hh, hbound⟩
  have hd : Tendsto (paperAlphabet (1 / 4)) atTop atTop :=
    paperAlphabet_tendsto (by norm_num)
  apply no_sublogarithmic_sequence_bound (paperAlphabet (1 / 4)) hd h hh
    (a := 3 / 128) (by norm_num) hC
  filter_upwards [eventually_ge_atTop 6, hd.eventually_ge_atTop 2] with N hN hd2
  let r := paperPrime (1 / 4) N
  have hr : Nat.Prime r := polynomialPrime_prime _ _ _
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  have hEven : Even 6 := by decide
  have hparam : 2 * Real.exp 1 * ((6 : ℝ) - 1) ≤
      (Fintype.card (ZMod r) : ℝ) ^ ((1 : ℝ) / 2 - 1 / 4) := by
    have hpar := paperPrime_parameter (θ := (1 / 4 : ℝ)) (by norm_num)
      (n := N) (by omega)
    have hNR : (6 : ℝ) ≤ N := by exact_mod_cast hN
    rw [ZMod.card]
    change 2 * Real.exp 1 * (6 - 1) ≤ (paperPrime (1 / 4) N : ℝ) ^ (1 / 2 - 1 / 4)
    have hexp := Real.exp_pos (1 : ℝ)
    nlinarith
  have hl := matching_constrainedError_lower (F := ZMod r)
    6 2 hEven (by norm_num) (by norm_num) (by norm_num)
    (1 / 4) (by norm_num) (by norm_num) hparam
  have hu := hbound (ZMod r × ZMod r) 6 2 (by norm_num)
    (by norm_num) (by norm_num) (matchingAdmissible (ZMod r) 6 hEven)
  rw [matchingAdmissible_slice] at hu
  have hcompare := hl.trans hu
  have hreal : (3 / 320 : ℝ) * Real.log (paperAlphabet (1 / 4) N) ≤
      (2 / 5 : ℝ) * C * h (paperAlphabet (1 / 4) N) := by
    have hreal' := EReal.coe_le_coe_iff.mp hcompare
    norm_num [Fintype.card_prod, ZMod.card] at hreal'
    convert hreal' using 1 <;>
      simp only [r, paperAlphabet, polynomialAlphabet, paperPrime,
        Nat.cast_pow, Real.log_pow] <;> (try simp only [pow_two]) <;> ring
  have hdR : (1 : ℝ) < paperAlphabet (1 / 4) N := by exact_mod_cast hd2
  have hlog : 0 < Real.log (paperAlphabet (1 / 4) N) := Real.log_pos hdR
  apply (le_div_iff₀ hlog).mpr
  nlinarith

end Paper06
