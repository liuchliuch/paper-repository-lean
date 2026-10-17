import Paper14.SieveResidualGeometry
import Paper14.DivisibleBandMean

open MeasureTheory Set Function Filter Finset
namespace Paper14
noncomputable section

lemma sieveSingle_zero_modulus (q : ℕ) (ε u : ℝ) :
    sieveSingle 0 (q : ℤ) ε u =
      if (Int.ceil u : ℝ) < u+ε ∧ IsCoprime (Int.ceil u) (q : ℤ) then 1 else 0 := by
  simp only [sieveSingle,Int.ofNat_eq_coe,Nat.cast_zero,Int.gcd_zero_right,Int.natAbs_natCast]

/-- Pointwise prime union bound for each actual single-q sieve remainder. -/
theorem sieveSingle_remainder_le (P Q : ℕ) {q : ℕ} (hq : 0 < q) (hqQ : q ≤ Q)
    (ε u : ℝ) :
    (sieveSingle (primorial P) (q : ℤ) ε u : ℝ)-(sieveSingle 0 (q : ℤ) ε u : ℝ) ≤
      ∑ ℓ ∈ Finset.range (Q+1),
        if P < ℓ ∧ Nat.Prime ℓ ∧ ℓ ∣ q then (divisibleBandSingle ℓ ε u : ℝ) else 0 := by
  classical
  have hsnonneg : 0 ≤ ∑ ℓ ∈ Finset.range (Q+1),
        if P < ℓ ∧ Nat.Prime ℓ ∧ ℓ ∣ q then (divisibleBandSingle ℓ ε u : ℝ) else 0 := by
    apply Finset.sum_nonneg
    intro ℓ hℓ
    split_ifs <;> positivity
  have hs0 := sieveSingle_le_one 0 (q : ℤ) ε u
  have hsM := sieveSingle_le_one (primorial P) (q : ℤ) ε u
  by_cases h0 : sieveSingle 0 (q : ℤ) ε u = 1
  · rw [h0,Nat.cast_one]
    have hh : (sieveSingle (primorial P) (q : ℤ) ε u : ℝ) ≤ 1 := by exact_mod_cast hsM
    linarith
  have h0' : sieveSingle 0 (q : ℤ) ε u = 0 := by omega
  by_cases hM : sieveSingle (primorial P) (q : ℤ) ε u = 0
  · simpa only [hM,h0',Nat.cast_zero,sub_zero] using hsnonneg
  have hM' : sieveSingle (primorial P) (q : ℤ) ε u = 1 := by omega
  have hcond : (Int.ceil u : ℝ) < u+ε ∧
      IsCoprime (Int.ceil u) ((Int.gcd (q : ℤ) (Int.ofNat (primorial P)) : ℕ) : ℤ) := by
    by_contra hn
    simp only [sieveSingle,if_neg hn] at hM'
    omega
  have hnot : ¬ IsCoprime (Int.ceil u) (q : ℤ) := by
    intro hc
    rw [sieveSingle_zero_modulus,if_pos ⟨hcond.1,hc⟩] at h0'
    omega
  obtain ⟨ℓ,hℓ,hPl,hℓq,hℓp⟩ := surviving_nonprimitive_large_prime P hcond.2 hnot
  have hlQ : ℓ < Q+1 := by have := Nat.le_of_dvd hq hℓq; omega
  have hh := Finset.single_le_sum (s := Finset.range (Q+1))
    (f := fun ℓ => if P < ℓ ∧ Nat.Prime ℓ ∧ ℓ ∣ q then (divisibleBandSingle ℓ ε u : ℝ) else 0)
    (fun ℓ _ => by dsimp only; split_ifs <;> positivity) (Finset.mem_range.mpr hlQ)
  have hterm : (if P < ℓ ∧ Nat.Prime ℓ ∧ ℓ ∣ q then
      (divisibleBandSingle ℓ ε u : ℝ) else 0) = 1 := by
    rw [if_pos ⟨hPl,hℓ,hℓq⟩]
    have hb : (Int.ceil u : ℝ) < u+ε ∧ (ℓ : ℤ) ∣ Int.ceil u := ⟨hcond.1,hℓp⟩
    simp only [divisibleBandSingle,if_pos hb,Nat.cast_one]
  dsimp only at hh
  rw [hterm] at hh
  simpa only [hM',h0',Nat.cast_one,Nat.cast_zero,sub_zero] using hh

/-- Actual G_M minus G_prim is bounded by the finite common-prime union,
with the original coefficient order and no spurious p cutoff. -/
theorem GM_remainder_le_prime_sum (P Q : ℕ) (c θ ε : ℝ) (hε : ε ≤ 1) :
    (GM (primorial P) Q c θ ε : ℝ)-(GPrim Q c θ ε : ℝ) ≤
      ∑ ℓ ∈ Finset.range (Q+1),
        if P < ℓ ∧ Nat.Prime ℓ then
          ∑ q ∈ Finset.range Q, if ℓ ∣ q+1 then
            (divisibleBandSingle ℓ ε (((q+1 : ℕ) : ℝ)*θ-c) : ℝ) else 0
        else 0 := by
  rw [GM_cast_sum_nat _ Q c θ ε hε,GPrim_cast_sum_nat Q c θ ε hε,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ q ∈ Finset.range Q, ∑ ℓ ∈ Finset.range (Q+1),
        if P < ℓ ∧ Nat.Prime ℓ ∧ ℓ ∣ q+1 then
          (divisibleBandSingle ℓ ε (((q+1 : ℕ) : ℝ)*θ-c) : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro q hq
      exact sieveSingle_remainder_le P Q (by omega) (by have := Finset.mem_range.mp hq; omega) ε _
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      by_cases hp : P < ℓ ∧ Nat.Prime ℓ
      · simp only [if_pos hp]
        apply Finset.sum_congr rfl
        intro q hq
        by_cases hd : ℓ ∣ q+1 <;> simp [hp.1,hp.2,hd]
      · simp only [if_neg hp]
        apply Finset.sum_eq_zero
        intro q hq
        rw [if_neg (fun h => hp ⟨h.1,h.2.1⟩)]

end
end Paper14
