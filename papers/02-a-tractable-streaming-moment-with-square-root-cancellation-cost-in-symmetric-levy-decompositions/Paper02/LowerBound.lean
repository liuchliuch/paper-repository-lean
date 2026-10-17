import Paper02.Bounds
import Paper02.MeasureDual
import Paper02.RSCore

/-!
Perturbation estimate for the actual second-difference certificate.  All
constraints below are those of (1.2); the error estimate uses only integers
inside the prescribed interval.
-/

noncomputable section

namespace Paper02.LowerBound

open Paper02 Finset

theorem admissible_error (gpos gneg : ℤ → ℝ) (n : ℕ) (η ρ : ℝ)
    (hη : 0 ≤ η) (h : AdmissibleSplit gpos gneg f n η ρ)
    (j : ℤ) (hj : |j| ≤ n) :
    |gpos j - gneg j - f j| ≤ 3 * η := by
  exact (h.1 j hj).trans (by nlinarith [f_le_three j])

theorem interior_secondDiff_error (gpos gneg : ℤ → ℝ) (N : ℕ) (η ρ : ℝ)
    (hN : 4 ≤ N) (hη : 0 ≤ η)
    (h : AdmissibleSplit gpos gneg f (N - 1) η ρ)
    (k : ℕ) (hk : k ∈ Icc 2 (N - 2)) :
    |secondDiff (fun j => gpos j - gneg j - f j) (k : ℤ)| ≤ 6 * η := by
  have hk' := mem_Icc.mp hk
  apply Bounds.secondDiff_error_le
  all_goals
    apply admissible_error gpos gneg (N - 1) η ρ hη h
    rw [abs_of_nonneg (by omega)]
    omega

/-- The perturbation of the complete interior certificate has exactly `N-3`
terms; each coefficient has absolute value one. -/
theorem interior_pairing_error (gpos gneg : ℤ → ℝ) (N : ℕ) (η ρ : ℝ)
    (hN : 4 ≤ N) (hη : 0 ≤ η)
    (h : AdmissibleSplit gpos gneg f (N - 1) η ρ) :
    |∑ k ∈ Icc 2 (N - 2), rudinShapiro k *
      secondDiff (fun j => gpos j - gneg j - f j) (k : ℤ)|
      ≤ 6 * η * ((N : ℝ) - 3) := by
  calc
    _ ≤ ∑ k ∈ Icc 2 (N - 2),
        |rudinShapiro k * secondDiff (fun j => gpos j - gneg j - f j) (k : ℤ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Icc 2 (N - 2), 6 * η := by
      apply sum_le_sum
      intro k hk
      rw [abs_mul, abs_rudinShapiro, one_mul]
      exact interior_secondDiff_error gpos gneg N η ρ hN hη h k hk
    _ = 6 * η * ((N : ℝ) - 3) := by
      rw [sum_const, Nat.card_Icc]
      have hcard : N - 2 + 1 - 2 = N - 3 := by omega
      rw [hcard, nsmul_eq_mul, Nat.cast_sub (by omega : 3 ≤ N)]
      push_cast
      ring

/-- Reverse triangle inequality for the second-difference pairing, before
specializing to the Rudin–Shapiro exact evaluation. -/
theorem interior_pairing_perturbation (gpos gneg : ℤ → ℝ) (N : ℕ) (η ρ : ℝ)
    (hN : 4 ≤ N) (hη : 0 ≤ η)
    (h : AdmissibleSplit gpos gneg f (N - 1) η ρ) :
    |∑ k ∈ Icc 2 (N - 2), rudinShapiro k * secondDiff f (k : ℤ)| -
      6 * η * ((N : ℝ) - 3) ≤
    |∑ k ∈ Icc 2 (N - 2), rudinShapiro k *
      secondDiff (fun j => gpos j - gneg j) (k : ℤ)| := by
  have herr := interior_pairing_error gpos gneg N η ρ hN hη h
  have heq : (∑ k ∈ Icc 2 (N - 2), rudinShapiro k *
      secondDiff (fun j => gpos j - gneg j - f j) (k : ℤ)) =
      (∑ k ∈ Icc 2 (N - 2), rudinShapiro k *
        secondDiff (fun j => gpos j - gneg j) (k : ℤ)) -
      (∑ k ∈ Icc 2 (N - 2), rudinShapiro k * secondDiff f (k : ℤ)) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    rw [secondDiff_sub]
    ring
  rw [heq] at herr
  have hrev := abs_sub_abs_le_abs_sub
    (∑ k ∈ Icc 2 (N - 2), rudinShapiro k * secondDiff f (k : ℤ))
    (∑ k ∈ Icc 2 (N - 2), rudinShapiro k *
      secondDiff (fun j => gpos j - gneg j) (k : ℤ))
  rw [abs_sub_comm] at hrev
  linarith

/-- The dual bound (2.3) for precisely the interior Rudin–Shapiro test.
The Lévy measures in the two memberships may be infinite or nonatomic. -/
theorem interior_dual (gpos gneg : ℝ → ℝ) (m : ℕ)
    (hgp : IsLSym gpos) (hgn : IsLSym gneg) (hN : 4 ≤ 2 ^ m) :
    |∑ k ∈ Icc 2 (2 ^ m - 2), rudinShapiro k *
      secondDiff (fun j : ℤ => gpos (j : ℝ) - gneg (j : ℝ)) (k : ℤ)|
      ≤ (gpos 1 + gneg 1) * (Real.sqrt (2 * (2 ^ m : ℕ)) + 3) := by
  classical
  have hM (t : ℝ) :
      |∑ i : ↥(Icc 2 (2 ^ m - 2)), rudinShapiro i.val *
        Real.cos (((i.val : ℤ) : ℝ) * t)| ≤
        Real.sqrt (2 * (2 ^ m : ℕ)) + 3 := by
    simp only [Int.cast_natCast]
    rw [Finset.sum_coe_sort (Icc 2 (2 ^ m - 2))
      (fun k : ℕ => rudinShapiro k * Real.cos ((k : ℝ) * t))]
    exact RS.interior_cos_bound m t hN
  have hd := LSym.dual_general hgp hgn
    (fun i : ↥(Icc 2 (2 ^ m - 2)) => rudinShapiro i.val)
    (fun i => (i.val : ℤ)) (Real.sqrt (2 * (2 ^ m : ℕ)) + 3) hM
  rw [Finset.sum_coe_sort (Icc 2 (2 ^ m - 2))
    (fun k : ℕ => rudinShapiro k *
      secondDiff (RestrictInt (fun x => gpos x - gneg x)) (k : ℤ))] at hd
  exact hd

/-- Proposition 3.1 with the original symmetric Lévy hypotheses and the
original relative approximation and cancellation constraints. -/
theorem prop_3_1 (m : ℕ) (η ρ : ℝ) (gpos gneg : ℝ → ℝ)
    (hN : 16 ≤ 2 ^ m) (hη0 : 0 ≤ η) (hη : η < 1 / 6)
    (hpair : AdmissibleLSymPair gpos gneg f (2 ^ m - 1) η ρ) :
    (1 - 6 * η) * (((2 ^ m : ℕ) : ℝ) - 3) /
      (3 * (Real.sqrt (2 * (2 ^ m : ℕ)) + 3)) ≤ ρ := by
  have hN4 : 4 ≤ 2 ^ m := by omega
  have hp := interior_pairing_perturbation (RestrictInt gpos) (RestrictInt gneg)
    (2 ^ m) η ρ hN4 hη0 hpair.2.2
  have hexact := RS.abs_pairing_lower m hN
  have hdual := interior_dual gpos gneg m hpair.1 hpair.2.1 hN4
  have hcert : (1 - 6 * η) * (((2 ^ m : ℕ) : ℝ) - 3) ≤
      (gpos 1 + gneg 1) * (Real.sqrt (2 * (2 ^ m : ℕ)) + 3) := by
    change _ ≤ |∑ k ∈ Icc 2 (2 ^ m - 2), rudinShapiro k *
      secondDiff (fun j : ℤ => gpos (j : ℝ) - gneg (j : ℝ)) (k : ℤ)| at hp
    nlinarith
  have hs : gpos 1 + gneg 1 ≤ 3 * ρ := by
    have hi : |(1 : ℤ)| ≤ ((2 ^ m - 1 : ℕ) : ℤ) := by
      rw [abs_one]
      exact_mod_cast (show 1 ≤ 2 ^ m - 1 by omega)
    have hs' := hpair.2.2.2 1 hi
    simpa [RestrictInt, f_one, mul_comm] using hs'
  exact Bounds.prop_3_1_algebra (2 ^ m) η ρ (gpos 1 + gneg 1) hN hη hcert hs

end Paper02.LowerBound
