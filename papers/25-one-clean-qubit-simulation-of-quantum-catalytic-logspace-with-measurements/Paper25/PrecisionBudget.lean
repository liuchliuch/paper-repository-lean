import Paper25.DecisionFamilies

/-! Explicit binary precision choices for inverse-polynomial synthesis.
No elementary-function computation or circuit existence is assumed here. -/
noncomputable section
namespace Paper25.OperationalModel

theorem logarithmic_of_power_dimension {k : Input → ℕ}
    (h : PolynomialBound (fun x => 2^k x)) : LogarithmicBound k := by
  obtain ⟨C,d,h⟩ := h
  refine ⟨ceilLog2 C+d,?_⟩
  intro x
  let L := Nat.log2 (x.length+2)+1
  have hlength : x.length+1 ≤ 2^L := by
    have hp := Nat.lt_pow_succ_log_self (b := 2) (by decide) (x.length+2)
    rw [← Nat.log2_eq_log_two] at hp
    exact (by omega : x.length+1 ≤ x.length+2).trans hp.le
  have hdim : 2^k x ≤ 2^(ceilLog2 C+d*L) := by
    calc
      _ ≤ C*(x.length+1)^d := h x
      _ ≤ (2^ceilLog2 C)*(2^L)^d :=
        Nat.mul_le_mul (le_powerTwoCeil C) (Nat.pow_le_pow_left hlength d)
      _ = _ := by rw [← pow_mul, pow_add, Nat.mul_comm L]
  have hk := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 hdim
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hc : ceilLog2 C ≤ ceilLog2 C*L := by nlinarith
  change k x ≤ (ceilLog2 C+d)*L
  nlinarith

theorem precision_logarithmic {N : Input → ℕ} (hN : PolynomialBound N)
    (hpos : ∀ x, 0 < N x) : LogarithmicBound (fun x => ceilLog2 (N x)) :=
  logarithmic_of_power_dimension (hN.paddedPowerTwo hpos)

theorem precision_error {N : ℕ} (hN : 0 < N) :
    1/(2:ℝ)^ceilLog2 N ≤ 1/(N:ℝ) := by
  apply one_div_le_one_div_of_le
  · exact_mod_cast hN
  · exact_mod_cast le_powerTwoCeil N

/-- A precision budget can charge a polynomial upper bound on the number of
approximated gates without computing any matrix dimension of the catalyst. -/
theorem per_gate_precision {D N : ℕ} (hD : 0 < D) (hN : 0 < N) :
    1/(2:ℝ)^ceilLog2 (D*N) ≤ (1/(D:ℝ))/(N:ℝ) := by
  have h := precision_error (Nat.mul_pos hD hN)
  simpa only [Nat.cast_mul, div_div] using h

theorem precision_family {D N : Input → ℕ} (hD : PolynomialBound D)
    (hN : PolynomialBound N) (hDp : ∀ x, 0 < D x) (hNp : ∀ x, 0 < N x) :
    LogarithmicBound (fun x => ceilLog2 (D x*N x)) ∧
      ∀ x, 1/(2:ℝ)^ceilLog2 (D x*N x) ≤ (1/(D x:ℝ))/(N x:ℝ) :=
  ⟨precision_logarithmic (hD.mul hN) (fun x => Nat.mul_pos (hDp x) (hNp x)),
    fun x => per_gate_precision (hDp x) (hNp x)⟩

end Paper25.OperationalModel
