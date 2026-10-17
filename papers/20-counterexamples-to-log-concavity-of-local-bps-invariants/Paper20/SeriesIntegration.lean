import Paper20.LogSeries

namespace Paper20.LogSeries
open Finset
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

@[simp] theorem rFromGamma_length (γ : List ℚ) (H : ℕ) :
    (rFromGamma γ H).length = H+1 := by
  induction H with
  | zero => rfl
  | succ H ih => simp [rFromGamma, ih]

/-- The actual integration loop (29) computes any normalized solution of
`R'=G R` from the corresponding logarithmic derivative coefficients. -/
theorem rFromGamma_correct (γ : List ℚ) (R G : PowerSeries ℚ)
    (h0 : PowerSeries.coeff 0 R = 1)
    (hode : PowerSeries.derivative ℚ R = G*R) :
    ∀ H, (∀ i < H, γ.getD (i+1) 0 = PowerSeries.coeff i G) →
      ∀ j ≤ H, (rFromGamma γ H).getD j 0 = PowerSeries.coeff j R := by
  intro H
  induction H with
  | zero =>
    intro hγ j hj
    have : j=0 := by omega
    subst j
    exact h0.symm
  | succ H ih =>
    intro hγ j hj
    rw [rFromGamma]
    by_cases hlt : j ≤ H
    · rw [List.getD_append _ _ _ _ (by simp; omega)]
      exact ih (fun i hi => hγ i (by omega)) j hlt
    · have he : j=H+1 := by omega
      subst j
      rw [List.getD_append_right _ _ _ _ (by simp), rFromGamma_length, Nat.sub_self]
      simp only [List.getD_cons_zero]
      simp only [Nat.add_sub_cancel]
      have hc := congrArg (PowerSeries.coeff H) hode
      rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
      have hs : ((List.range (H+1)).map (fun i => γ.getD (i+1) 0*
          (rFromGamma γ H).getD (H-i) 0)).sum =
          ∑ i ∈ range (H+1), PowerSeries.coeff i G*PowerSeries.coeff (H-i) R := by
        rw [sum_map_range]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hγ i (by simpa using Finset.mem_range.mp hi),
          ih (fun i hi => hγ i (by omega)) (H-i) (by omega)]
      rw [hs]
      push_cast at hc ⊢
      apply (div_eq_iff (by positivity : (H+1:ℚ) ≠ 0)).2
      simpa [mul_comm] using hc.symm

end
end Paper20.LogSeries
