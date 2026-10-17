import Paper20.SeriesIntegration

/-! Integer scaling of the genuine series integration recurrence. This
retains its formal power-series meaning while avoiding repeated rational
normalization in large exact partition calculations. -/
namespace Paper20.ScaledIntegration
open Finset
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def integrate (G : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | H+1 =>
    let prev := integrate G H
    prev ++ [((List.range (H+1)).map (fun i =>
      G.getD (i+1) 0*prev.getD (H-i) 0*
        ((H.factorial/(H-i).factorial:ℕ):ℤ))).sum]

@[simp] theorem integrate_length (G : List ℤ) (H : ℕ) : (integrate G H).length=H+1 := by
  induction H with
  | zero => rfl
  | succ H ih => simp [integrate, ih]

lemma factorial_ratio (H i : ℕ) :
    ((H.factorial/(H-i).factorial:ℕ):ℚ)*((H-i).factorial:ℚ) = (H.factorial:ℚ) := by
  exact_mod_cast Nat.div_mul_cancel (Nat.factorial_dvd_factorial (Nat.sub_le H i))

lemma sum_map_range_rat (f : ℕ → ℚ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

/-- The actual integer recurrence computes `H! L^H [w^H] R` whenever
its integer inputs are the corresponding scaled logarithmic derivative.
Only the defining differential equation and constant term are used. -/
theorem integrate_correct (G : List ℤ) (L : ℕ) (R F : PowerSeries ℚ)
    (h0 : PowerSeries.coeff 0 R=1)
    (hode : PowerSeries.derivative ℚ R=F*R) :
    ∀ H, (∀ i < H, (G.getD (i+1) 0:ℚ) =
        (L:ℚ)^(i+1)*PowerSeries.coeff i F) →
      ∀ j ≤ H, ((integrate G H).getD j 0:ℚ) =
        (L:ℚ)^j*(j.factorial:ℚ)*PowerSeries.coeff j R := by
  intro H
  induction H with
  | zero =>
    intro hG j hj
    have : j=0 := by omega
    subst j
    simp [integrate,h0]
  | succ H ih =>
    intro hG j hj
    rw [integrate]
    by_cases hjH : j ≤ H
    · rw [List.getD_append _ _ _ _ (by simp; omega)]
      exact ih (fun i hi => hG i (by omega)) j hjH
    · have he : j=H+1 := by omega
      subst j
      rw [List.getD_append_right _ _ _ _ (by simp), integrate_length, Nat.sub_self]
      simp only [List.getD_cons_zero]
      rw [Int.cast_list_sum, List.map_map]
      have hs : ((List.range (H+1)).map (fun i =>
          (G.getD (i+1) 0:ℚ)*((integrate G H).getD (H-i) 0:ℚ)*
            ((H.factorial/(H-i).factorial:ℕ):ℚ))).sum =
          (L:ℚ)^(H+1)*(H.factorial:ℚ)*
            ∑ i ∈ range (H+1), PowerSeries.coeff i F*PowerSeries.coeff (H-i) R := by
        rw [sum_map_range_rat, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hG i (Finset.mem_range.mp hi),
          ih (fun i hi => hG i (by omega)) (H-i) (by omega)]
        have hp : (L:ℚ)^(i+1)*(L:ℚ)^(H-i) = (L:ℚ)^(H+1) := by
          rw [← pow_add]
          congr 1
          have := Finset.mem_range.mp hi
          omega
        have hf := factorial_ratio H i
        calc
          _ = ((L:ℚ)^(i+1)*(L:ℚ)^(H-i))*
              (((H.factorial/(H-i).factorial:ℕ):ℚ)*((H-i).factorial:ℚ))*
              (PowerSeries.coeff i F*PowerSeries.coeff (H-i) R) := by ring
          _ = _ := by rw [hp,hf]
      have hc := congrArg (PowerSeries.coeff H) hode
      rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
      simp only [Function.comp_def, Int.cast_mul, Int.cast_natCast]
      rw [hs, ← hc, Nat.factorial_succ]
      push_cast
      ring

end
end Paper20.ScaledIntegration
