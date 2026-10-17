import P31.AdditionalClaims

/-! The paper's own objective-plus-descent calculation in §7.2.  The
accelerated objective budget [4] and the standard smooth steepest-descent
decrease are explicit hypotheses on actual objective values and gradients.
Neither external algorithm is reconstructed here. -/
noncomputable section
open scoped BigOperators
namespace P31
variable {ι : Type*} [Fintype ι]

lemma objective_descent_exponent {p : ℝ} (hp : p ≠ 0) :
    2*((p+1)/p)-1 = 1+2/p := by field_simp; ring

lemma objective_descent_query_exponent {p : ℝ} (hp : 0 < p) :
    1/((p+1)/p) = p/(p+1) := by field_simp

lemma continuation_decay_gain {p : ℝ} (hp : p ≠ 0) :
    (p+2)/p-(p+1)/p = 1/p := by field_simp; ring

/-- Telescoping descent converts a supplied accelerated objective budget
into the displayed best-gradient rate. All gradients are actual vectors. -/
theorem objective_plus_descent_rate {p q C L R : ℝ} (hp : 2 ≤ p)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (f : (ι → ℝ) → ℝ) (g : (ι → ℝ) → ι → ℝ) (x : ℕ → ι → ℝ)
    (xstar : ι → ℝ) (N : ℕ) (hN : 0 < N)
    (hmin : ∀ y, f xstar ≤ f y)
    (hobjective : f (x 0)-f xstar ≤ C*L*R^2/(N:ℝ)^(1+2/p))
    (hdescent : ∀ j, j<N → lpNorm q (g (x j))^2 ≤ 2*L*(f (x j)-f (x (j+1)))) :
    ∃ j, j<N ∧ lpNorm q (g (x j)) ≤ Real.sqrt (2*C)*L*R/(N:ℝ)^((p+1)/p) := by
  let B := Real.sqrt (2*C)*L*R/(N:ℝ)^((p+1)/p)
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hpow : 0 < (N:ℝ)^((p+1)/p) := Real.rpow_pos_of_pos hn _
  have hB : 0 ≤ B := div_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hL) hR) hpow.le
  have hp0 : p ≠ 0 := ne_of_gt (show 0<p by linarith)
  have hexp : 2*((p+1)/p) = (1+2/p)+1 := by field_simp; ring
  have hden : ((N:ℝ)^((p+1)/p))^2 = (N:ℝ)^(1+2/p)*(N:ℝ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hn.le]
    rw [mul_comm, hexp, Real.rpow_add hn, Real.rpow_one]
  have hidentity : (N:ℝ)*B^2 = 2*L*(C*L*R^2/(N:ℝ)^(1+2/p)) := by
    dsimp [B]
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), hden]
    field_simp
  have htelall : ∀ n, ∑ j ∈ Finset.range n, (f (x j)-f (x (j+1))) = f (x 0)-f (x n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  have hsum : ∑ j ∈ Finset.range N, lpNorm q (g (x j))^2 ≤ ∑ _j ∈ Finset.range N, B^2 := by
    calc
      _ ≤ ∑ j ∈ Finset.range N, 2*L*(f (x j)-f (x (j+1))) :=
        Finset.sum_le_sum (fun j hj => hdescent j (Finset.mem_range.mp hj))
      _ = 2*L*(f (x 0)-f (x N)) := by rw [← Finset.mul_sum, htelall N]
      _ ≤ 2*L*(C*L*R^2/(N:ℝ)^(1+2/p)) :=
        mul_le_mul_of_nonneg_left (by linarith [hmin (x N)]) (by positivity)
      _ = _ := by simp [← hidentity]
  obtain ⟨j,hj,hjle⟩ := Finset.exists_le_of_sum_le (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN)) hsum
  refine ⟨j, Finset.mem_range.mp hj, ?_⟩
  nlinarith [lpNorm_nonneg q (g (x j))]

end P31
