import Paper20.PowerSeriesBPS
import Paper20.HilbertCertificate

/-! Remark 2.1: the node normalization from its Hilbert series, together
with uniqueness of the BPS coefficients in the defining expansion. -/
namespace Paper20.Node
open Paper20.Semantics Paper20.HilbertCertificate Finset BigOperators

/-- Coefficients of `(1-q+q²)/(1-q)²`: `H₀=1` and `H_ℓ=ℓ` for `ℓ≥1`. -/
def H (ℓ : ℕ) : ℤ := if ℓ = 0 then 1 else ℓ

/-- The node's BPS polynomial is `1+w`. -/
def n (h : ℕ) : ℤ := if h ≤ 1 then 1 else 0

lemma residual (ℓ : ℕ) :
    hilbertResidual 2 H ℓ = if ℓ = 0 then 1 else if ℓ = 1 then -1 else if ℓ = 2 then 1 else 0 := by
  rw [hilbertResidual_truncate]
  rcases ℓ with _ | _ | _ | ℓ
  · norm_num [H]
  · norm_num [H, Finset.sum_range_succ]
  · norm_num [H, Finset.sum_range_succ]
  · have hm : min 2 (ℓ+3) = 2 := by omega
    rw [hm]
    norm_num [Finset.sum_range_succ, H]
    omega

lemma expansion (ℓ : ℕ) :
    expansionCoeff 1 n ℓ = if ℓ = 0 then 1 else if ℓ = 1 then -1 else if ℓ = 2 then 1 else 0 := by
  rcases ℓ with _ | _ | _ | ℓ
  · norm_num [expansionCoeff, n, Finset.sum_range_succ]
  · norm_num [expansionCoeff, n, Finset.sum_range_succ]
  · norm_num [expansionCoeff, n, Finset.sum_range_succ]
  · have h2 : Nat.choose 2 (ℓ+3) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h0 : Nat.choose 0 (ℓ+3-1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [expansionCoeff, n, Finset.sum_range_succ, h2, h0]

/-- The actual defining BPS identity for the node's Hilbert coefficients. -/
theorem local_expansion : localBPSExpansion 2 1 H n := by
  intro ℓ
  rw [residual, expansion]

/-- Formal-series version of Remark 2.1, with the stated Hilbert numerator. -/
theorem hilbert_identity :
    (1-PowerSeries.X)^2 * hilbertSeries H =
      1-PowerSeries.X+PowerSeries.X^2 := by
  rw [(localBPSExpansion_iff_series 2 1 H n).mp local_expansion]
  simp only [bpsSeries, Finset.sum_range_succ, Finset.sum_range_zero,
    n, Nat.sub_self, Nat.sub_zero, show (0:ℕ) ≤ 1 by omega,
    show (1:ℕ) ≤ 1 by omega, if_true, Nat.mul_zero, Nat.mul_one,
    pow_zero, pow_one, mul_one, one_mul, zero_add]
  norm_num
  ring

/-- Every sequence defined by the node Hilbert expansion has `n₀=n₁=1`. -/
theorem node_BPS {m : ℕ → ℤ} (hm : localBPSExpansion 2 1 H m) :
    m 0 = 1 ∧ m 1 = 1 := by
  have he := localBPSExpansion_unique hm local_expansion
  exact ⟨(he 0 (by decide)).trans (by rfl), (he 1 le_rfl).trans (by rfl)⟩

end Paper20.Node
