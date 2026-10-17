import Paper20.Semantics
import Paper20.Certs.H43
import Paper20.Certs.F43

/-! Verified finite differences of the ordinary-point Hilbert certificate.
This checks `(1-q)^43 H` and does not assume that the Hilbert certificate
has already been identified with the partition sum (13). -/
namespace Paper20.HilbertCertificate
open Paper20.Semantics Finset BigOperators

/-- Only the first `min b ℓ+1` terms can contribute to a residual coefficient. -/
theorem hilbertResidual_truncate (b ℓ : ℕ) (H : ℕ → ℤ) :
    hilbertResidual b H ℓ =
      ∑ i ∈ range (min b ℓ + 1), (-1 : ℤ)^i * (Nat.choose b i : ℤ) * H (ℓ-i) := by
  symm
  apply Finset.sum_subset (by intro i hi; simp only [mem_range] at *; omega)
  intro i hi hnot
  have hi' := Finset.mem_range.mp hi
  have hnot' : ¬ i < min b ℓ+1 := by simpa only [mem_range] using hnot
  have hbi : b < i := by omega
  rw [Nat.choose_eq_zero_of_lt hbi]
  simp

/-- The signed binomial row, using the proved fast implementation. -/
def binomialRow (b : ℕ) : List ℤ :=
  (List.range (b+1)).map (fun i => (-1 : ℤ)^i * (Nat.fast_choose b i : ℤ))

theorem binomialRow_get {b i : ℕ} (hi : i ≤ b) :
    (binomialRow b).getD i 0 = (-1 : ℤ)^i * (Nat.choose b i : ℤ) := by
  unfold binomialRow
  rw [List.getD_eq_getD_getElem?, List.getElem?_map,
    List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some]
  rw [Nat.choose_eq_fast_choose]

/-- Executable convolution against a supplied row. -/
def residualWithRow (row H : List ℤ) (ℓ : ℕ) : ℤ :=
  ((List.range (min row.length (ℓ+1))).map
    (fun i => row.getD i 0 * H.getD (ℓ-i) 0)).sum

lemma listSum_range_eq (f : ℕ → ℤ) (m : ℕ) :
    ((List.range m).map f).sum = ∑ i ∈ range m, f i := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.range_succ, Finset.sum_range_succ, ih]

/-- The executable convolution computes the coefficient of the formal series. -/
theorem residualWithRow_correct (b ℓ : ℕ) (H : List ℤ) :
    residualWithRow (binomialRow b) H ℓ =
      hilbertResidual b (fun i => H.getD i 0) ℓ := by
  rw [hilbertResidual_truncate]
  unfold residualWithRow
  have hlen : (binomialRow b).length = b+1 := by simp [binomialRow]
  rw [hlen, show min (b+1) (ℓ+1) = min b ℓ+1 by omega]
  rw [listSum_range_eq]
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ b := by simp only [mem_range] at hi; omega
  rw [binomialRow_get hi']

end Paper20.HilbertCertificate
