import Paper25.Liouville
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Diagonal

/-!
The exact Fourier expansion of specified-string controls and the reflection
in Section 4.3 / Appendix A.2. The sum includes the empty Pauli string, so its
scalar phase is not discarded. Gate decomposition and uniform generation are
separate obligations from these matrix identities.
-/
noncomputable section
namespace Paper25.PauliControls
open Matrix Finset

abbrev Bits (k : ℕ) := Fin k → Fin 2

def zSign (b : Fin 2) : ℂ := if b = 0 then 1 else -1

lemma zSign_mul (b x : Fin 2) : zSign b * zSign x = if b = x then 1 else -1 := by
  fin_cases b <;> fin_cases x <;> norm_num [zSign]

def pauliString {k : ℕ} (S : Finset (Fin k)) : Matrix (Bits k) (Bits k) ℂ :=
  Matrix.diagonal fun x => ∏ j ∈ S, zSign (x j)

def controlCoeff {k : ℕ} (b : Bits k) (S : Finset (Fin k)) : ℂ :=
  ∏ j ∈ S, zSign (b j)

def controlProjector {k : ℕ} (b : Bits k) : Matrix (Bits k) (Bits k) ℂ :=
  Matrix.diagonal fun x => if x = b then 1 else 0

lemma control_product {k : ℕ} (b x : Bits k) :
    (∏ j : Fin k, (1 + zSign (b j) * zSign (x j))) =
      if x = b then (2 : ℂ) ^ k else 0 := by
  classical
  by_cases h : x = b
  · subst x
    norm_num [zSign_mul]
  · rw [if_neg h]
    have hne : ∃ j, x j ≠ b j := by
      by_contra hn
      push_neg at hn
      exact h (funext hn)
    obtain ⟨j, hj⟩ := hne
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [zSign_mul, if_neg (Ne.symm hj)]
    norm_num

lemma control_fourier_sum {k : ℕ} (b x : Bits k) :
    (∑ S : Finset (Fin k), controlCoeff b S * ∏ j ∈ S, zSign (x j)) =
      if x = b then (2 : ℂ) ^ k else 0 := by
  classical
  have h := Finset.prod_one_add (f := fun j => zSign (b j) * zSign (x j))
    (Finset.univ : Finset (Fin k))
  rw [Finset.powerset_univ] at h
  simpa only [controlCoeff, Finset.prod_mul_distrib] using h.symm.trans (control_product b x)

/-- Exact projector expansion, including arbitrary positive/negative control
strings and the empty-set term. -/
theorem control_projector_expansion {k : ℕ} (b : Bits k) :
    controlProjector b = ((2 : ℂ) ^ k)⁻¹ •
      ∑ S : Finset (Fin k), controlCoeff b S • pauliString S := by
  classical
  ext x y
  by_cases h : x = y
  · subst y
    simp only [controlProjector, Matrix.diagonal_apply_eq, Matrix.smul_apply,
      Matrix.sum_apply, smul_eq_mul, pauliString]
    rw [control_fourier_sum]
    by_cases hb : x = b <;> simp [hb]
  · simp [controlProjector, pauliString, Matrix.sum_apply, Matrix.smul_apply, h]

lemma pauliString_empty (k : ℕ) : pauliString (∅ : Finset (Fin k)) = 1 := by
  simp [pauliString, Matrix.diagonal_one]

lemma pauliString_commute {k : ℕ} (S T : Finset (Fin k)) :
    Commute (pauliString S) (pauliString T) := by
  unfold pauliString
  change _ * _ = _ * _
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  ring

lemma controlProjector_idempotent {k : ℕ} (b : Bits k) :
    controlProjector b * controlProjector b = controlProjector b := by
  rw [controlProjector, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  split_ifs <;> norm_num

/-- The actual all-zero ancillary reflection in equation (20). -/
theorem zero_reflection_expansion (k : ℕ) :
    (2 : ℂ) • controlProjector (fun _ : Fin k => 0) - 1 =
      (2 / (2 : ℂ) ^ k) • ∑ S : Finset (Fin k), pauliString S - 1 := by
  rw [control_projector_expansion, smul_smul]
  congr 1
  simp [controlCoeff, zSign, div_eq_mul_inv]

end Paper25.PauliControls
