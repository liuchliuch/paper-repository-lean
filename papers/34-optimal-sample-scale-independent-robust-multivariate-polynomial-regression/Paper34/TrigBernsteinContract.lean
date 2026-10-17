import Paper34.Kernel
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-!
# The classical, external trigonometric Bernstein contract

External source: H. Queffélec and R. Zarouf, *On Bernstein's inequality for
polynomials*, arXiv:1903.10801, Theorem 1.1, §1.1:
https://arxiv.org/html/1903.10801#S1.SS1

For every complex trigonometric polynomial
`T(t) = ∑_{k=-d}^d a_k exp(i*k*t)` of degree at most `d ≥ 1`, the source states
`sup_t |T'(t)| ≤ d * sup_t |T(t)|`. `ClassicalTrigBernstein` below is its
pointwise upper-bound formulation: an arbitrary global upper bound `M ≥ 0`
on `|T|` bounds every `|T'|` by `d*M`. Every degree, function, upper bound,
point, and hypothesis is universally quantified.

The polynomial space is the complex linear span of exactly those genuine
Fourier characters whose integer frequencies have absolute value at most
`d`. This is the finite trigonometric polynomial space, with no assumed
derivative bound built into membership. It uses the same period-`2π` torus
and `fourier` characters as `Kernel` and `TensorNorming`.

The contract is an explicit proposition supplied by a caller, not a new Lean
axiom. All cosine/degree-space membership lemmas in this file are proved.
-/

namespace Paper34.TrigBernstein

noncomputable section

open scoped BigOperators

/-- The actual frequency-`k` Fourier character, lifted from the common torus. -/
def character (k : ℤ) : ℝ → ℂ := fun t => fourier k (t : Kernel.Torus)

/-- Exactly the complex span of frequencies `-d,…,d`. -/
def trigPolynomialSpace (d : ℕ) : Submodule ℂ (ℝ → ℂ) :=
  Submodule.span ℂ (character '' {k : ℤ | k.natAbs ≤ d})

theorem character_eq_exp (k : ℤ) (t : ℝ) :
    character k t = Complex.exp ((k : ℂ) * (t : ℂ) * Complex.I) := by
  rw [character, fourier_coe_apply]
  congr 1
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

theorem character_add (k l : ℤ) : character (k + l) = character k * character l := by
  funext t
  exact fourier_add

theorem character_mem (d : ℕ) (k : ℤ) (hk : k.natAbs ≤ d) :
    character k ∈ trigPolynomialSpace d :=
  Submodule.subset_span ⟨k, hk, rfl⟩

theorem trigPolynomialSpace_mono {r s : ℕ} (hrs : r ≤ s) :
    trigPolynomialSpace r ≤ trigPolynomialSpace s := by
  apply Submodule.span_mono
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨k, hk.trans hrs, rfl⟩

theorem constant_mem (d : ℕ) (a : ℂ) :
    (fun _ : ℝ => a) ∈ trigPolynomialSpace d := by
  have h := (trigPolynomialSpace d).smul_mem a (character_mem d 0 (by simp))
  have he : a • character 0 = (fun _ : ℝ => a) := by
    funext t
    simp only [Pi.smul_apply, character, fourier_zero, smul_eq_mul, mul_one]
  rw [← he]
  exact h

/-- Products add frequency bounds. This is an internal span-induction proof. -/
theorem mul_mem {r s : ℕ} {f g : ℝ → ℂ}
    (hf : f ∈ trigPolynomialSpace r) (hg : g ∈ trigPolynomialSpace s) :
    f * g ∈ trigPolynomialSpace (r + s) := by
  induction hf, hg using Submodule.span_induction₂ with
  | mem_mem u v hu hv =>
      rcases hu with ⟨k, hk, rfl⟩
      rcases hv with ⟨l, hl, rfl⟩
      rw [← character_add]
      exact character_mem (r + s) (k + l)
        ((Int.natAbs_add_le k l).trans (Nat.add_le_add hk hl))
  | zero_left => simp
  | zero_right => simp
  | add_left u v w _ _ _ huw hvw =>
      simpa only [add_mul] using add_mem huw hvw
  | add_right u v w _ _ _ huv huw =>
      simpa only [mul_add] using add_mem huv huw
  | smul_left a u v _ _ huv =>
      simpa only [smul_mul_assoc] using (trigPolynomialSpace (r + s)).smul_mem a huv
  | smul_right a u v _ _ huv =>
      simpa only [mul_smul_comm] using (trigPolynomialSpace (r + s)).smul_mem a huv

theorem cos_eq_characters :
    (fun t : ℝ => (Real.cos t : ℂ)) =
      (2 : ℂ)⁻¹ • (character 1 + character (-1)) := by
  funext t
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, character_eq_exp,
    Int.cast_one, Int.cast_neg, one_mul, neg_mul]
  rw [Complex.ofReal_cos, Complex.cos]
  ring

theorem cos_mem : (fun t : ℝ => (Real.cos t : ℂ)) ∈ trigPolynomialSpace 1 := by
  rw [cos_eq_characters]
  exact (trigPolynomialSpace 1).smul_mem _
    (add_mem (character_mem 1 1 (by decide)) (character_mem 1 (-1) (by decide)))

theorem cos_pow_mem (r : ℕ) :
    (fun t : ℝ => (Real.cos t : ℂ) ^ r) ∈ trigPolynomialSpace r := by
  induction r with
  | zero => simpa only [pow_zero] using constant_mem 0 1
  | succ r ih =>
      simpa only [Pi.mul_apply, pow_succ] using mul_mem ih cos_mem

/-- The sole external theorem contract in this file. Its function domain,
frequency bound, positivity condition, global norm bound and derivative point
are all explicit. It is used only after actual cosine-lift membership is proved. -/
def ClassicalTrigBernstein : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (T : ℝ → ℂ), T ∈ trigPolynomialSpace d →
    ∀ (M : ℝ), 0 ≤ M → (∀ t : ℝ, ‖T t‖ ≤ M) →
      ∀ t : ℝ, ‖deriv T t‖ ≤ (d : ℝ) * M

end

end Paper34.TrigBernstein
