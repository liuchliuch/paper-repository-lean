/-
Copyright (c) 2026. Matching extension that preserves the constraint
(Proposition 3.2) for the finite-field CHSH edge law.
-/
import Paper06.Basic
import Paper06.Constraints

open Real Set BigOperators
open scoped Classical

namespace Paper06

/-! ### The two-site edge law `R` -/

/-- Edge law `R((x,a),(x',b)) = r^{-3} · 1{a+b = x x'}` on `Z = R × R`. -/
noncomputable def edgeW {R : Type*} [Fintype R] [CommRing R]
    (z z' : R × R) : ℝ :=
  (Fintype.card R : ℝ) ^ (-3 : ℤ) *
    if z.2 + z'.2 = z.1 * z'.1 then 1 else 0

theorem edgeW_nonneg {R : Type*} [Fintype R] [CommRing R]
    (z z' : R × R) : 0 ≤ edgeW (R := R) z z' := by
  unfold edgeW
  by_cases h : z.2 + z'.2 = z.1 * z'.1
  · rw [if_pos h]
    positivity
  · rw [if_neg h, mul_zero]

/-- The input-marginal map `Γ q (x) = ∑_a q(x,a)`. -/
noncomputable def inputMarg {R : Type*} [Fintype R]
    (q : (R × R) → ℝ) : R → ℝ :=
  fun x => ∑ a, q (x, a)

/-- The target `η = u_r` is the uniform law on `R`. -/
noncomputable def uniformW (R : Type*) [Fintype R] : R → ℝ :=
  fun _ => (Fintype.card R : ℝ)⁻¹

/-- Two-site marginal weight `P_2 = (1/(n-1)) R + ((n-2)/(n-1)) u_Z^{⊗2}`. -/
theorem prop_3_2_convex_weights (n : ℕ) (hn : 3 ≤ n) :
    (1 / (n - 1 : ℝ)) + ((n - 2 : ℝ) / (n - 1 : ℝ)) = 1 := by
  have hne : (n - 1 : ℝ) ≠ 0 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn)
    linarith
  field_simp [hne]
  ring

/-- **Proposition 3.2**, edge-law nonnegativity (part of admissibility). -/
theorem prop_3_2_edge_nonneg' {R : Type*} [Fintype R] [CommRing R]
    (z z' : R × R) : 0 ≤ edgeW (R := R) z z' :=
  edgeW_nonneg z z'

/-- The edge law is symmetric under endpoint exchange when the game
relation is symmetric (`a+b = x x'` is symmetric in the two sites). -/
theorem edgeW_symm {R : Type*} [Fintype R] [CommRing R]
    (z z' : R × R) :
    edgeW (R := R) z z' = edgeW (R := R) z' z := by
  unfold edgeW
  by_cases h : z.2 + z'.2 = z.1 * z'.1
  · have h' : z'.2 + z.2 = z'.1 * z.1 := by
      rw [add_comm, mul_comm]
      exact h
    rw [if_pos h, if_pos h']
  · have h' : ¬ (z'.2 + z.2 = z'.1 * z.1) := by
      intro h'
      apply h
      rw [add_comm, mul_comm]
      exact h'
    rw [if_neg h, if_neg h']

end Paper06
