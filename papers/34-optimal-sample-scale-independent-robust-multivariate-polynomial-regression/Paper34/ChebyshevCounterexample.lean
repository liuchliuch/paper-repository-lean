import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Chebyshev counterexample at the bare grid scale

This file proves Remark 3.5 of the paper. We index the paper's cells by
`Fin d`, so `j` below corresponds to the paper's index `j + 1`.
-/

namespace Paper34.ChebyshevCounterexample

noncomputable section

open Polynomial

/-- The angular midpoint of the `j`-th of `d` angular cells. -/
def angle (d : ℕ) (j : Fin d) : ℝ :=
  ((j : ℕ) + (1 / 2 : ℝ)) * Real.pi / d

/-- The zero of the first-kind Chebyshev polynomial in the `j`-th cell. -/
noncomputable def node (d : ℕ) (j : Fin d) : ℝ := Real.cos (angle d j)

/-- The closed Chebyshev cell, with zero-based indexing. -/
def cell (d : ℕ) (j : Fin d) : Set ℝ :=
  Set.Icc (Real.cos (((j : ℕ) + (1 : ℝ)) * Real.pi / d))
    (Real.cos ((j : ℕ) * Real.pi / d))

lemma angle_bounds (d : ℕ) (hd : 1 ≤ d) (j : Fin d) :
    (j : ℕ) * Real.pi / d ≤ angle d j ∧
      angle d j ≤ ((j : ℕ) + (1 : ℝ)) * Real.pi / d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  constructor
  · unfold angle
    apply (div_le_div_iff_of_pos_right hd').2
    nlinarith [Real.pi_pos]
  · unfold angle
    apply (div_le_div_iff_of_pos_right hd').2
    nlinarith [Real.pi_pos]

lemma node_mem_cell (d : ℕ) (hd : 1 ≤ d) (j : Fin d) : node d j ∈ cell d j := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hj : (j : ℝ) + 1 ≤ d := by exact_mod_cast (Nat.succ_le_iff.mpr j.isLt)
  have hb := angle_bounds d hd j
  have hleft : (0 : ℝ) ≤ (j : ℕ) * Real.pi / d := by positivity
  have hright : ((j : ℕ) + (1 : ℝ)) * Real.pi / d ≤ Real.pi := by
    apply (div_le_iff₀ hd').2
    nlinarith [Real.pi_pos]
  constructor
  · exact Real.cos_le_cos_of_nonneg_of_le_pi (hleft.trans hb.1) hright hb.2
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hleft (hb.2.trans hright) hb.1

lemma chebyshev_eval_node (d : ℕ) (hd : 1 ≤ d) (j : Fin d) :
    (Polynomial.Chebyshev.T ℝ (d : ℤ)).eval (node d j) = 0 := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  unfold node
  rw [Polynomial.Chebyshev.T_real_cos]
  have hang : ((d : ℤ) : ℝ) * angle d j = Real.pi / 2 + (j : ℕ) * Real.pi := by
    unfold angle
    push_cast
    field_simp
    ring
  rw [hang, Real.cos_add_nat_mul_pi]
  simp

lemma chebyshev_ne_zero (d : ℕ) : Polynomial.Chebyshev.T ℝ (d : ℤ) ≠ 0 := by
  intro hz
  have h := Polynomial.Chebyshev.T_eval_one ℝ (d : ℤ)
  rw [hz] at h
  norm_num at h

/-- The first-kind Chebyshev polynomial has degree at most its natural index. -/
lemma chebyshev_natDegree_le (d : ℕ) :
    (Polynomial.Chebyshev.T ℝ (d : ℤ)).natDegree ≤ d := by
  induction d using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more d ih ih1 =>
    rw [show ((d + 2 : ℕ) : ℤ) = (d : ℤ) + 2 by omega,
      Polynomial.Chebyshev.T_add_two]
    have ih1' : (Polynomial.Chebyshev.T ℝ ((d : ℤ) + 1)).natDegree ≤ d + 1 := by
      simpa using ih1
    calc
      _ ≤ max (2 * Polynomial.X * Polynomial.Chebyshev.T ℝ ((d : ℤ) + 1)).natDegree
          (Polynomial.Chebyshev.T ℝ (d : ℤ)).natDegree := Polynomial.natDegree_sub_le _ _
      _ ≤ d + 2 := by
        apply max_le
        · calc
            _ ≤ (2 * (Polynomial.X : ℝ[X])).natDegree +
                (Polynomial.Chebyshev.T ℝ ((d : ℤ) + 1)).natDegree :=
              Polynomial.natDegree_mul_le
            _ ≤ 1 + (d + 1) := by
              apply Nat.add_le_add _ ih1'
              calc
                _ ≤ (2 : ℝ[X]).natDegree + (Polynomial.X : ℝ[X]).natDegree :=
                  Polynomial.natDegree_mul_le
                _ = 1 := by norm_num
            _ = d + 2 := by omega
        · omega

/-- Remark 3.5: at `m = d`, every cell admits a representative annihilating the
same nonzero polynomial of degree at most `d`. -/
theorem remark_3_5 (d : ℕ) (hd : 1 ≤ d) :
    ∃ q : ℝ[X], q ≠ 0 ∧ q.natDegree ≤ d ∧
      ∃ representatives : Fin d → ℝ,
        (∀ j, representatives j ∈ cell d j) ∧
        (∀ j, q.eval (representatives j) = 0) := by
  exact ⟨Polynomial.Chebyshev.T ℝ (d : ℤ), chebyshev_ne_zero d,
    chebyshev_natDegree_le d, node d, node_mem_cell d hd, chebyshev_eval_node d hd⟩

/-- In particular, these representative evaluations do not determine a
polynomial of degree at most `d`. -/
theorem representative_evaluation_not_injective (d : ℕ) (hd : 1 ≤ d) :
    ¬ Function.Injective (fun q : {q : ℝ[X] // q.natDegree ≤ d} =>
      fun j : Fin d => q.val.eval (node d j)) := by
  intro h
  have heq : (⟨Polynomial.Chebyshev.T ℝ (d : ℤ), chebyshev_natDegree_le d⟩ :
      {q : ℝ[X] // q.natDegree ≤ d}) = ⟨0, by simp⟩ := by
    apply h
    funext j
    simpa using chebyshev_eval_node d hd j
  exact chebyshev_ne_zero d (congrArg Subtype.val heq)


/-- The algebraic identity in (6.3), expressing the normalized endpoint-cell
width as a squared sine. This is a statement about real widths. -/
lemma uniform_endpoint_width_identity (m : ℕ) (hm : 1 ≤ m) :
    (1 - Real.cos (Real.pi / m)) / 2 =
      Real.sin (Real.pi / (2 * m)) ^ 2 := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [Real.sin_sq_eq_half_sub]
  have hang : 2 * (Real.pi / (2 * (m : ℝ))) = Real.pi / m := by
    field_simp
  rw [hang]
  ring

/-- The quantitative bound in (6.3), proved with Jordan's inequality. -/
lemma uniform_endpoint_width_lower_bound (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ)⁻¹ ^ 2 ≤ (1 - Real.cos (Real.pi / m)) / 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hang : Real.pi / (2 * (m : ℝ)) ≤ Real.pi / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * m)).2
    nlinarith [Real.pi_pos]
  have hs := Real.mul_le_sin (x := Real.pi / (2 * (m : ℝ))) (by positivity) hang
  have hs' : (m : ℝ)⁻¹ ≤ Real.sin (Real.pi / (2 * (m : ℝ))) := by
    convert hs using 1
    field_simp
  rw [uniform_endpoint_width_identity m hm]
  exact pow_le_pow_left₀ (by positivity) hs' 2


/-- Each angular midpoint stays at least half a cell away from both endpoints. -/
lemma angle_endpoint_distance (m : ℕ) (hm : 1 ≤ m) (j : Fin m) :
    Real.pi / (2 * m) ≤ angle m j ∧
      angle m j ≤ Real.pi - Real.pi / (2 * m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hm'
  have hj : (j : ℝ) + 1 ≤ m := by exact_mod_cast (Nat.succ_le_iff.mpr j.isLt)
  have hmid : angle m j * m = ((j : ℕ) + (1 / 2 : ℝ)) * Real.pi := by
    unfold angle
    field_simp
  have hhalf : Real.pi / (2 * (m : ℝ)) * m = Real.pi / 2 := by
    field_simp
  constructor
  · apply (mul_le_mul_iff_left₀ hm').mp
    rw [hmid, hhalf]
    nlinarith [mul_nonneg (Nat.cast_nonneg (j : ℕ) : (0 : ℝ) ≤ j) Real.pi_pos.le]
  · apply (mul_le_mul_iff_left₀ hm').mp
    rw [hmid]
    have hjp := mul_le_mul_of_nonneg_right hj Real.pi_pos.le
    nlinarith [hhalf]

/-- The normalized length of a cell is a product of two sines. -/
lemma uniform_cell_width_identity (m : ℕ) (hm : 1 ≤ m) (j : Fin m) :
    (Real.cos ((j : ℕ) * Real.pi / m) -
        Real.cos (((j : ℕ) + (1 : ℝ)) * Real.pi / m)) / 2 =
      Real.sin (angle m j) * Real.sin (Real.pi / (2 * m)) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [Real.cos_sub_cos]
  have hsum : ((j : ℕ) * Real.pi / m +
      ((j : ℕ) + (1 : ℝ)) * Real.pi / m) / 2 = angle m j := by
    unfold angle
    field_simp
    ring
  have hdiff : ((j : ℕ) * Real.pi / m -
      ((j : ℕ) + (1 : ℝ)) * Real.pi / m) / 2 = -(Real.pi / (2 * m)) := by
    field_simp
    ring
  rw [hsum, hdiff, Real.sin_neg]
  ring

/-- An endpoint cell has the smallest normalized width among the Chebyshev
cells. This is the geometric minimum claim used before (6.3). -/
lemma endpoint_width_le_cell_width (m : ℕ) (hm : 1 ≤ m) (j : Fin m) :
    (1 - Real.cos (Real.pi / m)) / 2 ≤
      (Real.cos ((j : ℕ) * Real.pi / m) -
        Real.cos (((j : ℕ) + (1 : ℝ)) * Real.pi / m)) / 2 := by
  have hb := angle_endpoint_distance m hm j
  have hhalf0 : (0 : ℝ) ≤ Real.pi / (2 * m) := by positivity
  have hhalfpi : Real.pi / (2 * (m : ℝ)) ≤ Real.pi / 2 := by linarith
  have hsin : Real.sin (Real.pi / (2 * (m : ℝ))) ≤ Real.sin (angle m j) := by
    by_cases hjhalf : angle m j ≤ Real.pi / 2
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hjhalf hb.1
    · have hreflect : Real.pi - angle m j ≤ Real.pi / 2 := by linarith
      have hlower : Real.pi / (2 * (m : ℝ)) ≤ Real.pi - angle m j := by linarith
      simpa using Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ Real.pi / (2 * (m : ℝ)))
        hreflect hlower
  rw [uniform_endpoint_width_identity m hm, uniform_cell_width_identity m hm j, pow_two]
  exact mul_le_mul_of_nonneg_right hsin
    (Real.sin_nonneg_of_nonneg_of_le_pi hhalf0 (by linarith [Real.pi_pos]))

/-- Every normalized one-dimensional cell width is at least `m⁻²`. -/
lemma uniform_cell_width_lower_bound (m : ℕ) (hm : 1 ≤ m) (j : Fin m) :
    (m : ℝ)⁻¹ ^ 2 ≤
      (Real.cos ((j : ℕ) * Real.pi / m) -
        Real.cos (((j : ℕ) + (1 : ℝ)) * Real.pi / m)) / 2 :=
  (uniform_endpoint_width_lower_bound m hm).trans (endpoint_width_le_cell_width m hm j)

end

end Paper34.ChebyshevCounterexample
