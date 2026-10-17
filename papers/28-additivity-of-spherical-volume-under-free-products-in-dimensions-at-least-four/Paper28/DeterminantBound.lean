import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The complementary 2-plane determinant estimate in the proof of Lemma 2.1.
All objects below are actual real matrices and their usual determinants. -/
set_option autoImplicit false
noncomputable section
namespace Paper28

/-- Cauchy--Schwarz in the exact scalar form used in Lemma 2.1. -/
theorem complementary_sqrt_bound (a b : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) :
    Real.sqrt (a * b) + Real.sqrt ((1 - a) * (1 - b)) ≤ 1 := by
  let x := Real.sqrt a
  let y := Real.sqrt b
  let z := Real.sqrt (1 - a)
  let w := Real.sqrt (1 - b)
  have hx : x ^ 2 = a := Real.sq_sqrt ha₀
  have hy : y ^ 2 = b := Real.sq_sqrt hb₀
  have hz : z ^ 2 = 1 - a := Real.sq_sqrt (sub_nonneg.mpr ha₁)
  have hw : w ^ 2 = 1 - b := Real.sq_sqrt (sub_nonneg.mpr hb₁)
  rw [Real.sqrt_mul ha₀, Real.sqrt_mul (sub_nonneg.mpr ha₁)]
  change x * y + z * w ≤ 1
  nlinarith [sq_nonneg (x * w - z * y)]

/-- The sum of the square-root determinants of complementary PSD 2x2
Gram matrices is at most one, as in S2.Ex10--S2.Ex12. -/
theorem complementary_det_bound (D : Matrix (Fin 2) (Fin 2) ℝ)
    (hD : D.PosSemidef) (hC : (1 - D).PosSemidef) :
    Real.sqrt D.det + Real.sqrt (1 - D).det ≤ 1 := by
  have hdiag (i : Fin 2) : 0 ≤ D i i := by
    simpa using hD.2 (Pi.single i 1)
  have hdiagC (i : Fin 2) : D i i ≤ 1 := by
    have h : 0 ≤ (1 - D) i i := by
      simpa using hC.2 (Pi.single i 1)
    simpa using h
  have hsym : D 1 0 = D 0 1 := by
    have h := congrFun (congrFun hD.isHermitian.eq 0) 1
    simpa using h
  have hdet : D.det ≤ D 0 0 * D 1 1 := by
    rw [Matrix.det_fin_two, hsym]
    nlinarith [sq_nonneg (D 0 1)]
  have hdetC : (1 - D).det ≤ (1 - D 0 0) * (1 - D 1 1) := by
    have hn01 : (0 : Fin 2) ≠ 1 := by decide
    have hn10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [Matrix.det_fin_two, Matrix.sub_apply, Matrix.one_apply,
      ite_true, if_neg hn01, if_neg hn10, zero_sub]
    rw [hsym]
    nlinarith [sq_nonneg (D 0 1)]
  exact (add_le_add (Real.sqrt_le_sqrt hdet) (Real.sqrt_le_sqrt hdetC)).trans
    (complementary_sqrt_bound _ _ (hdiag 0) (hdiagC 0) (hdiag 1) (hdiagC 1))

/-- Equivalent formulation with two explicitly named complementary matrices. -/
theorem two_gram_det_bound (D E : Matrix (Fin 2) (Fin 2) ℝ)
    (hD : D.PosSemidef) (hE : E.PosSemidef) (hDE : D + E = 1) :
    Real.sqrt D.det + Real.sqrt E.det ≤ 1 := by
  have heq : E = 1 - D := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm] using hDE
  subst E
  exact complementary_det_bound D hD hE

end Paper28
