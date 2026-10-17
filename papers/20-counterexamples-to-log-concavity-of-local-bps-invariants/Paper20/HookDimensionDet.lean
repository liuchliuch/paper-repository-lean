import Paper20.HookIntegrality

namespace Paper20.HookDeterminant
open Polynomial Matrix Finset Paper20.HookBeta
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

/-- The determinant orientation of strictly decreasing beta numbers. -/
def betaSign (μ : YoungDiagram) : ℤ :=
  ∏ i : rows μ, (-1:ℤ)^((Ioi i).card)

lemma betaSign_sq (μ : YoungDiagram) : betaSign μ*betaSign μ=1 := by
  rw [betaSign,← Finset.prod_mul_distrib]
  have he (i : rows μ) : (-1:ℤ)^((Ioi i).card)*(-1:ℤ)^((Ioi i).card)=1 := by
    rw [← pow_add,← two_mul, pow_mul]
    simp
  simp_rw [he]
  exact Finset.prod_const_one

/-- The signed beta Vandermonde, before taking absolute values. -/
theorem betaDet_signed (μ : YoungDiagram) : betaDet μ=betaSign μ*(betaDelta μ:ℤ) := by
  rw [betaDet,Matrix.det_vandermonde,betaSign,betaDelta,Nat.cast_prod,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Nat.cast_prod,← Finset.prod_const,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hlt : i<j := mem_Ioi.mp hj
  have hb : betaVector μ j ≤ betaVector μ i := (beta_strict μ i.val j.val hlt j.isLt).le
  rw [Nat.cast_sub hb]
  ring

/-- Exact determinant formula for the actual natural hook quotient.
It is derived from the proved hook product and exact dimension, not used
as a replacement definition for that quotient. -/
theorem actual_dim_factorial_det {n : ℕ} (p : Part n) :
    (dimOf n p.parts:ℚ)=
      (betaSign p.diagram:ℚ)*(n.factorial:ℚ)*
        (factorialMatrix (betaVector p.diagram) (fun i : rows p.diagram => i.val)).det := by
  let H : ℕ := (hooksOf p.parts).prod
  let D := betaDelta p.diagram
  have hD : D ≠ 0 := betaDelta_ne_zero p.diagram
  have hH : H ≠ 0 := by
    intro hz
    have he := actual_dim_mul_hooks p
    change dimOf n p.parts*H=n.factorial at he
    rw [hz,mul_zero] at he
    exact Nat.factorial_ne_zero n he.symm
  have hc := factorialMatrix_det_clear p.diagram
  have hv := hook_beta_factor p.diagram
  rw [← actual_hook_product p] at hv
  have hd := congrArg (fun a : ℕ => (a:ℚ)) (actual_dim_mul_hooks p)
  simp only [Nat.cast_mul] at hd
  have hs := congrArg (fun a : ℤ => (a:ℚ)) (betaSign_sq p.diagram)
  simp only [Int.cast_mul,Int.cast_one] at hs
  have hprod : ((H*D:ℕ):ℚ)*
      (factorialMatrix (betaVector p.diagram) (fun i : rows p.diagram => i.val)).det=
        (betaSign p.diagram:ℚ)*(D:ℚ) := by
    rw [show H*D=∏ i : rows p.diagram, (betaVector p.diagram i).factorial from hv,hc,
      betaDet_signed,Int.cast_mul,Int.cast_natCast]
  have hDn : (D:ℚ) ≠ 0 := by exact_mod_cast hD
  have hHn : (H:ℚ) ≠ 0 := by exact_mod_cast hH
  apply (mul_left_cancel₀ hHn)
  apply (mul_left_cancel₀ hDn)
  dsimp only [H] at *
  simp only [Nat.cast_mul] at hprod
  linear_combination (norm := ring_nf)
    (D:ℚ)*hd - (betaSign p.diagram:ℚ)*(n.factorial:ℚ)*hprod
    - (D:ℚ)*(n.factorial:ℚ)*hs

end
end Paper20.HookDeterminant
