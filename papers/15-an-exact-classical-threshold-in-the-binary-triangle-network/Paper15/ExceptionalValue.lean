import Paper15.ExceptionalCalculus
import Paper15.Main

/-! # Value of every feasible interior stationary point

The stationary-point algebra is connected to the unique quartic root on the
whole positive range forced by the constraints, not just its isolating interval.
Existence of multipliers at an interior maximum is proved in Paper15.Lagrange.
The remaining global upper-bound obligations include boundary exclusion and
the full gap/reduction arguments.
-/
noncomputable section
namespace Paper15

lemma yQuartic_strictAntiOn_extended :
    StrictAntiOn yQuartic (Set.Ioo (0 : ℝ) (3/4)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _) continuous_yQuartic.continuousOn
  intro y hy
  rw [interior_Ioo] at hy
  rw [deriv_yQuartic]
  have hp := pow_lt_pow_left₀ hy.2 hy.1.le (by norm_num : (3 : ℕ) ≠ 0)
  norm_num at hp
  linarith

/-- Under positivity and both constraints, the symmetric law is unique and
its pair moment is exactly the threshold. -/
theorem exceptional_iid_value {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h1 : exceptionalM1 x y = 0) (h3 : exceptionalM3 x y = 0) :
    exceptionalM2 x y = tStar := by
  have hy0 : y ≠ 0 := hy.ne'
  have hyhi : y < 3/4 := by
    dsimp [exceptionalM1] at h1
    nlinarith [mul_pos hx hy]
  have hxeq : x = (1 - 2 * y^2) / (4 * y) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hy0)).mpr
    dsimp [exceptionalM1] at h1
    nlinarith
  have hq : yQuartic y = 0 := by
    rw [hxeq, exceptionalM3_subst hy0] at h3
    dsimp [exceptionalM3Sub] at h3
    field_simp at h3
    dsimp [yQuartic]
    nlinarith
  have hyrange : yRoot ∈ Set.Ioo (0 : ℝ) (3/4) := by
    have hlo := yRoot_gt_3861
    have hhi := yRoot_lt_3862
    constructor <;> linarith
  have hyeq : y = yRoot :=
    yQuartic_strictAntiOn_extended.injOn ⟨hy, hyhi⟩ hyrange (hq.trans yRoot_quartic.symm)
  have hxy : x = xAtt := by
    rw [hyeq] at hxeq
    exact hxeq
  rw [hxy, hyeq]
  calc
    exceptionalM2 xAtt yRoot = exceptionalM2Sub yRoot := exceptionalM2_xAtt
    _ = exceptionalM2Final yRoot := exceptionalM2Sub_eq_final_of_yRoot
    _ = tStar := attained_value_eq_tStar

/-- Every feasible interior constrained stationary point of the actual
exceptional model has value exactly `t_*`. -/
theorem exceptional_stationary_value {x y : Fin 3 → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hz : ∀ i, x i + y i < 1)
    (hstat : IsExceptionalStationary x y)
    (h1 : (momentsOf x y).M1 = 0) (h3 : (momentsOf x y).M3 = 0) :
    (momentsOf x y).M2 = tStar := by
  obtain ⟨hx01, hx12, hy01, hy12⟩ := lemma7_stationary hx hy hz hstat
  have hxf : x = fun _ => x 0 := by
    funext i
    fin_cases i
    · rfl
    · exact hx01.symm
    · exact (hx01.trans hx12).symm
  have hyf : y = fun _ => y 0 := by
    funext i
    fin_cases i
    · rfl
    · exact hy01.symm
    · exact (hy01.trans hy12).symm
  have heq (a b : ℝ) : momentsOf (fun _ => a) (fun _ => b) =
      AggregateMoments.mk (exceptionalM1 a b) (exceptionalM2 a b) (exceptionalM3 a b) := by
    change AggregateMoments.mk _ _ _ = AggregateMoments.mk _ _ _
    congr 1 <;>
      simp [momentsOf, m1Of, m2Of, m3Of, eQty, tQty, sQty, vQty, uOf,
        exceptionalM1, exceptionalM2, exceptionalM3] <;> ring
  rw [hxf, hyf, heq] at h1 h3 ⊢
  exact exceptional_iid_value (hx 0) (hy 0) h1 h3

end Paper15
