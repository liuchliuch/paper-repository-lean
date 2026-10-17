import Paper14.AppendixFirstGeometry
import Paper14.AppendixCountBasic

open MeasureTheory Set Finset
open scoped ENNReal
namespace Paper14
noncomputable section

/-- The actual Appendix A strip intersected with A_r. -/
def appendixStrip (r : ℝ) (p q : ℕ) : Set (ℝ × ℝ) :=
  {x ∈ appendixAr r | r < (q : ℝ)*x.2-(p : ℝ)*x.1 ∧ (q : ℝ)*x.2-(p : ℝ)*x.1 ≤ 1}

lemma measurableSet_appendixAr (r : ℝ) : MeasurableSet (appendixAr r) :=
  measurableSet_Omega.inter ((measurableSet_le measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const))

lemma measurableSet_appendixStrip (r : ℝ) (p q : ℕ) : MeasurableSet (appendixStrip r p q) :=
  by
    have hu : Measurable (fun x : ℝ × ℝ => (q : ℝ)*x.2-(p : ℝ)*x.1) := by fun_prop
    exact (measurableSet_appendixAr r).inter ((measurableSet_lt measurable_const hu).inter
      (measurableSet_le hu measurable_const))

/-- Every vector of F_2 has exactly the coefficient range (52). -/
lemma appendix_F2_coefficients {n : ℕ} {α : ℝ} (hα : 0 < α) (hε : α/(n : ℝ) < 1)
    {x : ℝ × ℝ} (hx : x ∈ appendixAr (1-α/(n : ℝ))) {p q : ℤ}
    (hrect : inZRect (2*n) ((2*α)/(2*n : ℕ)) x p q) :
    1 ≤ q ∧ q ≤ 4*(n : ℤ) ∧ 0 ≤ p ∧ p < 2*q := by
  have hn0 : n ≠ 0 := by
    intro hn
    subst n
    have hqneg : q ≤ 0 := by exact_mod_cast hrect.2.1
    have hqpos := hrect.1
    omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have heq : (2*α)/(2*n : ℕ) = α/(n : ℝ) := by push_cast; field_simp
  rw [heq] at hrect
  have hb := rectangle_coeff_bounds hx.1 hε hrect.2.2.1 hrect.2.2.2.1 hrect.2.2.2.2.1 hrect.2.2.2.2.2.1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hrect.1
  have hpR : (0 : ℝ) ≤ p := by exact_mod_cast hb.1
  have hΩ := mem_Omega_iff.mp hx.1
  have hu0 : 0 < (q : ℝ)*x.2-(p : ℝ)*x.1 := lt_trans (by linarith) hrect.2.2.1
  have hqt := mul_le_mul_of_nonneg_left hΩ.2.2.2 hqR.le
  have hps := mul_le_mul_of_nonneg_left hx.2.1 hpR
  have hplt : (p : ℝ) < 2*(q : ℝ) := by nlinarith
  exact ⟨by omega,by push_cast at hb; linarith [hb.2.2.2],hb.1,by exact_mod_cast hplt⟩

/-- Distinct p's with the same q cannot contribute together. -/
lemma appendix_same_q_disjoint {r : ℝ} (hr : (1 : ℝ)/2 < r) {p p' q : ℕ} (hpp : p ≠ p') :
    Disjoint (appendixStrip r p q) (appendixStrip r p' q) := by
  apply Set.disjoint_left.mpr
  intro x hx hx'
  have hs : (1 : ℝ)/2 ≤ x.1 := hx.1.2.1
  rcases lt_or_gt_of_ne hpp with hlt | hgt
  · have hppR : (p : ℝ)+1 ≤ p' := by exact_mod_cast hlt
    have hmul := mul_le_mul_of_nonneg_right hppR (by linarith : 0 ≤ x.1)
    nlinarith [hx.2.2,hx'.2.1]
  · have hppR : (p' : ℝ)+1 ≤ p := by exact_mod_cast hgt
    have hmul := mul_le_mul_of_nonneg_right hppR (by linarith : 0 ≤ x.1)
    nlinarith [hx'.2.2,hx.2.1]

/-- The actual determinant bounds (25), directly from any intersection point. -/
theorem appendix_intersection_determinant {n p q p' q' : ℕ} (hn : 0 < n)
    {α : ℝ} (hα : 0 < α) (hαs : α < 1/32)
    (hq : 0 < q) (hqq : q < q') (hq'n : q' ≤ 4*n)
    (hne : (appendixStrip (1-α/(n : ℝ)) p q ∩
      appendixStrip (1-α/(n : ℝ)) p' q').Nonempty) :
    (4 : ℝ)/5*((q' : ℝ)-q) ≤ (p' : ℝ)*q-(p : ℝ)*q' ∧
      (p' : ℝ)*q-(p : ℝ)*q' ≤ 4*((q' : ℝ)-q) := by
  obtain ⟨x,hx,hx'⟩ := hne
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'R : (0 : ℝ) < q' := by exact_mod_cast (by omega : 0 < q')
  have hq'nR : (q' : ℝ) ≤ 4*(n : ℝ) := by exact_mod_cast hq'n
  have hqqR : (q : ℝ)+1 ≤ q' := by exact_mod_cast hqq
  have hε0 : 0 ≤ α/(n : ℝ) := (div_pos hα hnR).le
  have heqn : (α/(n : ℝ))*(4*(n : ℝ)) = 4*α := by field_simp
  have hsmall' : (α/(n : ℝ))*(q' : ℝ) < 1/8 := by
    have hh := mul_le_mul_of_nonneg_left hq'nR hε0
    rw [heqn] at hh
    linarith
  have hsmall : (α/(n : ℝ))*(q : ℝ) < 1/8 :=
    (mul_le_mul_of_nonneg_left (by linarith : (q : ℝ) ≤ q') hε0).trans_lt hsmall'
  let D := (p' : ℝ)*q-(p : ℝ)*q'
  have heq : D*x.1 = (q' : ℝ)*((q : ℝ)*x.2-(p : ℝ)*x.1)-
      (q : ℝ)*((q' : ℝ)*x.2-(p' : ℝ)*x.1) := by dsimp [D]; ring
  have hl := mul_lt_mul_of_pos_left hx.2.1 hq'R
  have hu := mul_le_mul_of_nonneg_left hx'.2.2 hqR.le
  have hl' := mul_lt_mul_of_pos_left hx'.2.1 hqR
  have hu' := mul_le_mul_of_nonneg_left hx.2.2 hq'R.le
  have hlow : (q' : ℝ)-q-1/8 < D*x.1 := by nlinarith
  have hupp : D*x.1 < (q' : ℝ)-q+1/8 := by nlinarith
  have hs0 : 0 ≤ x.1 := by linarith [hx.1.2.1]
  have hs1 : x.1 ≤ 1 := (mem_Omega_iff.mp hx.1.1).2.1
  have hD : 0 < D := by
    by_contra h
    have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hs0
    nlinarith
  have hDs1 := mul_le_mul_of_nonneg_left hs1 hD.le
  have hDs0 := mul_le_mul_of_nonneg_left hx.1.2.1 hD.le
  change (4 : ℝ)/5*((q' : ℝ)-q) ≤ D ∧ D ≤ 4*((q' : ℝ)-q)
  constructor <;> nlinarith

end
end Paper14
