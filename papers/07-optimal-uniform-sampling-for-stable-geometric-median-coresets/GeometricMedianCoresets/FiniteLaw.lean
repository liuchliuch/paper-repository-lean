import Mathlib.Tactic

/-! Elementary finite total-variation and Hellinger-affinity inequalities used in Section 3. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace GeometricMedianCoresets.FiniteLaw

variable {α : Type*} [Fintype α]

def tv (u v : α → ℝ) : ℝ := (∑ a, |u a - v a|) / 2
def affinity (u v : α → ℝ) : ℝ := ∑ a, Real.sqrt (u a) * Real.sqrt (v a)
def event (u : α → ℝ) (E : α → Prop) : ℝ := ∑ a with E a, u a

lemma tv_nonneg (u v : α → ℝ) : 0 ≤ tv u v := by unfold tv; positivity

/-- Total variation bounds the difference on every event, using equal total masses. -/
theorem event_sub_le_tv (u v : α → ℝ) (hsum : ∑ a, u a = ∑ a, v a) (E : α → Prop) :
    |event u E - event v E| ≤ tv u v := by
  have htotal : (∑ a with E a, (u a - v a)) + (∑ a with ¬ E a, (u a - v a)) = 0 := by
    rw [Finset.sum_filter_add_sum_filter_not, Finset.sum_sub_distrib, hsum, sub_self]
  have htotalabs := Finset.sum_filter_add_sum_filter_not Finset.univ E (fun a => |u a - v a|)
  have h1 := Finset.abs_sum_le_sum_abs (fun a => u a - v a) (Finset.univ.filter E)
  have h2 := Finset.abs_sum_le_sum_abs (fun a => u a - v a) (Finset.univ.filter (fun a => ¬ E a))
  have hneg : (∑ a with ¬ E a, (u a - v a)) = -(∑ a with E a, (u a - v a)) := by linarith
  rw [hneg, abs_neg] at h2
  unfold event tv
  rw [← Finset.sum_sub_distrib]
  linarith

/-- Affinity controls total variation by Cauchy--Schwarz. -/
theorem tv_le_sqrt_affinity (u v : α → ℝ)
    (hu : ∀ a, 0 ≤ u a) (hv : ∀ a, 0 ≤ v a)
    (hsu : ∑ a, u a = 1) (hsv : ∑ a, v a = 1) :
    tv u v ≤ Real.sqrt (1 - affinity u v ^ 2) := by
  let f := fun a => |Real.sqrt (u a) - Real.sqrt (v a)|
  let g := fun a => Real.sqrt (u a) + Real.sqrt (v a)
  have hprod : ∀ a, f a * g a = |u a - v a| := by
    intro a
    dsimp [f, g]
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), ← abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt (hu a), Real.sq_sqrt (hv a)]
  have hminus : ∑ a, f a ^ 2 = 2 - 2 * affinity u v := by
    calc _ = ∑ a, (u a + v a - 2 * (Real.sqrt (u a) * Real.sqrt (v a))) := by
            apply Finset.sum_congr rfl
            intro a _
            dsimp [f]
            rw [sq_abs]
            nlinarith [Real.sq_sqrt (hu a), Real.sq_sqrt (hv a)]
      _ = _ := by simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, hsu, hsv, affinity]; ring
  have hplus : ∑ a, g a ^ 2 = 2 + 2 * affinity u v := by
    calc _ = ∑ a, (u a + v a + 2 * (Real.sqrt (u a) * Real.sqrt (v a))) := by
            apply Finset.sum_congr rfl
            intro a _
            dsimp [g]
            nlinarith [Real.sq_sqrt (hu a), Real.sq_sqrt (hv a)]
      _ = _ := by simp only [Finset.sum_add_distrib,
        ← Finset.mul_sum, hsu, hsv, affinity]; ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  simp_rw [hprod] at hcs
  rw [hminus, hplus] at hcs
  have hbound : tv u v ^ 2 ≤ 1 - affinity u v ^ 2 := by unfold tv; nlinarith [hcs]
  apply (Real.le_sqrt (tv_nonneg u v) (le_trans (sq_nonneg _) hbound)).2 hbound

end GeometricMedianCoresets.FiniteLaw
