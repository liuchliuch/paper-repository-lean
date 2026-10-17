import Paper14.MapBCZ
import Paper14.MeasureOmega
import Paper14.CountableBranches
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.Arithmetic

/-! Paper S2.p3: the BCZ map preserves normalized area on the Farey triangle. -/
open MeasureTheory Measure Set Function
open scoped ENNReal
namespace Paper14
noncomputable section

lemma measurable_B : Measurable B := by unfold B; fun_prop
lemma measurable_Binv : Measurable Binv := by unfold Binv; fun_prop

def branchEquiv (k : ℤ) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun := branchMap k
  invFun := fun x => ((k : ℝ) * x.1 - x.2, x.1)
  left_inv := by intro x; ext <;> simp [branchMap]
  right_inv := by intro x; ext <;> simp [branchMap]
  measurable_toFun := by change Measurable (branchMap k); unfold branchMap; fun_prop
  measurable_invFun := by change Measurable (fun x : ℝ × ℝ => ((k : ℝ) * x.1 - x.2, x.1)); fun_prop

lemma measurePreserving_branch (k : ℤ) :
    MeasurePreserving (branchEquiv k) volume volume := by
  have hskew : MeasurePreserving
      (fun x : ℝ × ℝ => (x.1, (k : ℝ) * x.1 - x.2))
      ((volume : Measure ℝ).prod volume) (volume.prod volume) := by
    refine (MeasurePreserving.id (volume : Measure ℝ)).skew_product
      (g := fun a b : ℝ => (k : ℝ) * a - b) (μc := volume) (μd := volume) (by fun_prop) ?_
    filter_upwards [] with a
    exact ((measurePreserving_add_left volume ((k : ℝ) * a)).comp
      (by
        refine ⟨measurable_neg, ?_⟩
        simpa using (Real.map_volume_mul_left (by norm_num : (-1 : ℝ) ≠ 0)))).map_eq
  have h := hskew.comp (measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume))
  exact h

lemma B_bijOn : BijOn B Omega Omega := by
  refine ⟨fun x hx => B_mem_Omega hx, ?_, ?_⟩
  · intro x hx y hy heq
    have h := congrArg Binv heq
    simpa only [Binv_B x.1 x.2 hx, Binv_B y.1 y.2 hy] using h
  · intro y hy
    exact ⟨Binv y, Binv_mem_Omega hy, B_Binv y.1 y.2 hy⟩

/-- Normalized Lebesgue measure is invariant under `B`. -/
theorem measurePreserving_B : MeasurePreserving B m m := by
  have harea : MeasurePreserving B (volume.restrict Omega) (volume.restrict Omega) := by
    apply measurePreserving_countable_branches measurable_B measurableSet_Omega
      (fun x : ℝ × ℝ => ⌊(1 + x.1) / x.2⌋)
      (fun k => (measurableSet_singleton k).preimage (by fun_prop))
      branchEquiv measurePreserving_branch
    · intro x hx
      rfl
    · exact B_bijOn
  exact harea.smul_measure (2 : ℝ≥0∞)

end
end Paper14
