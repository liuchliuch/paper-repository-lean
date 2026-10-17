import Paper14.SelfInductionConvergence
import Paper14.CountableBranches
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Paper S2.p6: the Jacobian argument for the self-induction pushforward. -/
open MeasureTheory Measure Set Function
open scoped ENNReal
namespace Paper14
noncomputable section

def shearEquiv (k : ℤ) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun := fun x => (x.1, x.2 + (k : ℝ) * x.1)
  invFun := fun x => (x.1, x.2 - (k : ℝ) * x.1)
  left_inv := by intro x; ext <;> simp
  right_inv := by intro x; ext <;> simp
  measurable_toFun := by
    change Measurable (fun x : ℝ × ℝ => (x.1, x.2 + (k : ℝ) * x.1))
    fun_prop
  measurable_invFun := by
    change Measurable (fun x : ℝ × ℝ => (x.1, x.2 - (k : ℝ) * x.1))
    fun_prop

def scaleEquiv (r : ℝ) (hr : r ≠ 0) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun := (r • ·)
  invFun := (r⁻¹ • ·)
  left_inv := by intro x; simp [smul_smul, hr]
  right_inv := by intro x; simp [smul_smul, hr]
  measurable_toFun := by change Measurable (r • · : (ℝ × ℝ) → (ℝ × ℝ)); fun_prop
  measurable_invFun := by change Measurable (r⁻¹ • · : (ℝ × ℝ) → (ℝ × ℝ)); fun_prop

lemma measurePreserving_shear (k : ℤ) :
    MeasurePreserving (shearEquiv k) volume volume := by
  refine (MeasurePreserving.id (volume : Measure ℝ)).skew_product
    (g := fun a b : ℝ => b + (k : ℝ) * a) (μc := volume) (μd := volume) (by fun_prop) ?_
  filter_upwards [] with a
  simpa [add_comm] using (measurePreserving_add_left volume ((k : ℝ) * a)).map_eq

lemma measurePreserving_scale (r : ℝ) (hr : 0 < r) :
    MeasurePreserving (scaleEquiv r hr.ne') volume
      ((ENNReal.ofReal r ^ (2 : ℝ))⁻¹ • volume) := by
  refine ⟨(scaleEquiv r hr.ne').measurable, ?_⟩
  change Measure.map (Prod.map (fun a : ℝ => r * a) (fun b : ℝ => r * b))
    ((volume : Measure ℝ).prod volume) = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Real.map_volume_mul_left hr.ne', Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul]
  congr 1
  rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_inv_of_pos
    (sq_pos_of_pos hr), ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [abs_of_pos (inv_pos.mpr hr), ← pow_two, inv_pow]

/-- The conjugacy is a genuine bijection between the two sections. -/
lemma phiR_bijOn {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    BijOn (phiR r) Omega (Yr r) := by
  refine ⟨fun x hx => phiR_mem_Yr hr hr1 hx, ?_, ?_⟩
  · intro x hx y hy heq
    have h := congrArg (phiRInv r) heq
    simpa only [phiRInv_phiR hr hr1 hx, phiRInv_phiR hr hr1 hy] using h
  · intro y hy
    refine ⟨phiRInv r y, phiRInv_mem_Omega hr hr1 hy, ?_⟩
    exact phiR_phiRInv hr hr1 hy

/-- The full pushforward part of Lemma 2, including normalization. -/
theorem measurePreserving_phiR : Lemma2PushforwardStatement := by
  intro r hr hr1
  let c : ℝ≥0∞ := (ENNReal.ofReal r ^ (2 : ℝ))⁻¹
  have harea : MeasurePreserving (phiR r) (volume.restrict Omega)
      ((c • volume).restrict (Yr r)) := by
    apply measurePreserving_countable_branches (measurable_phiR r) measurableSet_Omega
      (fun x : ℝ × ℝ => phiJ r x.1 x.2)
      (fun k => (measurableSet_singleton k).preimage (by unfold phiJ; fun_prop))
      (fun k => (shearEquiv k).trans (scaleEquiv r hr.ne'))
      (fun k => (measurePreserving_scale r hr).comp (measurePreserving_shear k))
    · intro x hx
      rfl
    · exact phiR_bijOn hr hr1
  have h := harea.smul_measure (2 : ℝ≥0∞)
  have hrestrict : (volume.restrict Omega).restrict (Yr r) = volume.restrict (Yr r) := by
    rw [Measure.restrict_restrict (measurableSet_Yr r)]
    congr 1
    exact inter_eq_left.mpr (fun x hx => hx.1)
  simpa only [mr, m, Measure.restrict_smul, hrestrict, smul_smul, mul_comm,
    c] using h

end
end Paper14
