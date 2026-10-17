import Paper12.OneHotSymmetry

noncomputable section
namespace Paper12
open Matrix Classical
variable {X : Type*} [Fintype X]

theorem tensorOp_sum {J K : Type*} [Fintype J] [Fintype K] (m : J → QMat) (n : K → QMat) :
    tensorOp (Sum.elim m n) = registerTensor (tensorOp m) (tensorOp n) := by
  ext i j
  exact Fintype.prod_sum_type (fun x => (Sum.elim m n) x (i x) (j x))

def prepAuxLocal (α : Coeffs X) (r : Fin 2) : QMat :=
  if r = 0 then 1 else realRotation (Real.cos (beta0 α / 2)) (Real.sin (beta0 α / 2))

def prepStart (α : Coeffs X) : Vec (SelectorWire α ⊕ Fin 2) :=
  applyOp (prepT α).unitary (zeroKet _)

def prepGoodVec (α : Coeffs X) : Vec (SelectorWire α ⊕ Fin 2) :=
  registerVec (weightedOneHot (selectorD α)) (eBasis (oneHot (1 : Fin 2)))

def prepGood (α : Coeffs X) (b : Basis (SelectorWire α ⊕ Fin 2)) : Prop :=
  (if hammingWeight (b ∘ Sum.inl) = 1 then 1 - b (Sum.inr 0) else b (Sum.inr 0)) = 1 ∧
    b (Sum.inr 1) = 1

def prepProjector (α : Coeffs X) : Op (SelectorWire α ⊕ Fin 2) := predicateProjector (prepGood α)

theorem prepT_tensor (α : Coeffs X) :
    (prepT α).unitary = registerTensor (productPreparation (selectorD α)).unitary
      (tensorOp (prepAuxLocal α)) := by
  simp only [prepT, productPreparation, parallelCircuit_unitary]
  exact tensorOp_sum _ _

theorem prepAux_zero_apply (α : Coeffs X) (b : Basis (Fin 2)) :
    applyOp (tensorOp (prepAuxLocal α)) (zeroKet _) b =
      (if b 0 = 0 then (1 : ℂ) else 0) *
        realRotation (Real.cos (beta0 α / 2)) (Real.sin (beta0 α / 2)) (b 1) 0 := by
  rw [show zeroKet (Fin 2) = eBasis (fun _ => 0) from rfl, applyOp_eBasis]
  simp [tensorOp, Fin.prod_univ_two, prepAuxLocal, Matrix.one_apply]

theorem prepStart_apply (α : Coeffs X) (b : Basis (SelectorWire α ⊕ Fin 2)) :
    prepStart α b =
      applyOp (productPreparation (selectorD α)).unitary (zeroKet _) (b ∘ Sum.inl) *
      (if b (Sum.inr 0) = 0 then (1 : ℂ) else 0) *
      realRotation (Real.cos (beta0 α / 2)) (Real.sin (beta0 α / 2)) (b (Sum.inr 1)) 0 := by
  unfold prepStart
  rw [prepT_tensor, ← registerVec_zero, registerTensor_apply]
  change _ * applyOp (tensorOp (prepAuxLocal α)) (zeroKet _) (b ∘ Sum.inr) = _
  rw [prepAux_zero_apply]
  exact (mul_assoc _ _ _).symm

theorem prepGoodVec_inner (α : Coeffs X) (hmass : 0 < coeffMass α) :
    vecInner (prepGoodVec α) (prepGoodVec α) = 1 := by
  rw [prepGoodVec, vecInner_registerVec, vecInner_basis, if_pos rfl, mul_one,
    weightedOneHot_inner]
  exact_mod_cast selectorD_sq α hmass

theorem column_action_isometry {J : Type*} [Fintype J] (A : Op J)
    (hA : Aᴴ * A = 1) (ψ : Vec J) (hψ : vecInner ψ ψ = 1) :
    IsIsometry (column (applyOp A ψ)) := by
  rw [← column_apply]
  unfold IsIsometry
  rw [Matrix.conjTranspose_mul]
  calc _ = (column ψ)ᴴ * (Aᴴ * A) * column ψ := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hA, Matrix.mul_one]; exact column_isometry ψ hψ

theorem prepStart_isometry (α : Coeffs X) : IsIsometry (column (prepStart α)) := by
  exact column_action_isometry _ (Circuit.unitary_isUnitary (prepT α)) _ vecInner_zero

theorem prep_scale (α : Coeffs X) (hmass : 0 < coeffMass α) :
    (productC (selectorD α) : ℂ) * (Real.sin (beta0 α / 2) : ℂ) = (Real.sin theta0 : ℂ) := by
  have hs : productC (selectorD α) * Real.sin (beta0 α / 2) = Real.sin theta0 := by
    rw [selector_productC α hmass, (beta0_mem α (selector_amp_sq α hmass)).2.2]
    have hp := Real.sqrt_pos.mpr (prep_p0_pos α (selector_amp_sq α hmass))
    field_simp
  exact_mod_cast hs

theorem prep_project_start (α : Coeffs X) (hmass : 0 < coeffMass α) :
    applyOp (prepProjector α) (prepStart α) = (Real.sin theta0 : ℂ) • prepGoodVec α := by
  rw [prepProjector, predicateProjector_apply]
  funext b
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hf : b (Sum.inr 0) = 0
  · by_cases hr : b (Sum.inr 1) = 1
    · have haux : b ∘ Sum.inr = oneHot (1 : Fin 2) := by
        funext r
        fin_cases r <;> simp [oneHot, hf, hr]
      by_cases hw : hammingWeight (b ∘ Sum.inl) = 1
      · obtain ⟨q, hq⟩ := (hammingWeight_eq_one _).mp hw
        have hp : prepGood α b := by simp [prepGood, hw, hf, hr]
        rw [if_pos hp, prepStart_apply]
        simp only [hf, hr, ite_true, one_mul, mul_one]
        rw [hq, productPreparation_oneHot]
        simp only [prepGoodVec, registerVec, haux, eBasis, ite_true, mul_one]
        rw [hq, weightedOneHot_at]
        change (productC (selectorD α) : ℂ) * (selectorD α q : ℂ) *
          (Real.sin (beta0 α / 2) : ℂ) = (Real.sin theta0 : ℂ) * (selectorD α q : ℂ)
        calc _ = ((productC (selectorD α) : ℂ) * (Real.sin (beta0 α / 2) : ℂ)) *
            (selectorD α q : ℂ) := by ring
          _ = _ := congrArg (fun z : ℂ => z * (selectorD α q : ℂ)) (prep_scale α hmass)
      · have hp : ¬prepGood α b := by simp [prepGood, hw, hf]
        rw [if_neg hp]
        simp [prepGoodVec, registerVec, weightedOneHot_off _ _ hw]
    · have hp : ¬prepGood α b := fun h => hr h.2
      have haux : b ∘ Sum.inr ≠ oneHot (1 : Fin 2) := by
        intro h
        have hh := congrFun h 1
        exact hr (by simpa [oneHot] using hh)
      rw [if_neg hp]
      simp [prepGoodVec, registerVec, eBasis, haux]
  · have hstart : prepStart α b = 0 := by rw [prepStart_apply]; simp [hf]
    have haux : b ∘ Sum.inr ≠ oneHot (1 : Fin 2) := by
      intro h
      have hh := congrFun h 0
      exact hf (by simpa [oneHot] using hh)
    simp [hstart, prepGoodVec, registerVec, eBasis, haux]
end Paper12
