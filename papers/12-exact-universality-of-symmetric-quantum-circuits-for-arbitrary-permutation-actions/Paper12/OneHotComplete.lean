import Paper12.FixedRotations
import Paper12.OneHotAmplify

noncomputable section
namespace Paper12
open Matrix Classical
variable {X : Type*} [Fintype X]

theorem prepRaw_action (α : Coeffs X) (hmass : 0 < coeffMass α) :
    applyOp (prepRaw α).unitary (zeroKet _) =
      registerVec (registerVec (weightedOneHot (selectorD α)) (zeroKet (Fin 2))) (zeroKet (Fin 1)) := by
  let Data := SelectorWire α ⊕ Fin 2
  have hZP : applyOp ((singleCircuit (ryGate (0 : Fin 1) (-Real.pi / 2))).onRight (J := Data)).unitary
      (zeroKet _) = registerVec (zeroKet Data) (signedKet kickbackC) := by
    rw [← registerVec_zero, Circuit.onRight_unitary, registerTensor_apply, applyOp_one, ry_prepare_minus]
  have hT : applyOp ((prepT α).onLeft (K := Fin 1)).unitary
      (registerVec (zeroKet Data) (signedKet kickbackC)) =
      registerVec (prepStart α) (signedKet kickbackC) := by
    rw [Circuit.onLeft_unitary, extendLeft, registerTensor_apply, applyOp_one]
    rfl
  have hI : applyOp ((prepIteration α).power 2).unitary
      (registerVec (prepStart α) (signedKet kickbackC)) =
      registerVec (prepGoodVec α) (signedKet kickbackC) := by
    rw [Circuit.power_unitary, (prepIteration_simulates α kickbackC).power 2,
      prep_two_iterations α hmass]
  have hZR : applyOp ((singleCircuit (ryGate (0 : Fin 1) (Real.pi / 2))).onRight (J := Data)).unitary
      (registerVec (prepGoodVec α) (signedKet kickbackC)) =
      registerVec (prepGoodVec α) (zeroKet (Fin 1)) := by
    rw [Circuit.onRight_unitary, registerTensor_apply, applyOp_one, ry_reset_minus]
  have hR0 : applyOp (Gate.one (⟨Sum.inr 1, pmat .X, pmat_unitary .X⟩ : OneQubit Data)).unitary
      (prepGoodVec α) = registerVec (weightedOneHot (selectorD α)) (zeroKet (Fin 2)) := by
    rw [OneQubit.right_unitary (J := SelectorWire α)
      (⟨1, pmat .X, pmat_unitary .X⟩ : OneQubit (Fin 2)), prepGoodVec, registerTensor_apply, applyOp_one]
    exact congrArg (registerVec (weightedOneHot (selectorD α))) flip_adjustment_zero
  have hR : applyOp ((singleCircuit (Gate.one
      (⟨Sum.inr 1, pmat .X, pmat_unitary .X⟩ : OneQubit Data))).onLeft (K := Fin 1)).unitary
      (registerVec (prepGoodVec α) (zeroKet (Fin 1))) =
      registerVec (registerVec (weightedOneHot (selectorD α)) (zeroKet (Fin 2))) (zeroKet (Fin 1)) := by
    rw [Circuit.onLeft_unitary, singleCircuit_unitary, extendLeft, registerTensor_apply,
      applyOp_one, hR0]
  simp only [prepRaw, Circuit.mul_unitary]
  rw [applyOp_mul, applyOp_mul, applyOp_mul, applyOp_mul, hZP, hT, hI, hZR, hR]

theorem rewireVec_trans {J K T : Type*} [Fintype J] [Fintype K] [Fintype T]
    (e : J ≃ K) (f : K ≃ T) (ψ : Vec J) :
    rewireVec (e.trans f) ψ = rewireVec f (rewireVec e ψ) := rfl

theorem rewireVec_sum_generic {J K T L : Type*} [Fintype J] [Fintype K] [Fintype T] [Fintype L]
    (e : J ≃ K) (f : T ≃ L) (ψ : Vec J) (χ : Vec T) :
    rewireVec (e.sumCongr f) (registerVec ψ χ) = registerVec (rewireVec e ψ) (rewireVec f χ) := rfl

theorem oneHotCircuit_prepares (α : Coeffs X) (hmass : 0 < coeffMass α) :
    applyOp (oneHotCircuit α).unitary
      (embedZero (W := Fin 3) (eBasis (fun _ : SelectorWire α => 0))) =
      embedZero (weightedOneHot (selectorD α)) := by
  have hzero : embedZero (W := Fin 3) (eBasis (fun _ : SelectorWire α => 0)) =
      rewireVec (prepWireEquiv α) (zeroKet _) := by
    rw [show eBasis (fun _ : SelectorWire α => 0) = zeroKet (SelectorWire α) from rfl,
      embedZero_registerVec, registerVec_zero, rewireVec_zero]
  rw [oneHotCircuit, Circuit.rewire_unitary, hzero, rewire_apply, prepRaw_action α hmass]
  rw [prepWireEquiv, rewireVec_trans, rewireVec_assoc, registerVec_zero,
    rewireVec_sum_generic, rewireVec_zero]
  exact (embedZero_registerVec _).symm

/-- Lemma 2.5: an actual elementary circuit with exact phase, clean workspace,
linear size, and every parameter-preserving selector permutation as a layer symmetry. -/
theorem lemma_2_5_circuit (α : Coeffs X) (hmass : 0 < coeffMass α) :
    ∃ B : Circuit (SelectorWire α ⊕ Fin 3),
      applyOp B.unitary (embedZero (W := Fin 3) (eBasis (fun _ : SelectorWire α => 0))) =
        embedZero (weightedOneHot (selectorD α)) ∧
      B.size ≤ 40 * (coeffCard α + 1) ∧
      ∀ τ : SelectorWire α ≃ SelectorWire α,
        (∀ q, α (τ q).val = α q.val) → B.Preserved (liftFixW τ) :=
  ⟨oneHotCircuit α, oneHotCircuit_prepares α hmass, oneHotCircuit_size α,
    oneHotCircuit_preserved α⟩
end Paper12
