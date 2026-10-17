import Paper12.SelectorPhases
import Paper12.VectorAlgebra
import Paper12.OuterComplete

noncomputable section
namespace Paper12
open Matrix Classical
variable {X : Type*} [Fintype X]
local instance blockSelectorDecidable (α : Coeffs X) : DecidableEq (SelectorWire α) := Classical.decEq _

def selectionAux (α : Coeffs X) : Circuit (X ⊕ (SelectorWire α ⊕ Fin 3)) :=
  ((fullSelection α).onLeft (K := Fin 3)).rewire (Equiv.sumAssoc X (SelectorWire α) (Fin 3))

def blockCircuit (α : Coeffs X) : Circuit (X ⊕ (SelectorWire α ⊕ Fin 3)) :=
  ((oneHotCircuit α).onRight (J := X)).adjoint.mul
    ((selectionAux α).mul ((oneHotCircuit α).onRight (J := X)))

theorem selectionAux_sector (α : Coeffs X) (q : SelectorWire α) (ψ : Vec X) :
    applyOp (selectionAux α).unitary
      (registerVec ψ (embedZero (W := Fin 3) (eBasis (oneHot q)))) =
      selectorPhase α q.val • registerVec (applyOp (pop X q.val) ψ)
        (embedZero (W := Fin 3) (eBasis (oneHot q))) := by
  simp only [selectionAux, Circuit.rewire_unitary, Circuit.onLeft_unitary, embedZero_registerVec]
  rw [← rewireVec_assoc, rewire_apply]
  rw [extendLeft, registerTensor_apply, applyOp_one, fullSelection_sector,
    registerVec_smul_left]
  rw [rewireVec_smul, rewireVec_assoc]

theorem block_prepare (α : Coeffs X) (hmass : 0 < coeffMass α) (ψ : Vec X) :
    applyOp ((oneHotCircuit α).onRight (J := X)).unitary
      (embedZero (W := SelectorWire α ⊕ Fin 3) ψ) =
      registerVec ψ (embedZero (W := Fin 3) (weightedOneHot (selectorD α))) := by
  rw [embedZero_registerVec, Circuit.onRight_unitary, registerTensor_apply, applyOp_one]
  have hz : zeroKet (SelectorWire α ⊕ Fin 3) =
      embedZero (W := Fin 3) (eBasis (fun _ : SelectorWire α => 0)) := by
    rw [embedZero_registerVec]
    exact registerVec_zero.symm
  rw [hz, oneHotCircuit_prepares α hmass]

theorem embedZero_sum {J K ι : Type*} [Fintype J] [Fintype K]
    (s : Finset ι) (f : ι → Vec J) :
    embedZero (W := K) (∑ i ∈ s, f i) = ∑ i ∈ s, embedZero (W := K) (f i) := by
  funext b
  simp only [embedZero, Finset.sum_apply]
  split_ifs <;> simp

theorem selectionAux_prepared (α : Coeffs X) (ψ : Vec X) :
    applyOp (selectionAux α).unitary
      (registerVec ψ (embedZero (W := Fin 3) (weightedOneHot (selectorD α)))) =
      ∑ q : SelectorWire α, ((selectorD α q : ℂ) * selectorPhase α q.val) •
        registerVec (applyOp (pop X q.val) ψ) (embedZero (W := Fin 3) (eBasis (oneHot q))) := by
  rw [weightedOneHot_sum, embedZero_sum, registerVec_sum_right, applyOp_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [embedZero_smul, registerVec_smul_right, applyOp_smul_vec,
    selectionAux_sector, smul_smul]

theorem vecInner_eBasis_right {J : Type*} [Fintype J] (ψ : Vec J) (a : Basis J) :
    vecInner ψ (eBasis a) = star (ψ a) := by
  simp [vecInner, eBasis]

theorem prepared_sector_inner (α : Coeffs X) (a : Basis X) (ψ : Vec X) (q : SelectorWire α) :
    vecInner (registerVec (eBasis a) (embedZero (W := Fin 3) (weightedOneHot (selectorD α))))
      (registerVec ψ (embedZero (W := Fin 3) (eBasis (oneHot q)))) =
      ψ a * (selectorD α q : ℂ) := by
  rw [vecInner_registerVec, vecInner_eBasis_left]
  simp only [embedZero_registerVec]
  rw [vecInner_registerVec, vecInner_zero, mul_one, vecInner_eBasis_right, weightedOneHot_at]
  simp

theorem blockCircuit_zeroBlock (α : Coeffs X) (hmass : 0 < coeffMass α) :
    zeroBlock (blockCircuit α).unitary =
      ∑ q : SelectorWire α, (((selectorD α q : ℂ) ^ 2) * selectorPhase α q.val) • pop X q.val := by
  ext a b
  rw [zeroBlock_inner]
  simp only [blockCircuit, Circuit.mul_unitary, Circuit.adjoint_unitary,
    applyOp_mul]
  rw [vecInner_adjoint, block_prepare α hmass, block_prepare α hmass,
    selectionAux_prepared, vecInner_sum_right]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro q _
  rw [vecInner_smul_right, prepared_sector_inner, applyOp_eBasis]
  ring

theorem blockCircuit_encoding (U : Op X) (hU : Uᴴ * U = 1) :
    zeroBlock (blockCircuit (pauliCoeff U)).unitary =
      ((coeffMass (pauliCoeff U) : ℂ)⁻¹) • U := by
  have hm : 0 < coeffMass (pauliCoeff U) := lt_of_lt_of_le (by norm_num) (coeff_mass_bounds U hU).1
  rw [blockCircuit_zeroBlock _ hm]
  have hsum : (∑ q : SelectorWire (pauliCoeff U),
      (((selectorD (pauliCoeff U) q : ℂ) ^ 2) * selectorPhase (pauliCoeff U) q.val) • pop X q.val) =
      ∑ w ∈ coeffSupport (pauliCoeff U),
        (((selectorAmp (pauliCoeff U) w) ^ 2 : ℂ) * selectorPhase (pauliCoeff U) w) • pop X w := by
    simpa only [selectorD, _root_.Complex.ofReal_pow] using
      (Finset.sum_coe_sort (coeffSupport (pauliCoeff U))
        (fun w => (((selectorAmp (pauliCoeff U) w : ℂ) ^ 2) *
          selectorPhase (pauliCoeff U) w) • pop X w))
  rw [hsum]
  exact block_encoding_identity _ U (pauliExpand_eq U).symm hm

theorem blockCircuit_size (α : Coeffs X) (hn : 0 < Fintype.card X) :
    (blockCircuit α).size + 1 ≤ 256 * Fintype.card X * (coeffCard α + 1) := by
  simp only [blockCircuit, Circuit.mul_size, Circuit.adjoint_size, Circuit.onRight_size,
    selectionAux, Circuit.rewire_size, Circuit.onLeft_size]
  have hb := oneHotCircuit_size α
  have hs := fullSelection_size α
  nlinarith
end Paper12
