import Paper12.BellSwap
import Paper12.LiftDecompose
import Paper12.OuterComplete

noncomputable section
namespace Paper12
open Matrix Classical
variable {X T : Type*} [Fintype X] [Fintype T]

def bellWires : ((X ⊕ X) ⊕ (X ⊕ T)) ≃ (X ⊕ ((X ⊕ X) ⊕ T)) where
  toFun
    | .inl (.inl d) => .inl d
    | .inl (.inr a) => .inr (.inl (.inl a))
    | .inr (.inl b) => .inr (.inl (.inr b))
    | .inr (.inr t) => .inr (.inr t)
  invFun
    | .inl d => .inl (.inl d)
    | .inr (.inl (.inl a)) => .inl (.inr a)
    | .inr (.inl (.inr b)) => .inr (.inl b)
    | .inr (.inr t) => .inr (.inr t)
  left_inv z := by rcases z with (d|a)|(b|t) <;> rfl
  right_inv z := by rcases z with d|((a|b)|t) <;> rfl

def swapWires : ((X ⊕ X) ⊕ (X ⊕ T)) ≃ (X ⊕ ((X ⊕ X) ⊕ T)) where
  toFun
    | .inl (.inl d) => .inl d
    | .inl (.inr b) => .inr (.inl (.inr b))
    | .inr (.inl a) => .inr (.inl (.inl a))
    | .inr (.inr t) => .inr (.inr t)
  invFun
    | .inl d => .inl (.inl d)
    | .inr (.inl (.inl a)) => .inr (.inl a)
    | .inr (.inl (.inr b)) => .inl (.inr b)
    | .inr (.inr t) => .inr (.inr t)
  left_inv z := by rcases z with (d|b)|(a|t) <;> rfl
  right_inv z := by rcases z with d|((a|b)|t) <;> rfl

def choiBell : Circuit (X ⊕ ((X ⊕ X) ⊕ T)) :=
  (bellPreparation.onLeft (K := X ⊕ T)).rewire bellWires

def choiSwap : Circuit (X ⊕ ((X ⊕ X) ⊕ T)) :=
  (pairSwap.onLeft (K := X ⊕ T)).rewire swapWires

def choiBlock (CJ : Circuit ((X ⊕ X) ⊕ T)) : Circuit (X ⊕ ((X ⊕ X) ⊕ T)) :=
  choiSwap.mul (choiBell.adjoint.mul (CJ.onRight (J := X)))

def choiProbability (X : Type*) [Fintype X] : ℝ := (((2 : ℝ) ^ Fintype.card X)⁻¹) ^ 2

def choiVec (U : Op X) : Vec (X ⊕ X) := fun b => choiCoeff U (b ∘ Sum.inl) (b ∘ Sum.inr)

theorem extendLeft_apply_any {J K : Type*} [Fintype J] [Fintype K]
    (A : Op J) (ψ : Vec (J ⊕ K)) (b : Basis (J ⊕ K)) :
    applyOp (extendLeft A) ψ b =
      applyOp A (fun a => ψ (Sum.elim a (b ∘ Sum.inr))) (b ∘ Sum.inl) := by
  simp only [applyOp, extendLeft, registerTensor]
  rw [sum_joint]
  apply Finset.sum_congr rfl
  intro a _
  simp [Matrix.one_apply]

theorem choiSwap_apply (ψ : Vec (X ⊕ ((X ⊕ X) ⊕ T)))
    (b : Basis (X ⊕ ((X ⊕ X) ⊕ T))) :
    applyOp (choiSwap (X := X) (T := T)).unitary ψ b =
      ψ (Sum.elim (fun x => b (Sum.inr (Sum.inl (Sum.inr x))))
        (Sum.elim (Sum.elim (fun x => b (Sum.inr (Sum.inl (Sum.inl x))))
          (fun x => b (Sum.inl x))) (fun t => b (Sum.inr (Sum.inr t))))) := by
  rw [choiSwap, Circuit.rewire_unitary, Circuit.onLeft_unitary, rewire_apply_any,
    extendLeft_apply_any, pairSwap_apply]
  change ψ _ = ψ _
  congr 1
  funext z
  rcases z with d|((a|b)|t) <;> rfl

theorem rewireOp_adjoint {J K : Type*} (e : J ≃ K) (A : Op J) :
    (rewireOp e A)ᴴ = rewireOp e Aᴴ := rfl

theorem bell_unprepare_zero (a : Basis (X ⊕ X)) :
    (bellPreparation (X := X)).unitaryᴴ (fun _ => 0) a =
      bellCoeff (a ∘ Sum.inl) (a ∘ Sum.inr) := by
  have h := bellPreparation_zero a
  rw [show zeroKet (X ⊕ X) = eBasis (fun _ => 0) from rfl, applyOp_eBasis] at h
  rw [Matrix.conjTranspose_apply, h]
  unfold bellCoeff
  split_ifs
  · exact _root_.Complex.conj_ofReal _
  · exact map_zero (starRingEnd ℂ)

theorem choiBell_contract (U : Op X) (ψ : Vec X) (b : Basis X) :
    applyOp (choiBell (X := X) (T := T)).unitaryᴴ
      (registerVec ψ (embedZero (W := T) (choiVec U)))
      (Sum.elim (fun _ => 0) (Sum.elim (Sum.elim (fun _ => 0) b) (fun _ => 0))) =
      ((2 : ℂ) ^ Fintype.card X)⁻¹ * applyOp U ψ b := by
  let z : Basis (X ⊕ ((X ⊕ X) ⊕ T)) :=
    Sum.elim (fun _ => 0) (Sum.elim (Sum.elim (fun _ => 0) b) (fun _ => 0))
  change applyOp (choiBell (X := X) (T := T)).unitaryᴴ _ z = _
  simp only [choiBell, Circuit.rewire_unitary, Circuit.onLeft_unitary,
    rewireOp_adjoint, extendLeft, registerTensor_adjoint, Matrix.conjTranspose_one]
  rw [rewire_apply_any]
  change applyOp (extendLeft (bellPreparation (X := X)).unitaryᴴ)
    (rewireVec (bellWires (X := X) (T := T)).symm
      (registerVec ψ (embedZero (W := T) (choiVec U)))) (z ∘ bellWires) = _
  rw [extendLeft_apply_any]
  have hL : (z ∘ (bellWires (X := X) (T := T))) ∘ Sum.inl = (fun _ => 0) := by
    funext x
    cases x <;> rfl
  have hR : (z ∘ (bellWires (X := X) (T := T))) ∘ Sum.inr = Sum.elim b (fun _ => 0) := by
    funext x
    cases x <;> rfl
  rw [hL, hR]
  conv_lhs => simp only [applyOp, bell_unprepare_zero, rewireVec]
  rw [sum_joint, ← choi_contraction U ψ b]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  simp only [registerVec, embedZero, choiVec, bellWires, Equiv.coe_fn_symm_mk,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr, implies_true, ite_true]
  ring

theorem choiBlock_action_zero (CJ : Circuit ((X ⊕ X) ⊕ T)) (U : Op X)
    (hprep : applyOp CJ.unitary (zeroKet _) = embedZero (W := T) (choiVec U))
    (ψ : Vec X) (b : Basis X) :
    applyOp (choiBlock CJ).unitary (embedZero ψ) (zeroBasisMap b) =
      ((2 : ℂ) ^ Fintype.card X)⁻¹ * applyOp U ψ b := by
  simp only [choiBlock, Circuit.mul_unitary, Circuit.adjoint_unitary, applyOp_mul]
  rw [embedZero_registerVec, Circuit.onRight_unitary, registerTensor_apply, applyOp_one, hprep,
    choiSwap_apply]
  exact choiBell_contract U ψ b

theorem choiBlock_encoding (CJ : Circuit ((X ⊕ X) ⊕ T)) (U : Op X)
    (hprep : applyOp CJ.unitary (zeroKet _) = embedZero (W := T) (choiVec U)) :
    zeroBlock (choiBlock CJ).unitary = ((2 : ℂ) ^ Fintype.card X)⁻¹ • U := by
  ext a b
  have h := choiBlock_action_zero CJ U hprep (eBasis b) a
  rw [embedZero_eBasis, applyOp_eBasis, applyOp_eBasis] at h
  rw [zeroBlock_entry]
  exact h

theorem choiBlock_size (CJ : Circuit ((X ⊕ X) ⊕ T)) :
    (choiBlock CJ).size = CJ.size + 5 * Fintype.card X := by
  simp only [choiBlock, Circuit.mul_size, Circuit.adjoint_size, Circuit.onRight_size,
    choiSwap, choiBell, Circuit.rewire_size, Circuit.onLeft_size, pairSwap_size, bellPreparation_size]
  omega
end Paper12
