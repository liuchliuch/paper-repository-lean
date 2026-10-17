import Paper12.PairGates
import Paper12.Choi
import Paper12.VectorAlgebra

noncomputable section
namespace Paper12
open Matrix Classical
variable {X : Type*} [Fintype X]

theorem rewire_apply_any {J K : Type*} [Fintype J] [Fintype K]
    (e : J ≃ K) (A : Op J) (ψ : Vec K) (b : Basis K) :
    applyOp (rewireOp e A) ψ b = applyOp A (rewireVec e.symm ψ) (b ∘ e) := by
  have h : rewireVec e (rewireVec e.symm ψ) = ψ := by
    funext c
    simp [rewireVec, Function.comp_def]
  conv_lhs => rw [← h, rewire_apply]
  rfl

def pairCNOTRight : Circuit (X ⊕ X) := pairCNOT.rewire (Equiv.sumComm X X)

theorem pairCNOTRight_apply (ψ : Vec (X ⊕ X)) (b : Basis (X ⊕ X)) :
    applyOp (pairCNOTRight (X := X)).unitary ψ b =
      ψ (Sum.elim (fun x => b (Sum.inl x))
        (fun x => bitXor (b (Sum.inr x)) (b (Sum.inl x)))) := by
  rw [pairCNOTRight, Circuit.rewire_unitary, rewire_apply_any, pairCNOT_apply]
  change ψ _ = ψ _
  congr 1
  funext z
  cases z <;> simp [pairAct, Function.comp_def]

def pairSwap : Circuit (X ⊕ X) := pairCNOT.mul (pairCNOTRight.mul pairCNOT)

theorem pairSwap_apply (ψ : Vec (X ⊕ X)) (b : Basis (X ⊕ X)) :
    applyOp (pairSwap (X := X)).unitary ψ b = ψ (b ∘ Equiv.sumComm X X) := by
  simp only [pairSwap, Circuit.mul_unitary, applyOp_mul]
  rw [pairCNOT_apply, pairCNOTRight_apply, pairCNOT_apply]
  congr 1
  funext z
  cases z with
  | inl x =>
    simp only [pairAct, Finset.mem_univ, ite_true, Sum.elim_inl, Sum.elim_inr]
    change bitXor (bitXor (b (Sum.inl x)) (b (Sum.inr x)))
      (bitXor (b (Sum.inr x)) (bitXor (b (Sum.inl x)) (b (Sum.inr x)))) = b (Sum.inr x)
    generalize b (Sum.inl x) = a
    generalize b (Sum.inr x) = c
    fin_cases a <;> fin_cases c <;> decide
  | inr x =>
    simp only [pairAct, Finset.mem_univ, ite_true, Sum.elim_inl, Sum.elim_inr]
    change bitXor (b (Sum.inr x)) (bitXor (b (Sum.inl x)) (b (Sum.inr x))) = b (Sum.inl x)
    generalize b (Sum.inl x) = a
    generalize b (Sum.inr x) = c
    fin_cases a <;> fin_cases c <;> decide

theorem pairSwap_size : (pairSwap (X := X)).size = 3 * Fintype.card X := by
  simp only [pairSwap, Circuit.mul_size, pairCNOTRight, Circuit.rewire_size, pairCNOT_size]
  omega

theorem pairCNOTRight_preserved (γ : X ≃ X) :
    (pairCNOTRight (X := X)).Preserved (γ.sumCongr γ) := by
  apply Circuit.preserved_rewire (Equiv.sumComm X X) (pairCNOT_preserved γ)
  intro z
  cases z <;> rfl

theorem pairSwap_preserved (γ : X ≃ X) :
    (pairSwap (X := X)).Preserved (γ.sumCongr γ) :=
  Circuit.preserved_mul (pairCNOT_preserved γ)
    (Circuit.preserved_mul (pairCNOTRight_preserved γ) (pairCNOT_preserved γ))

def bellPreparation : Circuit (X ⊕ X) :=
  pairCNOTRight.mul ((uniformChange (X := X) .Z).onLeft (K := X))

theorem kickback_pow_choiScale : kickbackC ^ Fintype.card X = (choiScale X : ℂ) := by
  have hr : (Real.sqrt 2 / 2 : ℝ) ^ 2 = (2 : ℝ)⁻¹ := by
    have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hpow : ((Real.sqrt 2 / 2 : ℝ) ^ Fintype.card X) ^ 2 = ((2 : ℝ) ^ Fintype.card X)⁻¹ := by
    rw [← pow_mul, Nat.mul_comm (Fintype.card X) 2, pow_mul, hr, inv_pow]
  have hchoi : choiScale X ^ 2 = ((2 : ℝ) ^ Fintype.card X)⁻¹ := by
    unfold choiScale
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  have he : (Real.sqrt 2 / 2 : ℝ) ^ Fintype.card X = choiScale X := by
    have h1 : 0 ≤ (Real.sqrt 2 / 2 : ℝ) ^ Fintype.card X := by positivity
    have h2 : 0 ≤ choiScale X := by unfold choiScale; positivity
    nlinarith
  unfold kickbackC
  exact_mod_cast he

theorem hadamard_zero :
    applyOp (uniformChange (X := X) .Z).unitary (zeroKet X) =
      fun _ => kickbackC ^ Fintype.card X := by
  funext b
  rw [show zeroKet X = eBasis (fun _ => 0) from rfl, applyOp_eBasis]
  simp only [uniformChange, parallelCircuit_unitary, basisChange, tensorOp]
  have he : ∀ x : X, hadamardMat (b x) 0 = kickbackC := by
    intro x
    generalize b x = v
    fin_cases v <;> simp [hadamardMat]
  simp only [he, Finset.prod_const, Finset.card_univ]

theorem bitXor_eq_zero (a b : Fin 2) : bitXor a b = 0 ↔ a = b := by
  fin_cases a <;> fin_cases b <;> decide

theorem bellPreparation_zero (b : Basis (X ⊕ X)) :
    applyOp (bellPreparation (X := X)).unitary (zeroKet (X ⊕ X)) b =
      bellCoeff (b ∘ Sum.inl) (b ∘ Sum.inr) := by
  rw [bellPreparation, Circuit.mul_unitary, applyOp_mul, pairCNOTRight_apply]
  rw [← registerVec_zero, Circuit.onLeft_unitary, extendLeft, registerTensor_apply,
    applyOp_one, hadamard_zero]
  have hz : (fun x => bitXor (b (Sum.inr x)) (b (Sum.inl x))) = (fun _ => 0) ↔
      b ∘ Sum.inl = b ∘ Sum.inr := by
    constructor
    · intro h
      funext x
      exact ((bitXor_eq_zero _ _).mp (congrFun h x)).symm
    · intro h
      funext x
      exact (bitXor_eq_zero _ _).mpr (congrFun h x).symm
  simp only [registerVec, Function.comp_def, Sum.elim_inl, Sum.elim_inr, zeroKet, eBasis,
    hz, bellCoeff, kickback_pow_choiScale]
  split_ifs <;> simp

theorem bellPreparation_size : (bellPreparation (X := X)).size = 2 * Fintype.card X := by
  simp only [bellPreparation, Circuit.mul_size, pairCNOTRight, Circuit.rewire_size,
    pairCNOT_size, Circuit.onLeft_size, uniformChange, parallelCircuit_size]
  omega

theorem bellPreparation_preserved (γ : X ≃ X) :
    (bellPreparation (X := X)).Preserved (γ.sumCongr γ) :=
  Circuit.preserved_mul (pairCNOTRight_preserved γ)
    (Circuit.preserved_onLeft γ (uniformChange_preserved .Z γ))
end Paper12
