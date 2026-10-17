import Paper12.CircuitTools

noncomputable section
namespace Paper12
open Matrix Classical
variable {J K : Type*} [Fintype J] [Fintype K]

def basisSumEquiv (J K : Type*) : Basis (J ⊕ K) ≃ Basis J × Basis K where
  toFun b := (b ∘ Sum.inl, b ∘ Sum.inr)
  invFun p := Sum.elim p.1 p.2
  left_inv b := by funext z; cases z <;> rfl
  right_inv p := rfl

theorem sum_joint {A : Type*} [AddCommMonoid A] (f : Basis (J ⊕ K) → A) :
    (∑ b : Basis (J ⊕ K), f b) =
      ∑ i : Basis J, ∑ j : Basis K, f (Sum.elim i j) := by
  rw [← Equiv.sum_comp (basisSumEquiv J K).symm]
  exact Fintype.sum_prod_type _

def registerTensor (A : Op J) (B : Op K) : Op (J ⊕ K) :=
  fun i j => A (i ∘ Sum.inl) (j ∘ Sum.inl) * B (i ∘ Sum.inr) (j ∘ Sum.inr)

@[simp] theorem registerTensor_mul (A A' : Op J) (B B' : Op K) :
    registerTensor (A * A') (B * B') = registerTensor A B * registerTensor A' B' := by
  ext i j
  simp only [Matrix.mul_apply, registerTensor]
  rw [sum_joint]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

@[simp] theorem registerTensor_one : registerTensor (1 : Op J) (1 : Op K) = 1 := by
  ext i j
  simp only [registerTensor, Matrix.one_apply]
  by_cases h : i = j
  · subst j; simp
  · rw [if_neg h]
    by_cases hL : i ∘ Sum.inl = j ∘ Sum.inl
    · have hR : i ∘ Sum.inr ≠ j ∘ Sum.inr := by
        intro hR
        apply h
        funext z
        cases z with
        | inl x => exact congrFun hL x
        | inr x => exact congrFun hR x
      simp [hL, hR]
    · simp [hL]

theorem registerTensor_adjoint (A : Op J) (B : Op K) :
    (registerTensor A B)ᴴ = registerTensor Aᴴ Bᴴ := by
  ext i j
  simp only [registerTensor, Matrix.conjTranspose_apply]
  exact map_mul (starRingEnd ℂ) _ _

def extendLeft (A : Op J) : Op (J ⊕ K) := registerTensor A 1

def extendLeftHom : Op J →* Op (J ⊕ K) where
  toFun := extendLeft
  map_one' := registerTensor_one
  map_mul' A B := by simpa only [extendLeft, Matrix.one_mul] using
    registerTensor_mul A B (1 : Op K) (1 : Op K)

def registerVec (ψ : Vec J) (χ : Vec K) : Vec (J ⊕ K) :=
  fun b => ψ (b ∘ Sum.inl) * χ (b ∘ Sum.inr)

theorem registerTensor_apply (A : Op J) (B : Op K) (ψ : Vec J) (χ : Vec K) :
    applyOp (registerTensor A B) (registerVec ψ χ) =
      registerVec (applyOp A ψ) (applyOp B χ) := by
  funext i
  simp only [applyOp, registerTensor, registerVec]
  rw [sum_joint, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  ring

def zeroKet (J : Type*) [Fintype J] : Vec J := eBasis (fun _ => 0)

theorem embedZero_registerVec (ψ : Vec J) :
    embedZero (W := K) ψ = registerVec ψ (zeroKet K) := by
  funext b
  have hz : (∀ r : K, b (Sum.inr r) = 0) ↔ b ∘ Sum.inr = (fun _ => 0) := by
    exact ⟨fun h => funext h, fun h r => congrFun h r⟩
  simp only [embedZero, registerVec, zeroKet, eBasis, hz]
  split_ifs <;> simp <;> rfl

theorem extendLeft_apply_zero (A : Op J) (ψ : Vec J) :
    applyOp (extendLeft (K := K) A) (embedZero ψ) = embedZero (applyOp A ψ) := by
  rw [embedZero_registerVec, extendLeft, registerTensor_apply, applyOp_one,
    embedZero_registerVec]
end Paper12
