import Paper12.WireSupport
import Paper12.StateVectors

noncomputable section
namespace Paper12
open Matrix Classical
variable {J K T : Type*} [Fintype J] [Fintype K] [Fintype T]

def rewireVec (e : J ≃ K) (ψ : Vec J) : Vec K := fun b => ψ (b ∘ e)

theorem rewire_apply (e : J ≃ K) (A : Op J) (ψ : Vec J) :
    applyOp (rewireOp e A) (rewireVec e ψ) = rewireVec e (applyOp A ψ) := by
  funext b
  exact Equiv.sum_comp (basisRewire e) (fun c => A (b ∘ e) c * ψ c)

theorem rewireVec_zero (e : J ≃ K) : rewireVec e (zeroKet J) = zeroKet K := by
  funext b
  have hz : b ∘ e = (fun _ : J => (0 : Fin 2)) ↔ b = fun _ : K => (0 : Fin 2) := by
    constructor
    · intro h
      funext y
      obtain ⟨x, rfl⟩ := e.surjective y
      exact congrFun h x
    · intro h; rw [h]; rfl
  simp only [rewireVec, zeroKet, eBasis, hz]

theorem rewireVec_sum (e : J ≃ K) (f : T ≃ T) (ψ : Vec J) (χ : Vec T) :
    rewireVec (e.sumCongr f) (registerVec ψ χ) = registerVec (rewireVec e ψ) (rewireVec f χ) := rfl

theorem rewireVec_assoc (ψ : Vec J) (χ : Vec K) (η : Vec T) :
    rewireVec (Equiv.sumAssoc J K T) (registerVec (registerVec ψ χ) η) =
      registerVec ψ (registerVec χ η) := by
  funext b
  exact mul_assoc _ _ _

theorem registerVec_zero : registerVec (zeroKet J) (zeroKet K) = zeroKet (J ⊕ K) := by
  funext b
  have hz : b = (fun _ : J ⊕ K => (0 : Fin 2)) ↔
      b ∘ Sum.inl = (fun _ : J => (0 : Fin 2)) ∧ b ∘ Sum.inr = (fun _ : K => (0 : Fin 2)) := by
    constructor
    · intro h; subst b; exact ⟨rfl, rfl⟩
    · rintro ⟨hL, hR⟩
      funext x
      cases x with
      | inl x => exact congrFun hL x
      | inr x => exact congrFun hR x
  simp only [registerVec, zeroKet, eBasis, hz]
  by_cases hL : b ∘ Sum.inl = (fun _ : J => (0 : Fin 2)) <;>
    by_cases hR : b ∘ Sum.inr = (fun _ : K => (0 : Fin 2)) <;> simp [hL, hR]
end Paper12
