import Paper12.WireSupport

noncomputable section
namespace Paper12
open Classical
variable {X W : Type*}

def workspacePerm (γ : X ≃ X) (e : (X ⊕ W) ≃ (X ⊕ W))
    (hr : ∀ x, e (Sum.inl x) = Sum.inl (γ x)) : W ≃ W :=
  Equiv.ofBijective (fun w => Classical.choose (lift_inr_map e hr w)) (by
    constructor
    · intro a b hab
      have ha := Classical.choose_spec (lift_inr_map e hr a)
      have hb := Classical.choose_spec (lift_inr_map e hr b)
      dsimp only at hab
      exact Sum.inr.inj (e.injective (ha.trans ((congrArg Sum.inr hab).trans hb.symm)))
    · intro b
      obtain ⟨a, ha⟩ := lift_inr_surj e hr b
      refine ⟨a, ?_⟩
      have hh := Classical.choose_spec (lift_inr_map e hr a)
      exact Sum.inr.inj (hh.symm.trans ha))

theorem lift_decompose (γ : X ≃ X) (e : (X ⊕ W) ≃ (X ⊕ W))
    (hr : ∀ x, e (Sum.inl x) = Sum.inl (γ x)) :
    e = γ.sumCongr (workspacePerm γ e hr) := by
  apply Equiv.ext
  intro z
  cases z with
  | inl x => exact hr x
  | inr w => exact Classical.choose_spec (lift_inr_map e hr w)
end Paper12
