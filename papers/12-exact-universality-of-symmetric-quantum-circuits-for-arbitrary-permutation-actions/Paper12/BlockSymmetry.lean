import Paper12.BlockCircuit

noncomputable section
namespace Paper12
open Matrix Classical
variable {X : Type*} [Fintype X]

theorem actWord_cancel (γ : X ≃ X) (w : PWord X) :
    actWord γ (actWord γ.symm w) = w := by
  funext x
  simp [actWord]

def selectorPerm (α : Coeffs X) (γ : X ≃ X)
    (hα : ∀ w, α (actWord γ w) = α w) : SelectorWire α ≃ SelectorWire α where
  toFun q := ⟨actWord γ q.val, by
    have hq := q.property
    simpa only [coeffSupport, Finset.mem_filter, Finset.mem_univ, true_and, hα] using hq⟩
  invFun q := ⟨actWord γ.symm q.val, by
    have hh := hα (actWord γ.symm q.val)
    rw [actWord_cancel] at hh
    have hq := q.property
    simp only [coeffSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rw [← hh]
    exact hq⟩
  left_inv q := by apply Subtype.ext; exact actWord_cancel γ.symm q.val
  right_inv q := by apply Subtype.ext; exact actWord_cancel γ q.val

theorem fullSelection_preserved (α : Coeffs X) (γ : X ≃ X)
    (τ : SelectorWire α ≃ SelectorWire α)
    (hα : ∀ q, α (τ q).val = α q.val)
    (hw : ∀ q x, (τ q).val (γ x) = q.val x) :
    (fullSelection α).Preserved (γ.sumCongr τ) := by
  apply Circuit.preserved_mul
  · apply Circuit.preserved_onRight γ
    apply selectorPhaseCircuit_preserved
    intro q
    simp only [selectorPhase, hα]
  · exact pauliSelection_preserved _ γ τ hw

theorem selectionAux_preserved (α : Coeffs X) (γ : X ≃ X)
    (τ : SelectorWire α ≃ SelectorWire α)
    (hα : ∀ q, α (τ q).val = α q.val)
    (hw : ∀ q x, (τ q).val (γ x) = q.val x) :
    (selectionAux α).Preserved (γ.sumCongr (τ.sumCongr (Equiv.refl (Fin 3)))) := by
  apply Circuit.preserved_rewire (Equiv.sumAssoc X (SelectorWire α) (Fin 3))
    (Circuit.preserved_onLeft (Equiv.refl (Fin 3)) (fullSelection_preserved α γ τ hα hw))
  intro z
  cases z with
  | inl z => cases z <;> rfl
  | inr z => rfl

theorem blockCircuit_preserved (α : Coeffs X) (γ : X ≃ X)
    (τ : SelectorWire α ≃ SelectorWire α)
    (hα : ∀ q, α (τ q).val = α q.val)
    (hw : ∀ q x, (τ q).val (γ x) = q.val x) :
    (blockCircuit α).Preserved (γ.sumCongr (τ.sumCongr (Equiv.refl (Fin 3)))) := by
  have hB := Circuit.preserved_onRight γ (oneHotCircuit_preserved α τ hα)
  exact Circuit.preserved_mul (Circuit.preserved_adjoint hB)
    (Circuit.preserved_mul (selectionAux_preserved α γ τ hα hw) hB)

theorem blockCircuit_symmetric {Γ : Subgroup (X ≃ X)} (U : Op X)
    (hU : Equivariant Γ U) : Nonempty (Symmetric Γ (blockCircuit (pauliCoeff U))) := by
  let τ (γ : Γ) := selectorPerm (pauliCoeff U) γ.val (coeff_orbit (hU γ.val γ.property))
  refine ⟨⟨fun γ => γ.val.sumCongr ((τ γ).sumCongr (Equiv.refl (Fin 3))),
    (fun _ _ => rfl), ?_⟩⟩
  intro γ
  apply blockCircuit_preserved
  · intro q
    exact coeff_orbit (hU γ.val γ.property) q.val
  · intro q x
    exact actWord_at_image γ.val q.val x
end Paper12
