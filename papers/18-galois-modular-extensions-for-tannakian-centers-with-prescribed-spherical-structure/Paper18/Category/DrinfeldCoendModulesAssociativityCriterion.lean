import Paper18.Category.DrinfeldCoendModulesCapTensor

/-! # Actual cap associativity is equivalent to the annular tensor law -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D]

instance orderedProductKernel_isIso (X Y : D) : IsIso (orderedProductKernel X Y) := by
  dsimp only [orderedProductKernel, tensorμ]
  infer_instance

/-- For every actual natural annular family, actual cap associativity is
exactly its actual cabled tensor law. Both directions use proved rigid and
braided identities, with no assumed module or half-braiding laws. -/
lemma cap_associativity_iff_tensor (M : D) (h : ∀ T : D, T ⊗ M ⟶ T ⊗ M)
    (hn : ∀ {T U : D} (f : T ⟶ U), f ▷ M ≫ h U = h T ≫ f ▷ M)
    (X Y : D) :
    (productKernel X Y ▷ M ≫ capOf (Y ⊗ X) M (h (Y ⊗ X)) =
      (α_ (dual D X ⊗ X) (dual D Y ⊗ Y) M).hom ≫
        (dual D X ⊗ X) ◁ capOf Y M (h Y) ≫ capOf X M (h X)) ↔
      h (X ⊗ Y) = annularTensor X Y M (h X) (h Y) := by
  rw [natural_cap_product_reindex M h hn X Y, ← capOf_annularTensor X Y M (h X) (h Y)]
  constructor
  · intro he
    exact capOf_injective (X ⊗ Y) M ((cancel_epi (orderedProductKernel X Y ▷ M)).mp he)
  · intro he
    rw [he]

end Paper18.Category.DrinfeldCoendModules
