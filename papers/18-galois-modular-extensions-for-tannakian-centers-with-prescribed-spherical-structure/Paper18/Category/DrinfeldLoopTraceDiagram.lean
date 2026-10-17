import Paper18.Category.DrinfeldLoopTraceChoi

/-!
# Vanishing of the actual induction annular trace

The actual annulus is identified with a rigid Choi contraction. Its actual
partial trace factors through a morphism from the tensor unit to `A`, so a
zero unit-Hom space forces vanishing. No numerical loop-trace law or
sphericality certificate is an input.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [MonoidalPreadditive C]

/-- The actual annular term has zero pivotal trace whenever its label has
no actual morphisms from the tensor unit. -/
lemma inductionLoopAnnularTerm_rightTrace_eq_zero (J : PivotalStructure C) (T A : C)
    (hA : ∀ a : 𝟙_ C ⟶ A, a = 0)
    (u : T ⟶ dual C (dual C T) ⊗ A) (p : dual C (dual C T) ⊗ A ⟶ T) :
    J.rightTrace (inductionLoopAnnularTerm J T A u p) = 0 := by
  rw [← inductionLoopAnnularBare_trace, inductionLoopAnnularBare_eq_choi]
  exact rightTrace_annularChoi_eq_zero J T A hA _ _

end Paper18.Category.Drinfeld
