import Paper18.Category.PivotalFunctor
import Mathlib.CategoryTheory.Monoidal.Action.End
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Actual adjunctions induced by rigid actions -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u v' u'
namespace Paper18.Category.ModuleFunctor
open MonoidalLeftAction
attribute [local instance] endofunctorMonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  (M : Type u') [Category.{v'} M] [MonoidalLeftAction C M]
  (c d : C) [ExactPairing c d]

/-- The actual cup of a rigid action, transported through the actual
strong monoidal action functor. -/
def actionCoevaluation : 𝟭 M ⟶ actionLeft M d ⋙ actionLeft M c := by
  letI := mapExactPairing (curriedActionMop C M) c d
  exact (η_ ((curriedActionMop C M).obj c) ((curriedActionMop C M).obj d)).unmop

/-- The actual cap of a rigid action. -/
def actionEvaluation : actionLeft M c ⋙ actionLeft M d ⟶ 𝟭 M := by
  letI := mapExactPairing (curriedActionMop C M) c d
  exact (ε_ ((curriedActionMop C M).obj c) ((curriedActionMop C M).obj d)).unmop

@[simp]
lemma actionCoevaluation_app (m : M) :
    (actionCoevaluation M c d).app m =
      (λₗ[C] m).inv ≫ (η_ c d) ⊵ₗ m ≫ (αₗ c d m).hom := rfl

@[simp]
lemma actionEvaluation_app (m : M) :
    (actionEvaluation M c d).app m =
      (αₗ d c m).inv ≫ (ε_ c d) ⊵ₗ m ≫ (λₗ[C] m).hom := rfl

/-- An actual exact pairing in the acting category gives an ordinary
adjunction of the actual action functors. -/
def actionAdjunction : actionLeft M d ⊣ actionLeft M c where
  unit := actionCoevaluation M c d
  counit := actionEvaluation M c d
  left_triangle_components m := by
    let A := curriedActionMop C M
    letI := mapExactPairing A c d
    have h := congrArg (fun f => f.unmop.app m)
      (ExactPairing.coevaluation_evaluation (A.obj c) (A.obj d))
    change d ⊴ₗ (actionCoevaluation M c d).app m ≫ 𝟙 _ ≫
      (actionEvaluation M c d).app (d ⊙ₗ m) = 𝟙 _ ≫ 𝟙 _ at h
    simpa only [id_comp, comp_id] using h
  right_triangle_components m := by
    let A := curriedActionMop C M
    letI := mapExactPairing A c d
    have h := congrArg (fun f => f.unmop.app m)
      (ExactPairing.evaluation_coevaluation (A.obj c) (A.obj d))
    change (actionCoevaluation M c d).app (c ⊙ₗ m) ≫ 𝟙 _ ≫
      c ⊴ₗ (actionEvaluation M c d).app m = 𝟙 _ ≫ 𝟙 _ at h
    simpa only [id_comp, comp_id] using h

@[simp] lemma actionAdjunction_unit : (actionAdjunction M c d).unit =
    actionCoevaluation M c d := rfl
@[simp] lemma actionAdjunction_counit : (actionAdjunction M c d).counit =
    actionEvaluation M c d := rfl

end Paper18.Category.ModuleFunctor
