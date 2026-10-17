import Paper18.Category.PicardAssociatorObstructionNaturality
import Paper18.Category.PicardAssociatorObstructionModuleDiagram

/-! # Pentagon defects of actual module-functor associator comparisons -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u vM uM vN uN w
namespace Paper18.Category.PicardAssociatorObstruction

namespace AssociatorSystem
variable {E : Type u} [Category.{v} E] (A : AssociatorSystem E)

abbrev fourSource (a b c d : E) : E := A.product (A.product (A.product a b) c) d
abbrev fourTarget (a b c d : E) : E := A.product a (A.product b (A.product c d))

/-- The path with three actual associator moves. -/
def pentagonLong (a b c d : E) : A.fourSource a b c d ≅ A.fourTarget a b c d :=
  (A.right d).mapIso (A.assoc a b c) ≪≫ A.assoc a (A.product b c) d ≪≫
    (A.left a).mapIso (A.assoc b c d)

/-- The path with two actual associator moves. -/
def pentagonShort (a b c d : E) : A.fourSource a b c d ≅ A.fourTarget a b c d :=
  A.assoc (A.product a b) c d ≪≫ A.assoc a b (A.product c d)

end AssociatorSystem

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M]
  [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)] [MonoidalLeftAction C M]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Linear ℂ]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton M ι) (i : ι)
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N] [MonoidalLeftAction C N]
  [∀ X : C, (MonoidalLeftAction.actionLeft N X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft N X).Linear ℂ]
  (A : AssociatorSystem
    (ModuleFunctor.Bundled C (ModuleComponent.Component (C := C) S i) N))
  (a b c d e : ModuleFunctor.Bundled C (ModuleComponent.Component (C := C) S i) N)

/-- The scalar of the actual long pentagon path relative to the short
one. Its existence and invertibility follow from component Schur theory. -/
def pentagonDefect [(A.fourSource a b c d).toFunctor.Full]
    [(A.fourSource a b c d).toFunctor.Faithful] : ℂˣ :=
  bundledComparisonScalar S i (A.pentagonLong a b c d) (A.pentagonShort a b c d)

lemma pentagonDefect_spec [(A.fourSource a b c d).toFunctor.Full]
    [(A.fourSource a b c d).toFunctor.Faithful] :
    (A.pentagonLong a b c d).hom =
      (pentagonDefect S i A a b c d : ℂ) • (A.pentagonShort a b c d).hom :=
  bundledComparisonScalar_spec S i _ _

/-- Vanishing of the extracted obstruction is exactly commutativity of
the actual pentagon, with no chosen scalar equation needed. -/
lemma pentagonDefect_eq_one_iff [(A.fourSource a b c d).toFunctor.Full]
    [(A.fourSource a b c d).toFunctor.Faithful] :
    pentagonDefect S i A a b c d = 1 ↔
      (A.pentagonLong a b c d).hom = (A.pentagonShort a b c d).hom := by
  constructor
  · intro h
    simpa only [h, Units.val_one, one_smul] using pentagonDefect_spec S i A a b c d
  · intro h
    apply bundledComparisonScalar_eq
    simpa only [Units.val_one, one_smul] using h

/-- An actual bifunctor and actual triple-comparison natural isomorphism
give the six-face cocycle equation without any pentagon or square input. -/
theorem associator_face_cocycle
    [∀ j : Fin 14, ((A.diagram a b c d e).obj j).toFunctor.Full]
    [∀ j : Fin 14, ((A.diagram a b c d e).obj j).toFunctor.Faithful] :
    moduleFaceScalars S i (A.diagram a b c d e) 0 *
        moduleFaceScalars S i (A.diagram a b c d e) 2 *
        moduleFaceScalars S i (A.diagram a b c d e) 4 =
      moduleFaceScalars S i (A.diagram a b c d e) 1 *
        moduleFaceScalars S i (A.diagram a b c d e) 3 *
        moduleFaceScalars S i (A.diagram a b c d e) 5 :=
  moduleFaceScalars_cocycle S i _ (A.diagram_square₁ a b c d e)
    (A.diagram_square₂ a b c d e) (A.diagram_square₃ a b c d e)

end Paper18.Category.PicardAssociatorObstruction
