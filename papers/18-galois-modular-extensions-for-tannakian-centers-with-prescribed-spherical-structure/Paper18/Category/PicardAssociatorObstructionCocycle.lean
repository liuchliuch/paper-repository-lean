import Paper18.Category.PicardAssociatorObstructionPentagon

/-! # The derived four-variable pentagon defect satisfies the cocycle equation

This is a categorical cancellation theorem for actual module-functor
products and actual natural associator comparisons. No pentagon, scalar
defect equation, or scalar cocycle equation is assumed.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u vM uM vN uN w
namespace Paper18.Category.PicardAssociatorObstruction
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
  [(A.fourSource b c d e).toFunctor.Full] [(A.fourSource b c d e).toFunctor.Faithful]
  [(A.fourSource (A.product a b) c d e).toFunctor.Full]
  [(A.fourSource (A.product a b) c d e).toFunctor.Faithful]
  [(A.fourSource a (A.product b c) d e).toFunctor.Full]
  [(A.fourSource a (A.product b c) d e).toFunctor.Faithful]
  [(A.fourSource a b (A.product c d) e).toFunctor.Full]
  [(A.fourSource a b (A.product c d) e).toFunctor.Faithful]
  [(A.fourSource a b c (A.product d e)).toFunctor.Full]
  [(A.fourSource a b c (A.product d e)).toFunctor.Faithful]
  [(A.fourSource a b c d).toFunctor.Full] [(A.fourSource a b c d).toFunctor.Faithful]
  [((A.diagram a b c d e).obj 9).toFunctor.Full]
  [((A.diagram a b c d e).obj 9).toFunctor.Faithful]
  [(A.left a).Linear ℂ] [(A.right e).Linear ℂ]

/-- The inhomogeneous four-cocycle equation is derived from the actual
five-input associahedron, not supplied as data. Multiplication of the
inputs here is the actual bifunctor, before choosing group representatives. -/
theorem pentagonDefect_cocycle :
    pentagonDefect S i A b c d e * pentagonDefect S i A a (A.product b c) d e *
        pentagonDefect S i A a b c (A.product d e) =
      pentagonDefect S i A (A.product a b) c d e *
        pentagonDefect S i A a b (A.product c d) e * pentagonDefect S i A a b c d := by
  let D := A.diagram a b c d e
  letI : (D.obj 0).toFunctor.Full := inferInstanceAs
    ((A.fourSource (A.product a b) c d e).toFunctor.Full)
  letI : (D.obj 0).toFunctor.Faithful := inferInstanceAs
    ((A.fourSource (A.product a b) c d e).toFunctor.Faithful)
  letI : (D.obj 1).toFunctor.Full := inferInstanceAs
    ((A.fourSource a (A.product b c) d e).toFunctor.Full)
  letI : (D.obj 1).toFunctor.Faithful := inferInstanceAs
    ((A.fourSource a (A.product b c) d e).toFunctor.Faithful)
  letI : (D.obj 2).toFunctor.Full := inferInstanceAs
    ((A.fourSource a b (A.product c d) e).toFunctor.Full)
  letI : (D.obj 2).toFunctor.Faithful := inferInstanceAs
    ((A.fourSource a b (A.product c d) e).toFunctor.Faithful)
  letI : (D.obj 5).toFunctor.Full := inferInstanceAs
    ((A.fourSource a b c (A.product d e)).toFunctor.Full)
  letI : (D.obj 5).toFunctor.Faithful := inferInstanceAs
    ((A.fourSource a b c (A.product d e)).toFunctor.Faithful)
  have h₀ : moduleFaceScalars S i D 0 = pentagonDefect S i A b c d e := by
    apply bundledComparisonScalar_eq
    have h := congrArg (fun f => (A.left a).map f) (pentagonDefect_spec S i A b c d e)
    simpa only [AssociatorSystem.pentagonLong, AssociatorSystem.pentagonShort,
      Iso.trans_hom, Functor.map_comp, Functor.map_smul] using h
  have h₁ : moduleFaceScalars S i D 1 = pentagonDefect S i A (A.product a b) c d e := rfl
  have h₂ : moduleFaceScalars S i D 2 = pentagonDefect S i A a (A.product b c) d e := rfl
  have h₃ : moduleFaceScalars S i D 3 = pentagonDefect S i A a b (A.product c d) e := rfl
  have h₄ : moduleFaceScalars S i D 4 = pentagonDefect S i A a b c (A.product d e) := rfl
  have h₅ : moduleFaceScalars S i D 5 = pentagonDefect S i A a b c d := by
    apply bundledComparisonScalar_eq
    have h := congrArg (fun f => (A.right e).map f) (pentagonDefect_spec S i A a b c d)
    simpa only [AssociatorSystem.pentagonLong, AssociatorSystem.pentagonShort,
      Iso.trans_hom, Functor.map_comp, Functor.map_smul] using h
  have h := moduleFaceScalars_cocycle S i D (A.diagram_square₁ a b c d e)
    (A.diagram_square₂ a b c d e) (A.diagram_square₃ a b c d e)
  rw [h₀, h₁, h₂, h₃, h₄, h₅] at h
  exact h

end Paper18.Category.PicardAssociatorObstruction
