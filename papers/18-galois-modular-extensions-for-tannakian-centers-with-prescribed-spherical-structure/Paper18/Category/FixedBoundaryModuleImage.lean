import Paper18.Category.FixedBoundaryModuleEquivalence

/-!
# Actual module image from the underlying categorical image

For a fully faithful strong tensor functor and a separable algebra, every
actual target module whose underlying object is in the tensor functor's
essential image is itself in the essential image of module transport.
The proof uses the actual separability retraction and splitting of the
resulting actual source idempotent.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category.InternalModule
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  (F : C ⥤ D) [F.Monoidal] [F.Full] [F.Faithful]
  {A : C} [MonObj A] (S : SeparableAlgebra A)
include S

/-- Actual underlying-image membership lifts to actual module-image
membership, without assuming global essential surjectivity of F. -/
theorem mapModules_essImage_of_underlying (M : Mod_ D (F.obj A))
    (hM : ∃ X : C, Nonempty (F.obj X ≅ M.X)) :
    ∃ X : Mod_ C A, Nonempty ((mapModules F).obj X ≅ M) := by
  obtain ⟨X, ⟨e⟩⟩ := hM
  let r := (S.map F).freeRetract M
  let q := (freeFunctor (A := F.obj A)).mapIso e.symm ≪≫ mapModuleFreeIso F X
  letI : IsIdempotentComplete (Mod_ C A) :=
    (Idempotents.isIdempotentComplete_iff_idempotents_have_kernels (C := Mod_ C A)).mpr
      (fun X p _ => inferInstance)
  exact essImage_of_retract (mapModules F) (r.trans (Retract.ofIso q))

end Paper18.Category.InternalModule
