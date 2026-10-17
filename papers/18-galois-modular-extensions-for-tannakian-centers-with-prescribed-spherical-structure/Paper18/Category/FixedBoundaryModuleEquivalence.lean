import Paper18.Category.FixedBoundaryModules
import Paper18.Category.TannakianDeequivariantNondegenerateBasic
import Paper18.Category.FunctorRetract

/-! # Tensor equivalences induce actual equivalences of separable modules -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category.InternalModule
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] {A : C} [MonObj A]

/-- The actual tensorator is a free-module intertwiner. -/
def mapModuleFreeHom (X : C) :
    free (F.obj A) (F.obj X) ⟶ (mapModules F).obj (free A X) :=
  Mod_.Hom.mk' (Functor.LaxMonoidal.μ F A X) (by
    change γ[F.obj A,(free (F.obj A) (F.obj X)).X] ≫ Functor.LaxMonoidal.μ F A X =
      (F.obj A ◁ Functor.LaxMonoidal.μ F A X) ≫
        Functor.LaxMonoidal.μ F A (A ⊗ X) ≫ F.map γ[A,(free A X).X]
    exact freeAction_tensorator F X)

/-- Actual free modules commute with strong tensor transport. -/
def mapModuleFreeIso (X : C) :
    free (F.obj A) (F.obj X) ≅ (mapModules F).obj (free A X) := by
  let f := mapModuleFreeHom F (A := A) X
  letI : IsIso f.hom := (Functor.Monoidal.μIso F A X).isIso_hom
  letI := internalModule_isIso_of_underlying f
  exact asIso f

variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [F.Full] [F.Faithful] [F.EssSurj] (S : SeparableAlgebra A)

omit [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D]
  [MonoidalLinear ℂ D] [F.Full] [F.Faithful] in
include S in
/-- Separability makes every target module a retract of an actual image
free module. No essential-surjectivity statement for modules is assumed. -/
theorem mapModules_retract_dominant (M : Mod_ D (F.obj A)) :
    ∃ X : Mod_ C A, Nonempty (Retract M ((mapModules F).obj X)) := by
  let X := F.objPreimage M.X
  let e := F.objObjPreimageIso M.X
  let r := (S.map F).freeRetract M
  let q := (freeFunctor (A := F.obj A)).mapIso e.symm ≪≫ mapModuleFreeIso F X
  exact ⟨free A X, ⟨r.trans (Retract.ofIso q)⟩⟩

include S in
/-- Full faithfulness, actual separable retracts, and source kernels prove
essential surjectivity of tensor transport on actual modules. -/
theorem mapModules_essSurj : (mapModules F (A := A)).EssSurj := by
  letI : IsIdempotentComplete (Mod_ C A) :=
    (Idempotents.isIdempotentComplete_iff_idempotents_have_kernels (C := Mod_ C A)).mpr
      (fun X p _ => inferInstance)
  exact essSurj_of_retract_dominant (mapModules F) (mapModules_retract_dominant F S)

include S in
/-- An actual tensor equivalence induces an actual equivalence of the
categories of modules over an actual separable algebra and its image. -/
def moduleEquivalence : Mod_ C A ≌ Mod_ D (F.obj A) := by
  letI := mapModules_essSurj F S
  letI : (mapModules F (A := A)).IsEquivalence := {}
  exact (mapModules F).asEquivalence

end Paper18.Category.InternalModule
