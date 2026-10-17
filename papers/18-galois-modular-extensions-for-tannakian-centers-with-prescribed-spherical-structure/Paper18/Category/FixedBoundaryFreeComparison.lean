import Paper18.Category.FixedBoundaryModuleEquivalence
import Paper18.Category.FixedBoundaryModuleFunctorMonoidal

/-! # The actual free-module comparison for a specified boundary pair

The original tensorator and the inverse algebra component of the specified
alpha identify free modules before and after the actual boundary functor.
This comparison is constructed from actual module morphisms.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category.InternalModule
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A B : C} [MonObj A] [MonObj B] (e : A ≅ B) [IsMonHom e.hom]

/-- Change the actual free algebra factor along an algebra isomorphism. -/
def comapFreeHom (X : C) : free A X ⟶ (Mod_.comap e.hom).obj (free B X) :=
  Mod_.Hom.mk' (e.hom ▷ X) (by
    change ((α_ A A X).inv ≫ μ[A] ▷ X) ≫ (e.hom ▷ X) =
      (A ◁ (e.hom ▷ X)) ≫ (e.hom ▷ (B ⊗ X)) ≫
        (α_ B B X).inv ≫ μ[B] ▷ X
    calc
      _ = (α_ A A X).inv ≫ (μ[A] ≫ e.hom) ▷ X := by
        rw [comp_whiskerRight]; simp only [Category.assoc]
      _ = (α_ A A X).inv ≫ ((e.hom ⊗ₘ e.hom) ≫ μ[B]) ▷ X := by
        rw [IsMonHom.mul_hom]
      _ = _ := by
        rw [comp_whiskerRight]
        have hn := associator_inv_naturality e.hom e.hom (𝟙 X)
        simp only [MonoidalCategory.tensorHom_id] at hn
        rw [← reassoc_of% hn]
        simp only [MonoidalCategory.tensorHom_def', Category.assoc])

/-- Change of actual free algebra factor is an actual module isomorphism. -/
def comapFreeIso (X : C) : free A X ≅ (Mod_.comap e.hom).obj (free B X) := by
  let f := comapFreeHom e X
  letI : IsIso f.hom := (whiskerRightIso e X).isIso_hom
  letI := internalModule_isIso_of_underlying f
  exact asIso f

@[simp] theorem comapFreeIso_hom (X : C) : (comapFreeIso e X).hom.hom = e.hom ▷ X := rfl

end Paper18.Category.InternalModule

namespace Paper18.Category
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N]
  [RightRigidCategory N] [HasCoequalizers N]
  {i : A ⥤ N} [i.Braided] (P : BoundaryAutoequivalence i) (R : A)
  [MonObj R] [IsCommMonObj R]

/-- The actual free comparison retains the inverse specified algebra
component; its carrier is alpha_R inverse followed by the original tensorator. -/
def BoundaryAutoequivalence.moduleFreeIso (X : N) :
    InternalModule.free (i.obj R) (P.functor.obj X) ≅
      (P.moduleFunctor R).obj (InternalModule.free (i.obj R) X) := by
  let e := (P.boundaryAlgebraIso R).symm
  letI : IsMonHom e.hom := P.boundaryAlgebraIsoInvIsMonHom R
  exact InternalModule.comapFreeIso e (P.functor.obj X) ≪≫
    (Mod_.comap e.hom).mapIso (InternalModule.mapModuleFreeIso P.functor X)

@[simp] theorem BoundaryAutoequivalence.moduleFreeIso_hom (X : N) :
    (P.moduleFreeIso R X).hom.hom =
      (P.boundaryAlgebraIso R).inv ▷ P.functor.obj X ≫
        Functor.LaxMonoidal.μ P.functor (i.obj R) X := rfl

/-- Naturality follows from the original ambient tensorator and the
actual inverse algebra component. -/
def BoundaryAutoequivalence.moduleFreeNatIso :
    P.functor ⋙ InternalModule.freeFunctor (A := i.obj R) ≅
      InternalModule.freeFunctor (A := i.obj R) ⋙ P.moduleFunctor R :=
  NatIso.ofComponents (P.moduleFreeIso R) (by
    intro X Y f
    apply Mod_.Hom.ext
    change (i.obj R ◁ P.functor.map f) ≫
        (P.boundaryAlgebraIso R).inv ▷ P.functor.obj Y ≫
          Functor.LaxMonoidal.μ P.functor (i.obj R) Y =
      ((P.boundaryAlgebraIso R).inv ▷ P.functor.obj X ≫
        Functor.LaxMonoidal.μ P.functor (i.obj R) X) ≫
          P.functor.map (i.obj R ◁ f)
    rw [← Category.assoc, whisker_exchange]
    simp only [Category.assoc]
    rw [Functor.LaxMonoidal.μ_natural_right])

end Paper18.Category
