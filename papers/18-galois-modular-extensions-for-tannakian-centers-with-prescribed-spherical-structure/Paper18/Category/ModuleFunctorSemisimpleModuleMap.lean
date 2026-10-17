import Paper18.Category.ModuleFunctorFiniteBasic
import Mathlib.CategoryTheory.Monoidal.Mod_

/-! # Actual transport of native algebra modules by module functors -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonObj MonoidalLeftAction
universe v u vM uM vN uN
namespace Paper18.Category.ModuleFunctor
open MonoidalLeftAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type uM} [Category.{vM} M] [MonoidalLeftAction C M]
  {N : Type uN} [Category.{vN} N] [MonoidalLeftAction C N]
  {A : C} [MonObj A] (F : M ⥤ N) [F.LeftLinear C]

/-- The actual lineator transports an actual algebra module action. -/
def mapActionModule (X : Mod_ M A) : Mod_ N A := by
  letI : ModObj A (F.obj X.X) :=
    { smul := Functor.LaxLeftLinear.μₗ F A X.X ≫ F.map γ[A,X.X]
      one_smul' := by
        rw [← assoc, Functor.LaxLeftLinear.μₗ_naturality_left, assoc,
          ← F.map_comp, ModObj.one_smul]
        exact (Functor.LaxLeftLinear.μₗ_unitality F X.X).symm
      mul_smul' := by
        rw [Functor.LaxLeftLinear.μₗ_naturality_left_assoc,
          ← F.map_comp, ModObj.mul_smul, F.map_comp, F.map_comp,
          Functor.LaxLeftLinear.μₗ_associativity_assoc]
        rw [← Functor.LaxLeftLinear.μₗ_naturality_right_assoc]
        simp only [actionHomRight_comp, assoc] }
  exact ⟨F.obj X.X⟩

@[simp] lemma mapActionModule_X (X : Mod_ M A) : (mapActionModule F X).X = F.obj X.X := rfl

/-- Genuine action-preserving maps are transported by the actual functor. -/
def mapActionModuleHom {X Y : Mod_ M A} (f : X ⟶ Y) :
    mapActionModule F X ⟶ mapActionModule F Y :=
  Mod_.Hom.mk' (F.map f.hom) (by
    change (Functor.LaxLeftLinear.μₗ F A X.X ≫ F.map γ[A,X.X]) ≫ F.map f.hom =
      (A ⊴ₗ F.map f.hom) ≫ Functor.LaxLeftLinear.μₗ F A Y.X ≫ F.map γ[A,Y.X]
    rw [assoc, ← F.map_comp, IsMod_Hom.smul_hom, F.map_comp,
      ← assoc, ← Functor.LaxLeftLinear.μₗ_naturality_right, assoc])

/-- The actual functor on module objects. -/
def mapActionModules : Mod_ M A ⥤ Mod_ N A where
  obj := mapActionModule F
  map := mapActionModuleHom F
  map_id _ := by apply Mod_.Hom.ext; exact F.map_id _
  map_comp f g := by apply Mod_.Hom.ext; exact F.map_comp f.hom g.hom

variable {F} {G : M ⥤ N} [G.LeftLinear C] (τ : F ⟶ G) [IsModuleNatural C τ]

/-- Module naturality gives an actual transformation on algebra modules. -/
def mapActionModulesTransformation : mapActionModules (A := A) F ⟶ mapActionModules G where
  app X := Mod_.Hom.mk' (τ.app X.X) (by
    change (Functor.LaxLeftLinear.μₗ F A X.X ≫ F.map γ[A,X.X]) ≫ τ.app X.X =
      (A ⊴ₗ τ.app X.X) ≫ Functor.LaxLeftLinear.μₗ G A X.X ≫ G.map γ[A,X.X]
    rw [assoc, τ.naturality, ← assoc, IsModuleNatural.lineator, assoc])
  naturality {X Y} f := by apply Mod_.Hom.ext; exact τ.naturality f.hom

end Paper18.Category.ModuleFunctor
