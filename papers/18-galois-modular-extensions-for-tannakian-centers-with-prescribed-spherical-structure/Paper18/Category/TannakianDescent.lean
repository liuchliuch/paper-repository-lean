import Paper18.Category.TannakianGroupAction
import Paper18.Category.TannakianDeequivariantSemisimple

/-!
# The free-module equivariant comparison for Tannakian descent

The free module on an actual ambient object has canonical equivariant
structure induced by right translations of its regular algebra factor.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonObj Obj
universe v u
namespace Paper18.Category

section ModuleIso
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A : C} [MonObj A] {M N : Mod_ C A}

/-- An actual internal module morphism whose underlying morphism is an
isomorphism is itself an isomorphism. The inverse module law is derived
from the actual underlying inverse. -/
theorem internalModule_isIso_of_underlying (f : M ⟶ N) [IsIso f.hom] : IsIso f := by
  letI : IsMod_Hom A (asIso f.hom).hom := f.isMod_Hom
  let h : N ⟶ M := ⟨(asIso f.hom).inv⟩
  refine ⟨⟨h, ?_, ?_⟩⟩
  · apply Mod_.Hom.ext
    exact IsIso.hom_inv_id f.hom
  · apply Mod_.Hom.ext
    exact IsIso.inv_hom_id f.hom

end ModuleIso

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {G : Type} [Group G] [Fintype G] (T : TannakianCenter C G)

/-- The actual regular-algebra automorphism of right translation. -/
def TannakianCenter.regularTranslationIso (g : G) : T.regularAlgebra ≅ T.regularAlgebra :=
  T.inclusion.mapIso (Representation.rightTranslationIso g)

/-- Right translation on the regular factor gives a genuine module
intertwiner from the translated free module to the original free module. -/
def TannakianCenter.freeEquivariantHom (X : C) (g : G) :
    (T.moduleTranslation g).obj (T.deequivariantFree.obj X) ⟶ T.deequivariantFree.obj X :=
  Mod_.Hom.mk' (M := (T.moduleTranslation g).obj (T.deequivariantFree.obj X))
    (N := T.deequivariantFree.obj X) (T.regularTranslation g ▷ X) (by
    dsimp only [TannakianCenter.moduleTranslation, Mod_.comap, Mod_.scalarRestriction, TannakianCenter.deequivariantFree, InternalModule.freeFunctor]
    simp only [Category.assoc]
    change (T.regularTranslation g⁻¹ ▷ (T.regularAlgebra ⊗ X)) ≫
        ((α_ T.regularAlgebra T.regularAlgebra X).inv ≫ μ[T.regularAlgebra] ▷ X) ≫
        (T.regularTranslation g ▷ X) =
      T.regularAlgebra ◁ (T.regularTranslation g ▷ X) ≫
        (α_ T.regularAlgebra T.regularAlgebra X).inv ≫ μ[T.regularAlgebra] ▷ X
    let e := T.regularTranslationIso g
    letI : IsMonHom e.hom := T.regularTranslationIsMonHom g
    change e.inv ▷ (T.regularAlgebra ⊗ X) ≫
        ((α_ T.regularAlgebra T.regularAlgebra X).inv ≫ μ[T.regularAlgebra] ▷ X) ≫
        (e.hom ▷ X) =
      T.regularAlgebra ◁ (e.hom ▷ X) ≫
        (α_ T.regularAlgebra T.regularAlgebra X).inv ≫ μ[T.regularAlgebra] ▷ X
    calc
      _ = (α_ T.regularAlgebra T.regularAlgebra X).inv ≫
        ((e.inv ▷ T.regularAlgebra) ≫ μ[T.regularAlgebra] ≫ e.hom) ▷ X := by monoidal
      _ = (α_ T.regularAlgebra T.regularAlgebra X).inv ≫
        ((e.inv ▷ T.regularAlgebra) ≫ (e.hom ⊗ₘ e.hom) ≫ μ[T.regularAlgebra]) ▷ X := by
          rw [IsMonHom.mul_hom]
      _ = (α_ T.regularAlgebra T.regularAlgebra X).inv ≫
        ((T.regularAlgebra ◁ e.hom) ≫ μ[T.regularAlgebra]) ▷ X := by
          simp [MonoidalCategory.tensorHom_def, ← Category.assoc]
      _ = _ := by monoidal)

/-- The canonical equivariant structure map is an actual isomorphism of
modules, as its underlying regular-factor map is an actual isomorphism. -/
def TannakianCenter.freeEquivariantIso (X : C) (g : G) :
    (T.moduleTranslation g).obj (T.deequivariantFree.obj X) ≅ T.deequivariantFree.obj X := by
  letI : IsIso (T.freeEquivariantHom X g).hom :=
    (whiskerRightIso (T.regularTranslationIso g) X).isIso_hom
  letI := internalModule_isIso_of_underlying (T.freeEquivariantHom X g)
  exact asIso (T.freeEquivariantHom X g)

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
@[simp]
theorem TannakianCenter.freeEquivariantIso_hom (X : C) (g : G) :
    (T.freeEquivariantIso X g).hom.hom = T.regularTranslation g ▷ X := rfl

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
@[simp]
theorem TannakianCenter.freeEquivariantIso_inv_hom (X : C) (g : G) :
    (T.freeEquivariantIso X g).inv.hom = T.regularTranslation g⁻¹ ▷ X := by
  let e := whiskerRightIso (T.regularTranslationIso g) X
  letI : IsIso (T.regularTranslation g ▷ X) := e.isIso_hom
  apply (cancel_mono (T.regularTranslation g ▷ X)).mp
  have h := congrArg (fun k => k.hom) (T.freeEquivariantIso X g).inv_hom_id
  change (T.freeEquivariantIso X g).inv.hom ≫ (T.regularTranslation g ▷ X) = 𝟙 _ at h
  rw [h]
  change 𝟙 _ = e.inv ≫ e.hom
  exact e.inv_hom_id.symm

/-- The actual free module, with the coherent translation isomorphisms
proved from multiplication in the finite group. -/
def TannakianCenter.freeEquivariantObj (X : C) : T.deequivariantAction.Equivariant where
  obj := T.deequivariantFree.obj X
  structureIso := T.freeEquivariantIso X
  unit := by
    apply Mod_.Hom.ext
    change T.regularTranslation (1 : G) ▷ X = 𝟙 _
    rw [T.regularTranslation_one, id_whiskerRight]
  mul g h := by
    apply Mod_.Hom.ext
    change (T.regularTranslation h ▷ X) ≫ (T.regularTranslation g ▷ X) =
      𝟙 _ ≫ T.regularTranslation (g * h) ▷ X
    rw [Category.id_comp, T.regularTranslation_mul, comp_whiskerRight]

/-- Free extension with its actual equivariant structure defines the
Tannakian descent comparison functor. -/
def TannakianCenter.descentComparison : C ⥤ T.deequivariantAction.Equivariant where
  obj := T.freeEquivariantObj
  map f :=
    { hom := InternalModule.freeMap f
      comm g := by
        apply Mod_.Hom.ext
        change (T.regularAlgebra ◁ f) ≫ (T.regularTranslation g ▷ _) =
          (T.regularTranslation g ▷ _) ≫ (T.regularAlgebra ◁ f)
        exact whisker_exchange (T.regularTranslation g) f }
  map_id X := by
    apply WeakAction.Equivariant.Hom.ext
    apply Mod_.Hom.ext
    change T.regularAlgebra ◁ 𝟙 X = 𝟙 _
    exact MonoidalCategory.whiskerLeft_id _ _
  map_comp f g := by
    apply WeakAction.Equivariant.Hom.ext
    apply Mod_.Hom.ext
    change T.regularAlgebra ◁ (f ≫ g) = (T.regularAlgebra ◁ f) ≫ (T.regularAlgebra ◁ g)
    exact whiskerLeft_comp _ _ _

instance TannakianCenter.descentComparisonAdditive : T.descentComparison.Additive where
  map_add := by
    intro X Y f g
    apply WeakAction.Equivariant.Hom.ext
    apply Mod_.Hom.ext
    change T.regularAlgebra ◁ (f + g) = (T.regularAlgebra ◁ f) + (T.regularAlgebra ◁ g)
    simp

instance TannakianCenter.descentComparisonLinear : T.descentComparison.Linear ℂ where
  map_smul f c := by
    apply WeakAction.Equivariant.Hom.ext
    apply Mod_.Hom.ext
    change T.regularAlgebra ◁ (c • f) = c • (T.regularAlgebra ◁ f)
    simp

end Paper18.Category
