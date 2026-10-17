import Paper18.Category.FixedBoundaryRegularMonoidal
import Paper18.Category.TannakianDescent
import Paper18.Category.RelativeTensorFree

/-! # Actual regular descent for an arbitrary representation embedding

The canonical free module carries the actual right-translation action.
This construction does not require its algebra to be transparent or its
representation image to equal the full center.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators MonObj Obj
universe v u
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [CategoryTheory.Limits.HasCoequalizers C]
  {G : Type} [Group G] [Fintype G]
  (F : FDRep ℂ G ⥤ C) [F.Braided] [F.Additive] [F.Linear ℂ]

abbrev regularFree : C ⥤ Modules F := InternalModule.freeFunctor (A := regularAlgebra F)

/-- Right translation on the regular factor gives a genuine module
intertwiner from the translated free module to the original free module. -/
def freeEquivariantHom (X : C) (g : G) :
    ((moduleTranslation F) g).obj ((regularFree F).obj X) ⟶ (regularFree F).obj X :=
  Mod_.Hom.mk' (M := ((moduleTranslation F) g).obj ((regularFree F).obj X))
    (N := (regularFree F).obj X) ((regularTranslation F) g ▷ X) (by
    dsimp only [moduleTranslation, Mod_.comap, Mod_.scalarRestriction, regularFree, InternalModule.freeFunctor]
    simp only [Category.assoc]
    change ((regularTranslation F) g⁻¹ ▷ ((regularAlgebra F) ⊗ X)) ≫
        ((α_ (regularAlgebra F) (regularAlgebra F) X).inv ≫ μ[(regularAlgebra F)] ▷ X) ≫
        ((regularTranslation F) g ▷ X) =
      (regularAlgebra F) ◁ ((regularTranslation F) g ▷ X) ≫
        (α_ (regularAlgebra F) (regularAlgebra F) X).inv ≫ μ[(regularAlgebra F)] ▷ X
    let e := (regularTranslationIso F) g
    letI : IsMonHom e.hom := regularTranslationIsMonHom F g
    change e.inv ▷ ((regularAlgebra F) ⊗ X) ≫
        ((α_ (regularAlgebra F) (regularAlgebra F) X).inv ≫ μ[(regularAlgebra F)] ▷ X) ≫
        (e.hom ▷ X) =
      (regularAlgebra F) ◁ (e.hom ▷ X) ≫
        (α_ (regularAlgebra F) (regularAlgebra F) X).inv ≫ μ[(regularAlgebra F)] ▷ X
    calc
      _ = (α_ (regularAlgebra F) (regularAlgebra F) X).inv ≫
        ((e.inv ▷ (regularAlgebra F)) ≫ μ[(regularAlgebra F)] ≫ e.hom) ▷ X := by monoidal
      _ = (α_ (regularAlgebra F) (regularAlgebra F) X).inv ≫
        ((e.inv ▷ (regularAlgebra F)) ≫ (e.hom ⊗ₘ e.hom) ≫ μ[(regularAlgebra F)]) ▷ X := by
          rw [IsMonHom.mul_hom]
      _ = (α_ (regularAlgebra F) (regularAlgebra F) X).inv ≫
        (((regularAlgebra F) ◁ e.hom) ≫ μ[(regularAlgebra F)]) ▷ X := by
          simp [MonoidalCategory.tensorHom_def, ← Category.assoc]
      _ = _ := by monoidal)

/-- The canonical equivariant structure map is an actual isomorphism of
modules, as its underlying regular-factor map is an actual isomorphism. -/
def freeEquivariantIso (X : C) (g : G) :
    ((moduleTranslation F) g).obj ((regularFree F).obj X) ≅ (regularFree F).obj X := by
  letI : IsIso ((freeEquivariantHom F) X g).hom :=
    (whiskerRightIso ((regularTranslationIso F) g) X).isIso_hom
  letI := internalModule_isIso_of_underlying ((freeEquivariantHom F) X g)
  exact asIso ((freeEquivariantHom F) X g)

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
@[simp]
theorem freeEquivariantIso_hom (X : C) (g : G) :
    ((freeEquivariantIso F) X g).hom.hom = (regularTranslation F) g ▷ X := rfl

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
@[simp]
theorem freeEquivariantIso_inv_hom (X : C) (g : G) :
    ((freeEquivariantIso F) X g).inv.hom = (regularTranslation F) g⁻¹ ▷ X := by
  let e := whiskerRightIso ((regularTranslationIso F) g) X
  letI : IsIso ((regularTranslation F) g ▷ X) := e.isIso_hom
  apply (cancel_mono ((regularTranslation F) g ▷ X)).mp
  have h := congrArg (fun k => k.hom) ((freeEquivariantIso F) X g).inv_hom_id
  change ((freeEquivariantIso F) X g).inv.hom ≫ ((regularTranslation F) g ▷ X) = 𝟙 _ at h
  rw [h]
  change 𝟙 _ = e.inv ≫ e.hom
  exact e.inv_hom_id.symm

/-- The actual free module, with the coherent translation isomorphisms
proved from multiplication in the finite group. -/
def freeEquivariantObj (X : C) : (regularAction F).Equivariant where
  obj := (regularFree F).obj X
  structureIso := (freeEquivariantIso F) X
  unit := by
    apply Mod_.Hom.ext
    change (regularTranslation F) (1 : G) ▷ X = 𝟙 _
    rw [(regularTranslation_one F), id_whiskerRight]
  mul g h := by
    apply Mod_.Hom.ext
    change ((regularTranslation F) h ▷ X) ≫ ((regularTranslation F) g ▷ X) =
      𝟙 _ ≫ (regularTranslation F) (g * h) ▷ X
    rw [Category.id_comp, (regularTranslation_mul F), comp_whiskerRight]

/-- Free extension with its actual equivariant structure defines the
Tannakian descent comparison functor. -/
def descentComparison : C ⥤ (regularAction F).Equivariant where
  obj := (freeEquivariantObj F)
  map f :=
    { hom := InternalModule.freeMap f
      comm g := by
        apply Mod_.Hom.ext
        change ((regularAlgebra F) ◁ f) ≫ ((regularTranslation F) g ▷ _) =
          ((regularTranslation F) g ▷ _) ≫ ((regularAlgebra F) ◁ f)
        exact whisker_exchange ((regularTranslation F) g) f }
  map_id X := by
    apply WeakAction.Equivariant.Hom.ext
    apply Mod_.Hom.ext
    change (regularAlgebra F) ◁ 𝟙 X = 𝟙 _
    exact MonoidalCategory.whiskerLeft_id _ _
  map_comp f g := by
    apply WeakAction.Equivariant.Hom.ext
    apply Mod_.Hom.ext
    change (regularAlgebra F) ◁ (f ≫ g) = ((regularAlgebra F) ◁ f) ≫ ((regularAlgebra F) ◁ g)
    exact whiskerLeft_comp _ _ _

instance descentComparisonAdditive : (descentComparison F).Additive where
  map_add := by
    intro X Y f g
    apply WeakAction.Equivariant.Hom.ext
    apply Mod_.Hom.ext
    change (regularAlgebra F) ◁ (f + g) = ((regularAlgebra F) ◁ f) + ((regularAlgebra F) ◁ g)
    simp

instance descentComparisonLinear : (descentComparison F).Linear ℂ where
  map_smul f c := by
    apply WeakAction.Equivariant.Hom.ext
    apply Mod_.Hom.ext
    change (regularAlgebra F) ◁ (c • f) = c • ((regularAlgebra F) ◁ f)
    simp


end Paper18.Category.FixedBoundary
