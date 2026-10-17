import Paper18.Category.FixedBoundaryModuleWattsEquivalence

/-!
# Actual module trivialization from the representing unit value

A specified isomorphism from the representing object to the tensor unit
extends to a specified module natural isomorphism with identity. Its unit
component is exactly the original specified isomorphism.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.ModuleFunctor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The actual natural isomorphism obtained by right tensoring an actual
object isomorphism. -/
def tensorRightNaturalIso {U V : C} (e : U ≅ V) : tensorRight U ≅ tensorRight V :=
  NatIso.ofComponents (fun X => whiskerLeftIso X e)
    (fun {X Y} f => (tensorRightTransformation e.hom).naturality f)

instance tensorRightNaturalIso_moduleNatural {U V : C} (e : U ≅ V) :
    IsModuleNatural C (tensorRightNaturalIso e).hom := by
  change IsModuleNatural C (tensorRightTransformation e.hom)
  infer_instance

variable (F : C ⥤ C) [F.LeftLinear C]

/-- The actual ordinary identification extracted from the representing
unit object, including its precise chosen normalization. -/
def regularModuleUnitTrivialization (u : F.obj (𝟙_ C) ≅ 𝟙_ C) : F ≅ 𝟭 C :=
  regularRepresentationIso F ≪≫ tensorRightNaturalIso u ≪≫
    (regularRepresentationIso (𝟭 C)).symm

instance regularModuleUnitTrivialization_moduleNatural (u : F.obj (𝟙_ C) ≅ 𝟙_ C) :
    IsModuleNatural C (regularModuleUnitTrivialization F u).hom := by
  change IsModuleNatural C
    ((regularRepresentationIso F).hom ≫ (tensorRightNaturalIso u).hom ≫
      (regularRepresentationIso (𝟭 C)).inv)
  infer_instance

/-- The extracted identification retains exactly the specified value at
the tensor unit. -/
@[simp] theorem regularModuleUnitTrivialization_unit (u : F.obj (𝟙_ C) ≅ 𝟙_ C) :
    (regularModuleUnitTrivialization F u).hom.app (𝟙_ C) = u.hom := by
  change (transformationOfUnit F (𝟭 C) u.hom).app (𝟙_ C) = _
  exact transformationOfUnit_app_unit F (𝟭 C) u.hom

/-- The actual module trivialization with prescribed unit component is
unique. -/
theorem regularModuleUnitTrivialization_unique (u : F.obj (𝟙_ C) ≅ 𝟙_ C)
    (β : F ≅ 𝟭 C) [IsModuleNatural C β.hom]
    (hβ : β.hom.app (𝟙_ C) = u.hom) : β = regularModuleUnitTrivialization F u := by
  apply Iso.ext
  apply moduleNatTrans_ext
  rw [hβ, regularModuleUnitTrivialization_unit]

end Paper18.Category.ModuleFunctor
