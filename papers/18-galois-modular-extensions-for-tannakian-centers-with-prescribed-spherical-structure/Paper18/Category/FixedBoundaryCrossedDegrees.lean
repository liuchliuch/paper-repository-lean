import Paper18.Category.FixedBoundaryCrossedMonodromy
import Paper18.Category.FixedBoundaryCrossedHexagon
import Paper18.Category.FixedBoundaryModuleGrading
import Paper18.Category.FixedBoundaryRegularMonoidal

/-!
# Genuine crossed maps on every actual C₂ homogeneous module

Actual module degrees imply the actual regular-algebra monodromy equation.
Consequently the translated crossing and its neutral-factor hexagon apply
to the original de-equivariantization with no monodromy or crossed-coherence
premise left to supply.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [HasCoequalizers C]
  (F : FDRep ℂ RepresentationZ2.H ⥤ C) [F.Braided] [F.Additive] [F.Linear ℂ]
  (B : TensorInverse (F.obj RepresentationZ2.signRep))
  (hR : Centralizes (F.obj RepresentationZ2.signRep) (regularAlgebra F))

local instance imageFunctionsMonObj : MonObj (F.obj (Representation.functions (G := RepresentationZ2.H))) :=
  Functor.monObjObj _

abbrev regularDegreeCharacter : 𝟭 (Modules F) ≅ 𝟭 (Modules F) :=
  B.moduleMonodromyCharacter (regularAlgebra F) hR

/-- The actual algebra isomorphism for translation by a degree. -/
def degreeTranslationIso (g : ZMod 2) : regularAlgebra F ≅ regularAlgebra F :=
  F.mapIso (Representation.rightTranslationIso (Multiplicative.ofAdd g))

instance degreeTranslationIsoIsMonHom (g : ZMod 2) :
    IsMonHom (degreeTranslationIso F g).hom := by
  change IsMonHom (F.map (Representation.rightTranslation (Multiplicative.ofAdd g)))
  infer_instance

/-- Actual homogeneous module degrees give the actual ambient monodromy
needed to descend the other crossing. -/
theorem regular_module_monodromy (g : ZMod 2) (M : Modules F)
    (hM : Homogeneous (regularDegreeCharacter F B hR) g M) :
    (doubleBraiding (regularAlgebra F) M.X).hom = (degreeTranslationIso F g).hom ▷ M.X := by
  have h := congrArg (fun f : M ⟶ M => f.hom) hM
  have hx : Homogeneous B.monodromyCharacter g M.X := h
  exact regular_doubleBraiding_eq_degreeTranslation F B g M.X hx

/-- Every actual neutral module is local, derived from its actual degree. -/
theorem regular_degreeZero_local (M : Modules F)
    (hM : Homogeneous (regularDegreeCharacter F B hR) 0 M) : IsLocalModule M := by
  rw [isLocalModule_iff, regular_module_monodromy F B hR 0 M hM]
  have ht : (degreeTranslationIso F 0).hom = 𝟙 (regularAlgebra F) := by
    change F.map (Representation.rightTranslation (1 : RepresentationZ2.H)) = _
    rw [Representation.rightTranslation_one, F.map_id]
    rfl
  rw [ht, id_whiskerRight, Category.id_comp]

/-- The actual crossed map for a homogeneous second module. -/
def crossedBraidingOfDegree (g : ZMod 2) (M N : Modules F)
    (hN : Homogeneous (regularDegreeCharacter F B hR) g N) :
    M ⊗ N ⟶ N ⊗ (Mod_.comap (degreeTranslationIso F g).hom).obj M :=
  translatedBraidingHom (degreeTranslationIso F g) M N
    (regular_module_monodromy F B hR g N hN)

/-- The neutral-factor crossed hexagon now has only actual homogeneous
inputs; all balancing and monodromy conditions are theorems. -/
theorem crossedBraidingOfDegree_hexagon (g : ZMod 2) (X Z N : Modules F)
    (hZ : Homogeneous (regularDegreeCharacter F B hR) 0 Z)
    (hN : Homogeneous (regularDegreeCharacter F B hR) g N) :
    crossedBraidingOfDegree F B hR g X (Z ⊗ N)
        (by simpa only [zero_add] using homogeneous_tensor (χ := regularDegreeCharacter F B hR) hZ hN) =
      (α_ X Z N).inv ≫
        (localBraidingHom X Z (regular_degreeZero_local F B hR Z hZ) ▷ N) ≫
          (α_ Z X N).hom ≫ (Z ◁ crossedBraidingOfDegree F B hR g X N hN) ≫
            (α_ Z N ((Mod_.comap (degreeTranslationIso F g).hom).obj X)).inv :=
  translatedBraiding_hexagon (degreeTranslationIso F g) X Z N
    (regular_degreeZero_local F B hR Z hZ) _ _

end Paper18.Category.FixedBoundary
