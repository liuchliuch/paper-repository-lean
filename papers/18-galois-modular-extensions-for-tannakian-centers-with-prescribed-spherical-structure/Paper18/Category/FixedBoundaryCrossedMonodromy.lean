import Paper18.Category.FixedBoundaryC2Regular
import Paper18.Category.FixedBoundaryGrading
import Paper18.Category.CentralizerClosure

/-!
# Actual regular-algebra monodromy equals the degree translation

The actual two equivariant character summands of Fun(C₂) jointly detect
morphisms after tensoring. Their actual translation eigenvalues and the
actual homogeneous monodromy identity identify double braiding of the
regular algebra with right translation by the degree.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.Monoidal
universe v u
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

private theorem resolution_whisker_hom_ext {R U V X Z : C}
    (p : R ⟶ U) (a : U ⟶ R) (q : R ⟶ V) (b : V ⟶ R)
    (hres : p ≫ a + q ≫ b = 𝟙 R) (f g : R ⊗ X ⟶ Z)
    (ha : (a ▷ X) ≫ f = (a ▷ X) ≫ g)
    (hb : (b ▷ X) ≫ f = (b ▷ X) ≫ g) : f = g := by
  have h := congrArg₂ (fun r s => r + s)
    (congrArg (fun k => (p ▷ X) ≫ k) ha)
    (congrArg (fun k => (q ▷ X) ≫ k) hb)
  simpa only [← Category.assoc, ← comp_whiskerRight, ← Preadditive.add_comp,
    ← MonoidalPreadditive.add_whiskerRight, hres, id_whiskerRight, Category.id_comp] using h

variable (F : FDRep ℂ RepresentationZ2.H ⥤ C) [F.Braided] [F.Additive] [F.Linear ℂ]
open Representation RepresentationZ2 C2Regular

/-- The actual regular algebra translation associated to an actual degree. -/
def degreeTranslation (g : ZMod 2) : F.obj (functions (G := H)) ⟶ F.obj functions :=
  F.map (rightTranslation (Multiplicative.ofAdd g))

private theorem mapped_resolution :
    F.map unitProjection ≫ F.map functionsOne + F.map signProjection ≫ F.map signInclusion =
      𝟙 (F.obj (functions (G := H))) := by
  rw [← F.map_comp, ← F.map_comp, ← F.map_add, C2Regular.resolution, F.map_id]

private theorem unit_degreeTranslation (g : ZMod 2) :
    F.map (functionsOne (G := H)) ≫ degreeTranslation F g = F.map functionsOne := by
  rcases Paper18.ZMod.two_eq_zero_or_one g with rfl | rfl
  · simp [degreeTranslation]
  · change F.map functionsOne ≫ F.map (rightTranslation generator) = _
    rw [← F.map_comp, C2Regular.unit_translation]

private theorem sign_degreeTranslation (g : ZMod 2) :
    F.map signInclusion ≫ degreeTranslation F g = paritySign g • F.map signInclusion := by
  rcases Paper18.ZMod.two_eq_zero_or_one g with rfl | rfl
  · simp [degreeTranslation]
  · change F.map signInclusion ≫ F.map (rightTranslation generator) = _
    rw [← F.map_comp, C2Regular.sign_translation]
    simp

/-- The actual balancing obstruction on a homogeneous object is exactly
regular translation by its actual degree. -/
theorem regular_doubleBraiding_eq_degreeTranslation
    (B : TensorInverse (F.obj signRep)) (g : ZMod 2) (X : C)
    (hX : Homogeneous B.monodromyCharacter g X) :
    (doubleBraiding (F.obj (functions (G := H))) X).hom = degreeTranslation F g ▷ X := by
  apply resolution_whisker_hom_ext
    (F.map unitProjection) (F.map functionsOne) (F.map signProjection)
    (F.map signInclusion) (mapped_resolution F)
  · have hu : Centralizes (F.obj (𝟙_ (FDRep ℂ H))) X :=
      (centralizes_unit_left X).of_iso_left (εIso F).symm
    rw [doubleBraiding_naturality_left, hu, Category.id_comp,
      ← comp_whiskerRight, unit_degreeTranslation]
  · have ht : (doubleBraiding (F.obj signRep) X).hom =
        paritySign g • 𝟙 ((F.obj signRep) ⊗ X) := by
      rw [← B.monodromyCharacter_spec, hX]
      simp
    rw [doubleBraiding_naturality_left, ht, ← comp_whiskerRight,
      sign_degreeTranslation]
    simp

end Paper18.Category.FixedBoundary
