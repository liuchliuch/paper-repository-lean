import Paper18.Category.FixedBoundaryBosonGrading

/-!
# Actual transport of the monodromy grading

A braided tensor functor intertwines the canonical monodromy characters
when its image of the invertible grading object is given an actual
isomorphism to the target grading object. In particular, a specified
boundary isomorphism on that object preserves every actual homogeneous
component.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory CategoryTheory.Limits
universe v u v' u'
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]

namespace TensorInverse
variable {T : C} (B : TensorInverse T) (F : C ⥤ D) [F.Braided]
  {U : D} (A : TensorInverse U) (e : F.obj T ≅ U)
include e

/-- The actual tensorator and the actual chosen object isomorphism
intertwine the fully faithful preimages defining both characters. -/
theorem map_monodromyCharacter (X : C) :
    F.map (B.monodromyCharacter.hom.app X) = A.monodromyCharacter.hom.app (F.obj X) := by
  have hF : F.obj T ◁ F.map (B.monodromyCharacter.hom.app X) =
      (doubleBraiding (F.obj T) (F.obj X)).hom := by
    apply (cancel_mono (Functor.LaxMonoidal.μ F T X)).mp
    calc
      _ = Functor.LaxMonoidal.μ F T X ≫ F.map (T ◁ B.monodromyCharacter.hom.app X) :=
        Functor.LaxMonoidal.μ_natural_right F T (B.monodromyCharacter.hom.app X)
      _ = Functor.LaxMonoidal.μ F T X ≫ F.map (doubleBraiding T X).hom := by
        rw [B.monodromyCharacter_spec]
      _ = _ := tensorator_map_doubleBraiding F T X
  have hU : U ◁ F.map (B.monodromyCharacter.hom.app X) =
      (doubleBraiding U (F.obj X)).hom := by
    apply (cancel_epi (e.hom ▷ F.obj X)).mp
    calc
      _ = (F.obj T ◁ F.map (B.monodromyCharacter.hom.app X)) ≫ e.hom ▷ F.obj X :=
        (whisker_exchange e.hom (F.map (B.monodromyCharacter.hom.app X))).symm
      _ = (doubleBraiding (F.obj T) (F.obj X)).hom ≫ e.hom ▷ F.obj X := by rw [hF]
      _ = _ := (doubleBraiding_naturality_left e.hom (F.obj X)).symm
  letI := A.tensorLeftIsEquivalence
  apply (tensorLeft U).map_injective
  change U ◁ F.map (B.monodromyCharacter.hom.app X) =
    U ◁ A.monodromyCharacter.hom.app (F.obj X)
  rw [A.monodromyCharacter_spec]
  exact hU

variable [Preadditive C] [Linear ℂ C] [Preadditive D] [Linear ℂ D] [F.Linear ℂ]

/-- A braided linear functor preserving the actual invertible grading
object maps the actual homogeneous subcategory into its stated degree. -/
theorem homogeneous_map {d : ZMod 2} {X : C}
    (hX : FixedBoundary.Homogeneous B.monodromyCharacter d X) :
    FixedBoundary.Homogeneous A.monodromyCharacter d (F.obj X) := by
  unfold FixedBoundary.Homogeneous at hX ⊢
  rw [← B.map_monodromyCharacter F A e, hX, Functor.map_smul]
  exact congrArg (fun f => FixedBoundary.paritySign d • f) (F.map_id X)

/-- Faithfulness also reflects the actual monodromy degree. -/
theorem homogeneous_map_iff [F.Faithful] (d : ZMod 2) (X : C) :
    FixedBoundary.Homogeneous A.monodromyCharacter d (F.obj X) ↔
      FixedBoundary.Homogeneous B.monodromyCharacter d X := by
  constructor
  · intro h
    unfold FixedBoundary.Homogeneous at h ⊢
    apply F.map_injective
    rw [Functor.map_smul]
    calc
      F.map (B.monodromyCharacter.hom.app X) = A.monodromyCharacter.hom.app (F.obj X) :=
        B.map_monodromyCharacter F A e X
      _ = FixedBoundary.paritySign d • 𝟙 (F.obj X) := h
      _ = FixedBoundary.paritySign d • F.map (𝟙 X) :=
        (congrArg (fun f => FixedBoundary.paritySign d • f) (F.map_id X)).symm
  · exact B.homogeneous_map F A e

/-- The ordinary restriction is a functor between the actual homogeneous
full subcategories; it is obtained from the original braided functor. -/
def homogeneousMapFunctor (d : ZMod 2) :
    FixedBoundary.HomogeneousCategory B.monodromyCharacter d ⥤
      FixedBoundary.HomogeneousCategory A.monodromyCharacter d where
  obj X := ⟨F.obj X.obj, B.homogeneous_map F A e X.property⟩
  map f := F.map f
  map_id X := F.map_id X.obj
  map_comp f g := F.map_comp f g

instance homogeneousMapFunctorFaithful [F.Faithful] (d : ZMod 2) :
    (B.homogeneousMapFunctor F A e d).Faithful where
  map_injective h := F.map_injective h

instance homogeneousMapFunctorFull [F.Full] [F.Faithful] (d : ZMod 2) :
    (B.homogeneousMapFunctor F A e d).Full where
  map_surjective f := ⟨F.preimage f, F.map_preimage f⟩

end TensorInverse
end Paper18.Category
