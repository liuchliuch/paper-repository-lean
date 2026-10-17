import Paper18.Category.NondegenerateBraidedFunctorProjection
import Paper18.Category.Braided

/-! # Braidedness forces the actual right-adjoint unit to be transparent -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe v u v' u'
namespace Paper18.Category.NondegenerateBraidedFunctor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  (F : C ⥤ D) [F.Braided] {R : D ⥤ C} (adj : F ⊣ R)

/-- The actual right-adjoint object at the target unit. -/
def adjointUnit {F : C ⥤ D} (_adj : F ⊣ R) : C := R.obj (𝟙_ D)

/-- The actual left projection formula with its terminal unitor. -/
def unitProjection (X : C) : X ⊗ adjointUnit adj ⟶ R.obj (F.obj X) :=
  projection F adj X (𝟙_ D) ≫ R.map (ρ_ (F.obj X)).hom

@[reassoc]
lemma unitProjection_counit (X : C) :
    F.map (unitProjection F adj X) ≫ adj.counit.app (F.obj X) =
      δ F X (adjointUnit adj) ≫ (F.obj X ◁ adj.counit.app (𝟙_ D)) ≫
        (ρ_ (F.obj X)).hom := by
  simp only [unitProjection, F.map_comp, Category.assoc]
  have hn := adj.counit.naturality (ρ_ (F.obj X)).hom
  change F.map (R.map (ρ_ (F.obj X)).hom) ≫ adj.counit.app (F.obj X) =
    adj.counit.app (F.obj X ⊗ 𝟙_ D) ≫ (ρ_ (F.obj X)).hom at hn
  rw [hn, projection_counit_assoc]
  rfl

/-- The other projection mate, before using either actual braiding. -/
def unitProjectionRight (X : C) : adjointUnit adj ⊗ X ⟶ R.obj (F.obj X) :=
  adj.homEquiv _ _ (δ F (adjointUnit adj) X ≫
    (adj.counit.app (𝟙_ D) ▷ F.obj X) ≫ (λ_ (F.obj X)).hom)

@[reassoc]
lemma unitProjectionRight_counit (X : C) :
    F.map (unitProjectionRight F adj X) ≫ adj.counit.app (F.obj X) =
      δ F (adjointUnit adj) X ≫ (adj.counit.app (𝟙_ D) ▷ F.obj X) ≫
        (λ_ (F.obj X)).hom :=
  (adj.homEquiv _ _).symm_apply_apply _

/-- The first actual crossing intertwines the two genuine projection mates. -/
lemma braiding_unitProjectionRight (X : C) :
    (β_ X (adjointUnit adj)).hom ≫ unitProjectionRight F adj X =
      unitProjection F adj X := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, F.map_comp, Category.assoc]
  rw [unitProjectionRight_counit, unitProjection_counit, F.map_braiding]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
  rw [← braiding_naturality_right_assoc]
  simp only [Functor.id_obj, braiding_tensorUnit_right, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Braidedness also supplies the opposite crossing, with the same actual
mates. This is the additional constraint behind transparency. -/
lemma braiding_unitProjection (X : C) :
    (β_ (adjointUnit adj) X).hom ≫ unitProjection F adj X =
      unitProjectionRight F adj X := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, F.map_comp, Category.assoc]
  rw [unitProjection_counit, unitProjectionRight_counit, F.map_braiding]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
  rw [← braiding_naturality_left_assoc]
  simp only [Functor.id_obj, braiding_tensorUnit_left, Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable [RightRigidCategory C]
attribute [local instance 2000] RightRigidCategory.rightDual

/-- The genuine projection formula is invertible by source rigidity. -/
instance unitProjection_isIso (X : C) : IsIso (unitProjection F adj X) := by
  letI := projection_isIso F adj X (dual C X) (𝟙_ D)
  dsimp only [unitProjection]
  infer_instance

/-- The actual object R(1) lies in the actual Müger center. No
transparency or right-adjoint-unit assertion is supplied as data. -/
theorem adjointUnit_transparent : adjointUnit adj ∈ mugerCenter := by
  intro X _
  apply (centralizes_comm X (adjointUnit adj)).mp
  change (β_ X (adjointUnit adj)).hom ≫ (β_ (adjointUnit adj) X).hom = 𝟙 _
  apply (cancel_mono (unitProjection F adj X)).mp
  rw [Category.assoc, braiding_unitProjection, braiding_unitProjectionRight, Category.id_comp]

end Paper18.Category.NondegenerateBraidedFunctor
