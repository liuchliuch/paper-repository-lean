import Paper18.Category.PivotalFunctorTensor

/-! # Canonical dual comparison of the actual identity tensor functor -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category
universe v u
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The identity tensor functor's actual dual comparison is the identity,
as follows from the actual evaluation characterization. -/
@[simp] lemma dualComparison_identity (X : C) :
    dualComparison (𝟭 C) X = Iso.refl (dual C X) := by
  apply Iso.ext
  apply pairing_hom_ext (inferInstanceAs (ExactPairing X (dual C X)))
  have h := dualComparison_evaluation (𝟭 C) X
  change (dualComparison (𝟭 C) X).hom ▷ X ≫ ε_ X (dual C X) =
    (𝟙 (dual C X)) ▷ X ≫ ε_ X (dual C X)
  erw [id_whiskerRight, id_comp]
  simpa only [Functor.id_obj, Functor.LaxMonoidal.id_μ, Functor.id_map,
    Functor.OplaxMonoidal.id_η, id_comp, comp_id] using h

/-- Its canonical double-dual comparison is likewise the identity. -/
@[simp] lemma doubleDualComparison_identity (X : C) :
    doubleDualComparison (𝟭 C) X = Iso.refl ((doubleDualFunctor C).obj X) := by
  apply Iso.ext
  simp [doubleDualComparison, dualMapIso, dualMap]
  rfl

/-- The actual identity strong monoidal functor preserves every actual
pivotal structure through the canonical chosen-dual comparison. -/
theorem preservesPivotal_identity (J : PivotalStructure C) :
    PreservesPivotal (𝟭 C) J J := by
  intro X
  change J.j.hom.app X ≫ (doubleDualComparison (𝟭 C) X).hom = J.j.hom.app X
  rw [doubleDualComparison_identity]
  exact comp_id _

end Paper18.Category
