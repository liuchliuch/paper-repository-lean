import Paper18.Category.FixedBoundaryBasic
import Paper18.Category.SphericalizationFunctorCoherence
import Paper18.Category.SphericalizationAction

/-! # Extending the actual pivotal structure from a fixed boundary

The boundary comparison includes the canonical double-dual comparison of the
embedding. A trivialization of this actual fixed-boundary pair supplies a
coherent pivotal structure with the specified restriction.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor
open CategoryTheory.Functor.LaxMonoidal
universe v u v' u'
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  (F : C ⥤ D) [F.Braided] (J : PivotalStructure C)

/-- Double dualization is an actual equivalence, independently of any
pivotal structure on the ambient category. -/
def braidedDoubleDualEquivalence : D ≌ D :=
  CategoryTheory.Equivalence.mk (doubleDualFunctor D) (doubleDualFunctor D)
    (braidedFourDualNatIso (C := D)) (braidedFourDualNatIso (C := D)).symm

/-- The prescribed pivotal boundary, with the canonical chosen-dual
identification retained. -/
def pivotalBoundaryIso : F ⋙ doubleDualFunctor D ≅ F :=
  ((Functor.leftUnitor F).symm ≪≫ isoWhiskerRight J.j F ≪≫
    doubleDualComparisonNatIso F).symm

instance pivotalBoundaryIso_monoidal : NatTrans.IsMonoidal (pivotalBoundaryIso F J).hom := by
  letI : NatTrans.IsMonoidal (isoWhiskerRight J.j F).hom := by
    change NatTrans.IsMonoidal (Functor.whiskerRight J.j.hom F)
    rw [← Functor.hcomp_id]
    infer_instance
  change NatTrans.IsMonoidal (((doubleDualComparisonNatIso F).inv ≫
    (isoWhiskerRight J.j F).inv) ≫ (Functor.leftUnitor F).hom)
  infer_instance

@[simp] lemma pivotalBoundaryIso_hom (X : C) :
    (pivotalBoundaryIso F J).hom.app X =
      (doubleDualComparison F X).inv ≫ F.map (J.j.inv.app X) := by
  simp [pivotalBoundaryIso, doubleDualComparisonNatIso]

/-- The actual double-dual autoequivalence with its specified pivotal
boundary comparison, an object of the fixed-boundary groupoid. -/
def pivotalBoundary : BoundaryAutoequivalence F where
  functor := doubleDualFunctor D
  equivalence := inferInstanceAs (braidedDoubleDualEquivalence (D := D)).functor.IsEquivalence
  boundary := pivotalBoundaryIso F J

/-- The inverse of the fixed-boundary trivialization is the actual
coherent pivotal identification in the ambient category. -/
def pivotalOfBoundaryTrivialization
    (b : BoundaryIso F (pivotalBoundary F J) (BoundaryAutoequivalence.identity F)) :
    PivotalStructure D := by
  letI : NatTrans.IsMonoidal b.iso.inv := inferInstance
  refine ⟨b.iso.symm, ?_, ?_⟩
  · have h := NatTrans.IsMonoidal.unit (τ := b.iso.inv)
    change ε (𝟭 D) ≫ b.iso.inv.app (𝟙_ D) = ε (doubleDualFunctor D) at h
    simpa only [Functor.LaxMonoidal.id_ε, canonicalDoubleDual_unit,
      Category.id_comp] using h
  · intro X Y
    have h := NatTrans.IsMonoidal.tensor (τ := b.iso.inv) X Y
    change μ (𝟭 D) X Y ≫ b.iso.inv.app (X ⊗ Y) =
      (b.iso.inv.app X ⊗ₘ b.iso.inv.app Y) ≫ μ (doubleDualFunctor D) X Y at h
    simpa only [Functor.LaxMonoidal.id_μ, canonicalDoubleDual_tensor,
      Category.id_comp] using h

/-- The recovered pivotal structure agrees with the specified one along
the actual embedding and its canonical double-dual comparison. -/
lemma pivotalOfBoundaryTrivialization_preserves
    (b : BoundaryIso F (pivotalBoundary F J) (BoundaryAutoequivalence.identity F)) :
    PreservesPivotal F J (pivotalOfBoundaryTrivialization F J b) := by
  intro X
  have hb := BoundaryIso.to_identity_boundary F b X
  change b.iso.hom.app (F.obj X) = (pivotalBoundaryIso F J).hom.app X at hb
  have he : b.iso.app (F.obj X) =
      (F.mapIso (J.j.app X) ≪≫ doubleDualComparison F X).symm := by
    apply Iso.ext
    exact hb.trans (pivotalBoundaryIso_hom F J X)
  exact (congrArg Iso.inv he).symm

end Paper18.Category
