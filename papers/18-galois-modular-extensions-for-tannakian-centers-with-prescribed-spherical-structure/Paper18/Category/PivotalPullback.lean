import Paper18.Category.SphericalizationFunctorCoherence
import Paper18.Category.ModuleBalancingPositive
import Paper18.Category.FunctorImage

/-! # Actual pivotal pullback along fully faithful braided tensor functors -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor CategoryTheory.Functor.LaxMonoidal
universe v u v' u'
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual

section Cancel
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] [F.Full] [F.Faithful]
  {G H : C ⥤ C} [G.Monoidal] [H.Monoidal]
  (q : G ⋙ F ≅ H ⋙ F) [NatTrans.IsMonoidal q.hom]

lemma fullyFaithfulCancelRight_monoidal :
    NatTrans.IsMonoidal (fullyFaithfulCancelRight F q).hom := by
  let a := fullyFaithfulCancelRight F q
  have hm (X : C) : F.map (a.hom.app X) = q.hom.app X := F.map_preimage _
  change NatTrans.IsMonoidal a.hom
  constructor
  · apply F.map_injective
    apply (cancel_epi (ε F)).mp
    have h := NatTrans.IsMonoidal.unit (τ := q.hom)
    simpa only [Functor.LaxMonoidal.comp_ε, F.map_comp, Category.assoc, hm] using h
  · intro X Y
    apply F.map_injective
    apply (cancel_epi (μ F (G.obj X) (G.obj Y))).mp
    have h := NatTrans.IsMonoidal.tensor (τ := q.hom) X Y
    simp only [Functor.LaxMonoidal.comp_μ] at h
    rw [← hm X, ← hm Y, Functor.LaxMonoidal.μ_natural_assoc] at h
    simpa only [F.map_comp, Category.assoc, hm] using h

end Cancel

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D]
  (F : C ⥤ D) [F.Braided] [F.Full] [F.Faithful] (J : PivotalStructure D)

def pivotalPullbackImageIso : 𝟭 C ⋙ F ≅ doubleDualFunctor C ⋙ F :=
  Functor.leftUnitor F ≪≫ (Functor.rightUnitor F).symm ≪≫
    isoWhiskerLeft F J.j ≪≫ (doubleDualComparisonNatIso F).symm

instance pivotalPullbackImageIso_monoidal :
    NatTrans.IsMonoidal (pivotalPullbackImageIso F J).hom := by
  letI : NatTrans.IsMonoidal (isoWhiskerLeft F J.j).hom := by
    change NatTrans.IsMonoidal (Functor.whiskerLeft F J.j.hom)
    rw [← Functor.id_hcomp]
    infer_instance
  dsimp only [pivotalPullbackImageIso, Iso.trans_hom, Iso.symm_hom]
  infer_instance

def pivotalPullbackNatIso : 𝟭 C ≅ doubleDualFunctor C :=
  fullyFaithfulCancelRight F (pivotalPullbackImageIso F J)

instance pivotalPullbackNatIso_monoidal :
    NatTrans.IsMonoidal (pivotalPullbackNatIso F J).hom :=
  fullyFaithfulCancelRight_monoidal F (pivotalPullbackImageIso F J)

/-- The pivotal structure on the full braided tensor subcategory is
recovered by actual inverse maps on Hom, with canonical chosen-dual coherence. -/
def pivotalPullback : PivotalStructure C where
  j := pivotalPullbackNatIso F J
  unit := by
    simpa only [Functor.LaxMonoidal.id_ε, canonicalDoubleDual_unit, Category.id_comp] using
      (NatTrans.IsMonoidal.unit (τ := (pivotalPullbackNatIso F J).hom))
  tensor X Y := by
    simpa only [Functor.LaxMonoidal.id_μ, canonicalDoubleDual_tensor, Category.id_comp] using
      (NatTrans.IsMonoidal.tensor (τ := (pivotalPullbackNatIso F J).hom) X Y)

lemma pivotalPullback_preserves : PreservesPivotal F (pivotalPullback F J) J := by
  intro X
  change F.map (F.preimage ((pivotalPullbackImageIso F J).hom.app X)) ≫
    (doubleDualComparison F X).hom = J.j.hom.app (F.obj X)
  rw [F.map_preimage]
  simp [pivotalPullbackImageIso, doubleDualComparisonNatIso]

section Positive
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [CategoryTheory.Limits.HasKernels C] [CategoryTheory.Limits.HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [CategoryTheory.Limits.HasKernels D] [CategoryTheory.Limits.HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  [F.Additive] [F.Linear ℂ]
  {κ : Type*} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)

include T in
lemma pivotalPullback_positive (hJ : J.Positive) : (pivotalPullback F J).Positive := by
  intro X hX
  letI := hX
  letI := T.simple_map F X
  rw [← (pivotalPullback_preserves F J).rightDim_scalar X]
  exact hJ _ inferInstance

end Positive
end Paper18.Category
