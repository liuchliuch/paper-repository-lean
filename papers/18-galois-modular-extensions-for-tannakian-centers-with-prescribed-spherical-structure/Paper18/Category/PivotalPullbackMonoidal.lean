import Paper18.Category.PivotalPullback
import Paper18.Category.PivotalFunctorTensor

/-! # Actual pivotal pullback without a braiding assumption

The canonical strong-monoidal double-dual comparison is available for an
arbitrary strong monoidal functor. Full faithfulness therefore pulls back
an actual pivotal structure with its complete unit and tensor coherence.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor CategoryTheory.Functor.LaxMonoidal
universe v u v' u'
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [RightRigidCategory D]
  (F : C ⥤ D) [F.Monoidal] [F.Full] [F.Faithful] (J : PivotalStructure D)

/-- The actual bidual comparison identifying the image of the source
identity functor with the image of its canonical double dual. -/
def pivotalPullbackMonoidalImageIso : 𝟭 C ⋙ F ≅ doubleDualFunctor C ⋙ F :=
  Functor.leftUnitor F ≪≫ (Functor.rightUnitor F).symm ≪≫
    isoWhiskerLeft F J.j ≪≫ (doubleDualComparisonNatIso F).symm

instance pivotalPullbackMonoidalImageIso_isMonoidal :
    NatTrans.IsMonoidal (pivotalPullbackMonoidalImageIso F J).hom := by
  letI : NatTrans.IsMonoidal (isoWhiskerLeft F J.j).hom := by
    change NatTrans.IsMonoidal (Functor.whiskerLeft F J.j.hom)
    rw [← Functor.id_hcomp]
    infer_instance
  dsimp only [pivotalPullbackMonoidalImageIso, Iso.trans_hom, Iso.symm_hom]
  infer_instance

/-- Actual fullness supplies the pivotal components in the source;
faithfulness supplies naturality and the inverse equations. -/
def pivotalPullbackMonoidalNatIso : 𝟭 C ≅ doubleDualFunctor C :=
  fullyFaithfulCancelRight F (pivotalPullbackMonoidalImageIso F J)

instance pivotalPullbackMonoidalNatIso_isMonoidal :
    NatTrans.IsMonoidal (pivotalPullbackMonoidalNatIso F J).hom :=
  fullyFaithfulCancelRight_monoidal F (pivotalPullbackMonoidalImageIso F J)

/-- Pullback of an actual pivotal structure along any fully faithful strong
monoidal functor, using its canonical chosen-dual comparison. -/
def pivotalPullbackMonoidal : PivotalStructure C where
  j := pivotalPullbackMonoidalNatIso F J
  unit := by
    simpa only [Functor.LaxMonoidal.id_ε, canonicalDoubleDual_unit, Category.id_comp] using
      (NatTrans.IsMonoidal.unit (τ := (pivotalPullbackMonoidalNatIso F J).hom))
  tensor X Y := by
    simpa only [Functor.LaxMonoidal.id_μ, canonicalDoubleDual_tensor, Category.id_comp] using
      (NatTrans.IsMonoidal.tensor (τ := (pivotalPullbackMonoidalNatIso F J).hom) X Y)

/-- The pullback functor preserves the actual prescribed pivotal structure. -/
lemma pivotalPullbackMonoidal_preserves :
    PreservesPivotal F (pivotalPullbackMonoidal F J) J := by
  intro X
  change F.map (F.preimage ((pivotalPullbackMonoidalImageIso F J).hom.app X)) ≫
    (doubleDualComparison F X).hom = J.j.hom.app (F.obj X)
  rw [F.map_preimage]
  simp [pivotalPullbackMonoidalImageIso, doubleDualComparisonNatIso]

/-- Actual sphericality restricts along the fully faithful strong monoidal
functor, without any source or target braiding. -/
lemma pivotalPullbackMonoidal_spherical (hJ : J.Spherical) :
    (pivotalPullbackMonoidal F J).Spherical :=
  (pivotalPullbackMonoidal_preserves F J).spherical_of_faithful hJ

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
/-- The actual positive trace pulls back to the actual positive trace.
Simplicity of image objects follows from actual full faithfulness. -/
lemma pivotalPullbackMonoidal_positive (hJ : J.Positive) :
    (pivotalPullbackMonoidal F J).Positive := by
  intro X hX
  letI := hX
  letI := T.simple_map F X
  rw [← (pivotalPullbackMonoidal_preserves F J).rightDim_scalar X]
  exact hJ _ inferInstance

end Positive
end Paper18.Category
