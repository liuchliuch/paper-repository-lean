import Paper18.Category.SphericalizationCentralizerIntegralBasic
import Paper18.Category.SphericalizationEmbedding

/-! # Integral actual centralizers of prescribed lifts into sphericalization -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category.Sphericalized
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- The actual lifted centralizer is precisely the actual preimage of the
original centralizer under the actual faithful braided forgetful functor. -/
lemma centralizer_forget_iso_iff {B : Type u'} [Category.{v'} B]
    (F : B ⥤ C) (Fhat : B ⥤ Sphericalized C) (e : Fhat ⋙ forget ≅ F)
    (X : Sphericalized C) :
    X ∈ centralizer (Set.range Fhat.obj) ↔ forget.obj X ∈ centralizer (Set.range F.obj) :=
  centralizer_functor_comp_iso_iff forget F Fhat e X

/-- Integrality of an actual ambient centralizer implies integrality of the
actual centralizer of any actual sphericalization lift with the specified
forgetful comparison. -/
theorem centralizerIntegral_of_forget_iso {B : Type u'} [Category.{v'} B]
    (F : B ⥤ C) (Fhat : B ⥤ Sphericalized C) (e : Fhat ⋙ forget ≅ F)
    (hI : S.CentralizerIntegral (Set.range F.obj)) :
    (skeleton S).CentralizerIntegral (Set.range Fhat.obj) :=
  S.centralizerIntegral_of_comp_iso (skeleton S) forget F Fhat e hI

variable {B : Type u'} [Category.{v'} B] [MonoidalCategory B]
  [RightRigidCategory B] [BraidedCategory B]
  [Preadditive B] [Linear ℂ B] [MonoidalPreadditive B] [MonoidalLinear ℂ B]
  [HasKernels B] [HasFiniteBiproducts B] [Simple (𝟙_ B)]
  [∀ X Y : B, FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton B κ)
  (J : PivotalStructure B) (hJ : J.Spherical) (F : B ⥤ C) [F.Braided]

/-- In particular, the canonical actual prescribed spherical embedding has
an integral actual centralizer whenever the original image centralizer is integral. -/
theorem embedding_centralizerIntegral
    (hI : S.CentralizerIntegral (Set.range F.obj)) :
    (skeleton S).CentralizerIntegral (Set.range (embedding T J hJ F).obj) :=
  centralizerIntegral_of_forget_iso S F (embedding T J hJ F) (Iso.refl F) hI

end Paper18.Category.Sphericalized
