import Paper18.Category.FixedBoundaryBosonGrading
import Paper18.Category.SignKernelDimensions
import Paper18.Category.TannakianC2GeneratorBasic
import Paper18.Category.FactorizationEssentialSurjectiveBasic
import Paper18.Category.FusionSubcategoryFunctor

/-! # Minimal FP dimension gives the actual boson centralizer

The genuine monodromy kernel has index two. The actual boundary embedding
lands in this kernel, and equality of actual FP dimensions makes that
fully faithful tensor functor essentially surjective. No pivotal structure
on the ambient extension is used.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category.FixedBoundary
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalPreadditive A] [MonoidalLinear ℂ A]
  [HasKernels A] [HasFiniteBiproducts A] [RightRigidCategory A] [Simple (𝟙_ A)]
  [∀ X Y : A, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (SA : FiniteSemisimpleSkeleton A ι)
  (TC : TannakianCenter A RepresentationZ2.H)
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [HasKernels N] [HasFiniteBiproducts N] [RightRigidCategory N] [Simple (𝟙_ N)]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w'} [Fintype κ] (SN : FiniteSemisimpleSkeleton N κ)
  (i : A ⥤ N) [i.Braided] [i.Full] [i.Faithful] [i.Additive] [i.Linear ℂ]

/-- Minimal actual FP dimension identifies the actual boundary image with
the full actual centralizer of the specified C₂ generator. -/
theorem centralizer_of_minimal_fpdim
    (hN : IsNondegenerate (C := N))
    (hminimal : SN.fusionBasis.totalFPdim = 2 * SA.fusionBasis.totalFPdim) :
    ∀ Y : N, Centralizes (i.obj TC.c2Generator) Y →
      ∃ X : A, Nonempty (i.obj X ≅ Y) := by
  let B := TC.c2GeneratorTensorInverse.map i
  let chi := B.monodromyCharacter
  have hchi : ∀ X : N, chi.hom.app X ≫ chi.hom.app X = 𝟙 X :=
    B.monodromy_involutive_of_square (TensorInverse.mapSquare i TC.c2GeneratorSquareIso)
  have hn : ¬ Nonempty (i.obj TC.c2Generator ≅ 𝟙_ N) := by
    rintro ⟨q⟩
    exact TC.c2Generator_nonunit ⟨i.preimageIso (q ≪≫ Functor.Monoidal.εIso i)⟩
  have hne : chi ≠ Iso.refl (𝟭 N) := B.monodromy_nontrivial SN hN hn
  have hw : ∃ W : N, chi.hom.app W ≠ 𝟙 W := by
    by_contra h
    push_neg at h
    apply hne
    ext W
    exact h W
  obtain ⟨W, hW⟩ := hw
  have hi : ∀ X : A, SignKernel.positiveProperty chi (i.obj X) := fun X =>
    (B.monodromy_neutral_iff (i.obj X)).mpr ((TC.c2Generator_centralizes X).map i)
  let L := fullSubcategoryLift (SignKernel.positiveProperty chi) i hi
  letI := SignKernel.hasKernels chi SN
  letI := SignKernel.rightRigid chi SN
  letI := SignKernel.simpleUnit chi SN
  let SP := SignKernel.skeleton chi SN
  have hd : SA.fusionBasis.totalFPdim = SP.fusionBasis.totalFPdim := by
    have hh := SignKernel.totalFPdim_indexTwo_of_nontrivial SN chi hchi W hW
    change SN.fusionBasis.totalFPdim = 2 * SP.fusionBasis.totalFPdim at hh
    linarith
  letI : L.EssSurj := SA.essSurjOfTotalFPdimEq SP L hd
  intro Y hY
  let Z : SignKernel.Positive chi := ⟨Y, (B.monodromy_neutral_iff Y).mpr hY⟩
  refine ⟨L.objPreimage Z, ⟨?_⟩⟩
  exact (SignKernel.inclusion chi).mapIso (L.objObjPreimageIso Z)

end Paper18.Category.FixedBoundary
