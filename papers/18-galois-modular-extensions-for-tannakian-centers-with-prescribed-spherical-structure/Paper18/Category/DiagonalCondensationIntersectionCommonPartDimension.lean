import Paper18.Category.DiagonalCondensationIntersectionCentralizer
import Paper18.Category.RelativeTensorCentralDimensionBasic
import Paper18.Category.RelativeTensorLinear
import Paper18.Category.LocalModulesSemisimple

/-! # The actual dimension of the shared local intersection -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators TensorProduct MonObj
universe v u v' u' vE uE w wC wD wM wL
namespace Paper18.Category.DiagonalCondensation
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] [BraidedCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [BraidedCategory D] [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {E : Type uE} [Category.{vE} E] [Preadditive E] [Linear ℂ E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalLinear ℂ E] [BraidedCategory E]
  [RightRigidCategory E] [HasKernels E] [HasFiniteBiproducts E]
  [∀ X Y : E, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ E)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton E ι)
  (F : E ⥤ C) [F.Braided] [F.Full] [F.Faithful] [F.Additive] [F.Linear ℂ]
  (G : E ⥤ D) [G.Monoidal] [G.Full] [G.Faithful] [G.Additive] [G.Linear ℂ]


variable [HasKernels C] [HasFiniteBiproducts C]
  {κ : Type wC} [Fintype κ] (T : FiniteSemisimpleSkeleton C κ)
  [HasKernels D] [HasFiniteBiproducts D]
  {ν : Type wD} [Fintype ν] (U : FiniteSemisimpleSkeleton D ν)
  {A : DeligneProduct C D} [MonObj A]
  (e : A ≅ ⨁ fun i => pair (F.obj (S.simpleObject i))
    (G.obj (dual E (S.simpleObject i))))


variable {ζ : Type wM} [Fintype ζ]
  (K : FiniteSemisimpleSkeleton (Mod_ (DeligneProduct C D) A) ζ)


variable (P : ObjectProperty C) [IsAdditiveFullProperty P]

variable [P.IsMonoidal] [IsCommMonObj A]
  [RightRigidCategory (DeligneProduct C D)] [HasCoequalizers (DeligneProduct C D)]
  (hP : ∀ X : P.FullSubcategory, ∀ i,
    Centralizes (F.obj (S.simpleObject i)) X.obj)
  (hG : ∀ X Y : E, Centralizes X Y → Centralizes (G.obj X) (G.obj Y))


variable [HasKernels (LocalModules A)] [RightRigidCategory (LocalModules A)]
  [Simple (𝟙_ (LocalModules A))]
  {ζL : Type wL} [Fintype ζL] (SM : FiniteSemisimpleSkeleton (LocalModules A) ζL)

include T U e K hG in
/-- The actual mixed-Hom intersection theorem identifies its support FP
dimension with the support FP dimension of the actual first common part.
The fully faithful tensor-image formula and the constructed inherited
fusion skeleton supply the dimension equality. -/
theorem commonPart_supportFPdim_intersection :
    SM.supportFPdim (fun M =>
      (restrictedLeftLocal S F G e P hP).essImage M ∧
        (restrictedRightLocal S F G e (secondCentralizer G)
          (secondCentralizer_local_condition S G)).essImage M) =
      S.supportFPdim (commonPartProperty F P) := by
  let R := commonPartProperty F P
  let H := commonPartLocal S F G e P hP
  letI := S.fullSubcategoryHasKernels R
  letI := S.fullSubcategoryRightRigid R
  letI := S.fullSubcategorySimpleUnit R
  let SR := S.fullSubcategorySkeleton R
  letI := (commonPartLocalFullyFaithful S F G T e P hP).full
  letI := (commonPartLocalFullyFaithful S F G T e P hP).faithful
  have he : (fun M =>
      (restrictedLeftLocal S F G e P hP).essImage M ∧
        (restrictedRightLocal S F G e (secondCentralizer G)
          (secondCentralizer_local_condition S G)).essImage M) = H.essImage := by
    funext M
    exact propext (centralizerLocalImages_intersection S F G T U e K P hP hG M)
  rw [he, RelativeTensor.supportFPdim_essImage SR SM H]
  exact S.fullSubcategory_totalFPdim_eq R

end Paper18.Category.DiagonalCondensation
