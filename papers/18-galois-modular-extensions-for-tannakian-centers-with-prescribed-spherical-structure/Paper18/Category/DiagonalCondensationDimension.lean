import Paper18.Category.DiagonalCondensationDimensionBasic
import Paper18.Category.DiagonalCondensationDimensionCentralizer
import Paper18.Category.DiagonalCondensationEmbeddingFactors

/-! # The actual case-2 diagonal-condensation centralizer dimension -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators MonObj
universe v u w v' u' w' vE uE wE vB uB wB
namespace Paper18.Category.DiagonalCondensation
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory D] [BraidedCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  [HasKernels (DeligneProduct C D)] [Simple (𝟙_ (DeligneProduct C D))]
  [HasCoequalizers (DeligneProduct C D)]
  {E : Type uE} [Category.{vE} E] [Preadditive E] [Linear ℂ E]
  [HasKernels E] [HasFiniteBiproducts E]
  [∀ X Y : E, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalLinear ℂ E]
  [RightRigidCategory E] [Simple (𝟙_ E)]
  {ν : Type wE} [Fintype ν] (U : FiniteSemisimpleSkeleton E ν)
  (F : E ⥤ C) [F.Additive] [F.Monoidal]
  (G : E ⥤ D) [G.Additive] [G.Monoidal]
  {A : DeligneProduct C D} [MonObj A] [IsCommMonObj A]
  (e : A ≅ ⨁ fun i => pair (F.obj (U.simpleObject i))
    (G.obj (dual E (U.simpleObject i))))
  (R : SeparableAlgebra A)
  {B : Type uB} [Category.{vB} B] [Preadditive B] [Linear ℂ B]
  [HasKernels B] [HasFiniteBiproducts B]
  [∀ X Y : B, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalLinear ℂ B]
  [RightRigidCategory B] [Simple (𝟙_ B)]
  {ζ : Type wB} [Fintype ζ] (V : FiniteSemisimpleSkeleton B ζ)

include e in
/-- The actual diagonal local category has the product ambient dimension
normalized by the square of the shared category's actual total dimension. -/
lemma diagonalLocalTotalFPdim (P : ModuleBalancing.MultiplicationPairing A)
    (J : PivotalStructure (DeligneProduct C D))
    (hA : (J.twistIso A).hom = 𝟙 A)
    (hconnected : Module.finrank ℂ (𝟙_ (DeligneProduct C D) ⟶ A) = 1)
    (hW : IsNondegenerate (C := DeligneProduct C D)) :
    R.localTotalFPdim (DeligneProduct.skeleton S T) hconnected =
      (S.fusionBasis.totalFPdim * T.fusionBasis.totalFPdim) / U.fusionBasis.totalFPdim ^ 2 := by
  rw [R.localTotalFPdim_eq_div (DeligneProduct.skeleton S T) P J hA hconnected hW,
    diagonal_fpdim S T U F G e, DeligneProduct.totalFPdim_product]

include e in
/-- The actual centralizer of a fully faithful local image has the
case-2 dimension, computed solely from the actual diagonal isomorphism,
actual module condensation, and actual fusion-subcategory product law. -/
lemma diagonalLocalCentralizerFPdim (H : B ⥤ LocalModules A)
    [H.Additive] [H.Monoidal] [H.Linear ℂ] [H.Full] [H.Faithful]
    (P : ModuleBalancing.MultiplicationPairing A)
    (J : PivotalStructure (DeligneProduct C D))
    (hA : (J.twistIso A).hom = 𝟙 A)
    (hconnected : Module.finrank ℂ (𝟙_ (DeligneProduct C D) ⟶ A) = 1)
    (hW : IsNondegenerate (C := DeligneProduct C D)) :
    localCentralizerFPdim R (DeligneProduct.skeleton S T) hconnected H =
      (S.fusionBasis.totalFPdim * T.fusionBasis.totalFPdim) /
        (V.fusionBasis.totalFPdim * U.fusionBasis.totalFPdim ^ 2) := by
  rw [localCentralizerFPdim_eq_div R (DeligneProduct.skeleton S T) V H P J hA hconnected hW,
    diagonal_fpdim S T U F G e, DeligneProduct.totalFPdim_product]

variable [F.Full] [F.Faithful] [F.Linear ℂ] [G.Full] [G.Faithful] [G.Linear ℂ]
  [BraidedCategory B]
  (H : B ⥤ C) [H.Braided] [H.Additive] [H.Linear ℂ] [H.Full] [H.Faithful]
  (hH : ∀ X i, Centralizes (F.obj (U.simpleObject i)) (H.obj X))

/-- For the actual local free embedding of the first factor, full
faithfulness is derived from the diagonal Hom computation. The resulting
centralizer dimension has no full-faithfulness or dimension certificate
as an additional input. -/
lemma leftLocalCentralizerFPdim
    (P : ModuleBalancing.MultiplicationPairing A)
    (J : PivotalStructure (DeligneProduct C D))
    (hA : (J.twistIso A).hom = 𝟙 A)
    (hconnected : Module.finrank ℂ (𝟙_ (DeligneProduct C D) ⟶ A) = 1)
    (hW : IsNondegenerate (C := DeligneProduct C D)) :
    localCentralizerFPdim R (DeligneProduct.skeleton S T) hconnected
      (leftLocalFunctor (fun i => F.obj (U.simpleObject i))
        (fun i => G.obj (dual E (U.simpleObject i))) e H hH) =
      (S.fusionBasis.totalFPdim * T.fusionBasis.totalFPdim) /
        (V.fusionBasis.totalFPdim * U.fusionBasis.totalFPdim ^ 2) := by
  let ff := leftLocalFunctorFullyFaithful (fun i => F.obj (U.simpleObject i))
    (fun i => G.obj (dual E (U.simpleObject i))) e H hH
    (leftFreeFunctorFullyFaithful U F G e S)
  letI := ff.full
  letI := ff.faithful
  exact diagonalLocalCentralizerFPdim S T U F G e R V
    (leftLocalFunctor (fun i => F.obj (U.simpleObject i))
      (fun i => G.obj (dual E (U.simpleObject i))) e H hH) P J hA hconnected hW

end Paper18.Category.DiagonalCondensation
