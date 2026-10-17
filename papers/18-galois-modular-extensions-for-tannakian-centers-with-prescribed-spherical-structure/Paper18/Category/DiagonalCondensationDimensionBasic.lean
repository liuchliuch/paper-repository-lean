import Paper18.Category.DiagonalCondensationEmbeddingBasic
import Paper18.Category.DeligneProductEmbedding
import Paper18.Category.FactorizationEssentialSurjectiveProduct

/-! # Actual FP dimensions from the genuine diagonal decomposition -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u w v' u' w' vE uE wE
namespace Paper18.Category.DiagonalCondensation
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  [HasKernels (DeligneProduct C D)] [Simple (𝟙_ (DeligneProduct C D))]

/-- Actual external pairs have product FP dimension, derived from the
two actual strong unit-factor embeddings and their actual tensor iso. -/
lemma fpdim_externalPair (X : C) (Y : D) :
    (DeligneProduct.skeleton S T).fpdim (pair X Y) = S.fpdim X * T.fpdim Y := by
  let W := DeligneProduct.skeleton S T
  erw [← W.fpdim_iso (DeligneProduct.leftTensorRightIso X Y), W.fpdim_tensor,
    S.fpdim_map W (DeligneProduct.left (D := D)) X,
    T.fpdim_map W (DeligneProduct.right (C := C)) Y]

variable {E : Type uE} [Category.{vE} E] [Preadditive E] [Linear ℂ E]
  [HasKernels E] [HasFiniteBiproducts E]
  [∀ X Y : E, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalLinear ℂ E]
  [RightRigidCategory E] [Simple (𝟙_ E)]
  {ν : Type wE} [Fintype ν] (U : FiniteSemisimpleSkeleton E ν)
  (F : E ⥤ C) [F.Additive] [F.Monoidal]
  (G : E ⥤ D) [G.Additive] [G.Monoidal]

/-- The actual diagonal algebra has FP dimension equal to the shared
category's total FP dimension. Its genuine biproduct isomorphism is the
only algebra-object input; actual tensor functors preserve each summand's
FP dimension. -/
lemma diagonal_fpdim {A : DeligneProduct C D}
    (e : A ≅ ⨁ fun i => pair (F.obj (U.simpleObject i))
      (G.obj (dual E (U.simpleObject i)))) :
    (DeligneProduct.skeleton S T).fpdim A = U.fusionBasis.totalFPdim := by
  let W := DeligneProduct.skeleton S T
  have hd (i : ν) : U.fpdim (dual E (U.simpleObject i)) = U.fusionBasis.fpdim i := by
    rw [← U.fpdim_iso (U.dualIso i), U.fpdim_simple]
    exact U.fusionBasis.fpdim_dual i
  rw [W.fpdim_iso e, W.fpdim_biproduct]
  dsimp only [W]
  simp_rw [fpdim_externalPair S T, U.fpdim_map S F, U.fpdim_map T G,
    U.fpdim_simple, hd]
  exact Finset.sum_congr rfl (fun i _ => (pow_two _).symm)

end Paper18.Category.DiagonalCondensation
