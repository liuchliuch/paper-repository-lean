import Paper18.Results.CategoricalCaseTwoCondensation
import Paper18.Category.PivotalProductMap

/-! # The actual spherical embedding into case-2 local modules -/
noncomputable section
set_option maxHeartbeats 2000000
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj
universe v u w vN uN wN vP uP wP vB uB
namespace Paper18.Category.CaseTwoCondensation
variable {E : Type u} [Category.{v} E] [Preadditive E] [Linear ℂ E]
  [MonoidalCategory E] [BraidedCategory E] [RightRigidCategory E]
  [MonoidalPreadditive E] [MonoidalLinear ℂ E]
  [HasKernels E] [HasFiniteBiproducts E]
  [∀ X Y : E, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ E)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton E ι)
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [bN : BraidedCategory N] [RightRigidCategory N]
  [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [HasKernels N] [HasFiniteBiproducts N]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ N)]
  {κ : Type wN} [Fintype κ] (T : FiniteSemisimpleSkeleton N κ)
  {P : Type uP} [Category.{vP} P] [Preadditive P] [Linear ℂ P]
  [MonoidalCategory P] [bP : BraidedCategory P] [RightRigidCategory P]
  [MonoidalPreadditive P] [MonoidalLinear ℂ P]
  [HasKernels P] [HasFiniteBiproducts P]
  [∀ X Y : P, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ P)]
  {ν : Type wP} [Fintype ν] (U : FiniteSemisimpleSkeleton P ν)
  (JE : PivotalStructure E) (JN : PivotalStructure N) (JP : PivotalStructure P)
  (F : BraidedSphericalEmbedding JE JN) (G : BraidedSphericalEmbedding JE JP)


local instance productBraidingEmbedding : BraidedCategory (DeligneProduct N P) :=
  DeligneProduct.reverseSecondBraiding N P
local instance algebraCommEmbedding : IsCommMonObj (algebra S JE JN JP F G) :=
  algebra_commutative S JE JN JP F G

variable [HasKernels (DeligneProduct N P)] [Simple (𝟙_ (DeligneProduct N P))]
  [HasCoequalizers (DeligneProduct N P)]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [Linear ℂ B]
  [MonoidalCategory B] [BraidedCategory B] [RightRigidCategory B]
  (JB : PivotalStructure B) (H : BraidedSphericalEmbedding JB JN)
  (hH : ∀ X i, Centralizes (F.functor.obj (S.simpleObject i)) (H.functor.obj X))

local instance productLeftBraided :
    (DeligneProduct.left (C := N) (D := P)).Braided := by
  letI : BraidedCategory P := reverseBraiding P
  infer_instance

/-- The given category embeds into the actual first Deligne factor. -/
abbrev productEmbeddingFunctor : B ⥤ DeligneProduct N P :=
  H.functor ⋙ DeligneProduct.left

include hH in
/-- Actual centralization with the shared category proves locality of its
actual free images against the actual diagonal algebra. -/
theorem productEmbedding_centralizes (X : B) :
    Centralizes (algebra S JE JN JP F G) ((productEmbeddingFunctor JN JB H).obj X) := by
  let f : ι → N := fun i => F.functor.obj (S.simpleObject i)
  let g : ι → P := fun i => G.functor.obj (dual E (S.simpleObject i))
  let e := DiagonalAlgebra.productCanonicalAlgebraIso S F.functor G.functor
  let HX := H.functor.obj X
  have hs := hH X
  letI : BraidedCategory P := reverseBraiding P
  exact DiagonalCondensation.centralizes_diagonal_left f g e HX hs

/-- The actual free local functor used for the case-2 embedding. -/
def ambientEmbeddingFunctor : B ⥤ Ambient S JE JN JP F G :=
  DiagonalCondensation.localFreeAlong (productEmbeddingFunctor JN JB H)
    (productEmbedding_centralizes S JE JN JP F G JB H hH)

instance ambientEmbeddingFunctor_braided :
    (ambientEmbeddingFunctor S JE JN JP F G JB H hH).Braided := by
  unfold ambientEmbeddingFunctor productEmbeddingFunctor
  infer_instance
instance ambientEmbeddingFunctor_additive :
    (ambientEmbeddingFunctor S JE JN JP F G JB H hH).Additive := by
  unfold ambientEmbeddingFunctor productEmbeddingFunctor
  infer_instance
instance ambientEmbeddingFunctor_linear :
    (ambientEmbeddingFunctor S JE JN JP F G JB H hH).Linear ℂ := by
  unfold ambientEmbeddingFunctor productEmbeddingFunctor
  infer_instance

/-- The actual diagonal Hom comparison proves full faithfulness of the
actual module-valued first-factor free embedding. -/
def productFreeEmbeddingFullyFaithful :
    ((productEmbeddingFunctor JN JB H) ⋙
      InternalModule.freeFunctor (A := algebra S JE JN JP F G)).FullyFaithful :=
  (Functor.FullyFaithful.ofFullyFaithful H.functor).comp
    (DiagonalCondensation.leftFreeFunctorFullyFaithful S F.functor G.functor
      (DiagonalAlgebra.productCanonicalAlgebraIso S F.functor G.functor) T)

/-- The prescribed pivotal structures are preserved by the first-factor
embedding, through its actual canonical double-dual comparison. -/
theorem productEmbedding_preservesPivotal :
    PreservesPivotal (productEmbeddingFunctor JN JB H) JB (productPivotal JN JP) :=
  H.pivotal.comp (DeligneProduct.leftReverseSecond_preservesPivotal JN JP)

/-- The actual fully faithful braided spherical embedding of the given
category into the constructed actual local modular category. -/
def ambientEmbedding (hJE : JE.Spherical) :
    letI := ambientRightRigid S T U JE JN JP F G hJE
    BraidedSphericalEmbedding JB (ambientPivotal S T U JE JN JP F G hJE) := by
  letI := (separable S JE JN JP F G hJE).moduleRightRigid
  letI := ambientRightRigid S T U JE JN JP F G hJE
  exact localSphericalEmbedding JB (productPivotal JN JP)
    (algebra_twist S JE JN JP F G hJE) (productEmbeddingFunctor JN JB H)
    (productEmbedding_centralizes S JE JN JP F G JB H hH)
    (productEmbedding_preservesPivotal JN JP JB H)
    (productFreeEmbeddingFullyFaithful S T JE JN JP F G JB H)

/-- The constructed spherical embedding is exactly the actual free local functor. -/
@[simp] theorem ambientEmbedding_functor (hJE : JE.Spherical) :
    letI := ambientRightRigid S T U JE JN JP F G hJE
    (ambientEmbedding S T U JE JN JP F G JB H hH hJE).functor =
      ambientEmbeddingFunctor S JE JN JP F G JB H hH := rfl

end Paper18.Category.CaseTwoCondensation
