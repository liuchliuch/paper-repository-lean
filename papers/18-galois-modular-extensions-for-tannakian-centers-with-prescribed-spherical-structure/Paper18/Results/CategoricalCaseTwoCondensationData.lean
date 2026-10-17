import Paper18.Results.CategoricalCaseTwoCondensationBasic
import Paper18.Category.DiagonalAlgebraProductBraided
import Paper18.Category.DiagonalCondensationDimension
import Paper18.Category.DeligneProductNondegenerate

/-! # The actual algebra and local fusion category in case 2 -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj
universe v u w vN uN wN vP uP wP
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

/-- The actual shared diagonal algebra, transported by the two actual
spherical braided embeddings. -/
abbrev algebra : DeligneProduct N P :=
  DiagonalAlgebra.productCanonicalAlgebra S F.functor G.functor

/-- Actual bimodule separability is derived from the spherical shared
category and its canonical diagonal, then transported by the actual functor. -/
def separable (hJE : JE.Spherical) : SeparableAlgebra (algebra S JE JN JP F G) :=
  DiagonalAlgebra.productCanonicalSeparable S F.functor G.functor JE hJE

/-- The actual perfect multiplication pairing is transported independently
of any module category or modularity conclusion. -/
def multiplicationPairing : ModuleBalancing.MultiplicationPairing (algebra S JE JN JP F G) :=
  DiagonalAlgebra.productCanonicalMultiplicationPairing S F.functor G.functor

/-- Actual full faithfulness gives connectedness of the actual diagonal. -/
theorem algebra_connected :
    Module.finrank ℂ (𝟙_ (DeligneProduct N P) ⟶ algebra S JE JN JP F G) = 1 :=
  DiagonalAlgebra.productCanonicalAlgebra_connected S F.functor G.functor

local instance productBraiding : BraidedCategory (DeligneProduct N P) :=
  DeligneProduct.reverseSecondBraiding N P

/-- The actual local-module category, using precisely the reversed second
braiding for which the actual diagonal multiplication is commutative. -/
abbrev Ambient := LocalModules (algebra S JE JN JP F G)

/-- The commutative algebra law for that actual braiding. -/
def algebra_commutative : IsCommMonObj (algebra S JE JN JP F G) :=
  DiagonalAlgebra.productCanonicalAlgebra_commutative S F.functor G.functor

variable [HasKernels (DeligneProduct N P)] [Simple (𝟙_ (DeligneProduct N P))]
  [HasCoequalizers (DeligneProduct N P)]
local instance algebraComm : IsCommMonObj (algebra S JE JN JP F G) :=
  algebra_commutative S JE JN JP F G

/-- Actual kernels of the actual local category, constructed from
separability and the actual ambient product skeleton. -/
def ambientHasKernels (hJE : JE.Spherical) : HasKernels (Ambient S JE JN JP F G) :=
  (separable S JE JN JP F G hJE).localHasKernels (DeligneProduct.skeleton T U)

/-- Actual local duals, obtained by splitting free-module dual idempotents
and the proved dual closure of the actual local fusion subcategory. -/
def ambientRightRigid (hJE : JE.Spherical) : RightRigidCategory (Ambient S JE JN JP F G) :=
  (separable S JE JN JP F G hJE).localRightRigid (DeligneProduct.skeleton T U)
    (algebra_connected S JE JN JP F G)

/-- The actual local tensor unit is simple by actual connectedness. -/
def ambientSimpleUnit (hJE : JE.Spherical) : Simple (𝟙_ (Ambient S JE JN JP F G)) :=
  (separable S JE JN JP F G hJE).localSimpleUnit (DeligneProduct.skeleton T U)
    (algebra_connected S JE JN JP F G)

/-- The finite index of the actual simple local modules. -/
abbrev AmbientIndex (hJE : JE.Spherical) :=
  (separable S JE JN JP F G hJE).LocalSimpleIndex (DeligneProduct.skeleton T U)

/-- The actual complete finite simple skeleton of the constructed category. -/
def ambientSkeleton (hJE : JE.Spherical) :
    FiniteSemisimpleSkeleton (Ambient S JE JN JP F G) (AmbientIndex S T U JE JN JP F G hJE) :=
  (separable S JE JN JP F G hJE).localSkeleton (DeligneProduct.skeleton T U)

end Paper18.Category.CaseTwoCondensation
