import Paper18.Results.CategoricalCaseTwoCondensationData
import Paper18.Category.PivotalProductMap
import Paper18.Category.DiagonalAlgebraProductPivotal

/-! # The actual modular category obtained by case-2 condensation -/
noncomputable section
set_option maxHeartbeats 2000000
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


local instance productBraidingMain : BraidedCategory (DeligneProduct N P) :=
  DeligneProduct.reverseSecondBraiding N P
local instance algebraCommMain : IsCommMonObj (algebra S JE JN JP F G) :=
  algebra_commutative S JE JN JP F G

/-- The actual prescribed pivotal structure on N times the reverse of P. -/
abbrev productPivotal : PivotalStructure (DeligneProduct N P) :=
  DeligneProduct.reverseRightProductPivotal JN JP

/-- The actual algebra twist is derived from actual pivotal preservation
of the actual product functor and the proved spherical diagonal twist. -/
theorem algebra_twist (hJE : JE.Spherical) :
    ((productPivotal JN JP).twistIso (algebra S JE JN JP F G)).hom = 𝟙 _ := by
  exact DiagonalAlgebra.productCanonicalAlgebra_twist S F.functor G.functor
    JE JN JP F.pivotal G.pivotal hJE

include T U in
/-- Actual modularity of the reverse-second product follows from actual
modularity of its two factors. -/
theorem product_modular (hN : IsModular JN) (hP : IsModular JP) :
    IsModular (productPivotal JN JP) := by
  refine ⟨DeligneProduct.reverseRightProductPivotal_spherical JN JP T U hN.1 hP.1, ?_⟩
  have hr := (RelativeTensor.nondegenerate_reverse_iff (C := P)).mpr hP.2
  exact @DeligneProduct.isNondegenerate N _ _ _ _ _ _ bN _ _ _
    P _ _ _ _ _ _ (@reverseBraiding P _ _ bP) _ _ _ κ _ T ν _ U _ _ hN.2 hr

variable [HasKernels (DeligneProduct N P)] [Simple (𝟙_ (DeligneProduct N P))]
  [HasCoequalizers (DeligneProduct N P)]

/-- The actual descended local pivotal structure for the constructed
canonical diagonal algebra. Its trivial twist is proved above. -/
def ambientPivotal (hJE : JE.Spherical) :
    letI := ambientRightRigid S T U JE JN JP F G hJE
    PivotalStructure (Ambient S JE JN JP F G) := by
  letI := ambientRightRigid S T U JE JN JP F G hJE
  exact ModuleBalancing.localPivotal (productPivotal JN JP)
    (algebra_twist S JE JN JP F G hJE)

/-- Actual local modularity is derived from actual separability, pairing,
connectedness, and the actual modular product. -/
theorem ambient_modular (hJE : JE.Spherical) (hN : IsModular JN) (hP : IsModular JP) :
    letI := ambientRightRigid S T U JE JN JP F G hJE
    IsModular (ambientPivotal S T U JE JN JP F G hJE) := by
  letI := ambientRightRigid S T U JE JN JP F G hJE
  exact (separable S JE JN JP F G hJE).local_isModular (DeligneProduct.skeleton T U)
    (multiplicationPairing S JE JN JP F G) (productPivotal JN JP)
    (algebra_twist S JE JN JP F G hJE) (algebra_connected S JE JN JP F G)
    (product_modular T U JN JP hN hP)

end Paper18.Category.CaseTwoCondensation
