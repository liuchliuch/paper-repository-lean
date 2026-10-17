import Paper18.Category.NondegenerateExtension

/-! # Packaging an actual spherical embedding with its proved centralizer -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u v' u' w'
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [RightRigidCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)] [BraidedCategory D]
  {ι : Type w'} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  {J : PivotalStructure C} {K : PivotalStructure D}

/-- This only packages existing actual data and proofs; the input
centralizer proof must be derived by the relevant categorical construction. -/
def ModularExtension.ofEmbedding (hK : IsModular K)
    (F : BraidedSphericalEmbedding J K)
    (hI : S.CentralizerIntegral (Set.range F.functor.obj)) :
    ModularExtension.{v,u,v',u',w'} J where
  ambient := D
  category := inferInstance
  preadditive := inferInstance
  linear := inferInstance
  kernels := inferInstance
  biproducts := inferInstance
  finiteHom := inferInstance
  monoidal := inferInstance
  monoidalPreadditive := inferInstance
  monoidalLinear := inferInstance
  rightRigid := inferInstance
  simpleUnit := inferInstance
  braiding := inferInstance
  index := ι
  finiteIndex := inferInstance
  skeleton := S
  pivotal := K
  modular := hK
  embedding := F
  integralCentralizer := hI

end Paper18.Category
