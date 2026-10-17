import Paper18.Category.CentralizerFusion

/-!
# The actual conclusion sought by the modular extension theorem

This file only defines the categorical conclusion and its constituent data.
It does not assume the existence of an extension. In particular, modularity
means actual transparent objects are sums of units, and centralizer
integrality is intrinsic integrality of the constructed full subcategory.
-/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [RightRigidCategory C] [BraidedCategory C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [RightRigidCategory D] [BraidedCategory D]

/-- An actual fully faithful complex-linear braided spherical embedding.
Pivotal compatibility uses the canonical comparison derived from cups and
caps; trace preservation is not supplied as an extra field. -/
structure BraidedSphericalEmbedding (JC : PivotalStructure C) (JD : PivotalStructure D) where
  functor : C ⥤ D
  [additive : functor.Additive]
  [linear : functor.Linear ℂ]
  [braided : functor.Braided]
  [full : functor.Full]
  [faithful : functor.Faithful]
  pivotal : PreservesPivotal functor JC JD

attribute [instance] BraidedSphericalEmbedding.additive BraidedSphericalEmbedding.linear
  BraidedSphericalEmbedding.braided BraidedSphericalEmbedding.full
  BraidedSphericalEmbedding.faithful

/-- A genuine modular extension with the given spherical structure and an
integral actual centralizer. Existence of this structure is the conclusion
of the paper's main theorem. -/
structure ModularExtension (JC : PivotalStructure C) where
  ambient : Type u'
  [category : Category.{v'} ambient]
  [preadditive : Preadditive ambient]
  [linear : Linear ℂ ambient]
  [kernels : HasKernels ambient]
  [biproducts : HasFiniteBiproducts ambient]
  [finiteHom : ∀ X Y : ambient, FiniteDimensional ℂ (X ⟶ Y)]
  [monoidal : MonoidalCategory ambient]
  [monoidalPreadditive : MonoidalPreadditive ambient]
  [monoidalLinear : MonoidalLinear ℂ ambient]
  [rightRigid : RightRigidCategory ambient]
  [simpleUnit : Simple (𝟙_ ambient)]
  [braiding : BraidedCategory ambient]
  index : Type w'
  [finiteIndex : Fintype index]
  skeleton : FiniteSemisimpleSkeleton ambient index
  pivotal : PivotalStructure ambient
  modular : IsModular pivotal
  embedding : BraidedSphericalEmbedding JC pivotal
  integralCentralizer : skeleton.CentralizerIntegral (Set.range embedding.functor.obj)

end Paper18.Category
