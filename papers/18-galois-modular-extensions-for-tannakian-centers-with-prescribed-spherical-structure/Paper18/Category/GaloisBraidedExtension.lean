import Paper18.Category.NondegenerateExtension

/-! # The actual nonspherical extension required from Johnson--Freyd

This is only the type of the required categorical output. Its fields are
actual category structures, an actual braided full embedding and actual
centralizer integrality. It asserts no existence and contains no obstruction
or classification certificate.
-/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u v' u' w'
namespace Paper18.Category
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C]

/-- An actual nondegenerate braided extension with integral actual
centralizer, without a prescribed pivotal structure on the ambient category. -/
structure GaloisBraidedExtension where
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
  inclusion : C ⥤ ambient
  [inclusionAdditive : inclusion.Additive]
  [inclusionLinear : inclusion.Linear ℂ]
  [inclusionBraided : inclusion.Braided]
  [inclusionFull : inclusion.Full]
  [inclusionFaithful : inclusion.Faithful]
  nondegenerate : IsNondegenerate (C := ambient)
  integralCentralizer : skeleton.CentralizerIntegral (Set.range inclusion.obj)

attribute [instance] GaloisBraidedExtension.category GaloisBraidedExtension.preadditive
  GaloisBraidedExtension.linear GaloisBraidedExtension.kernels GaloisBraidedExtension.biproducts
  GaloisBraidedExtension.finiteHom GaloisBraidedExtension.monoidal
  GaloisBraidedExtension.monoidalPreadditive GaloisBraidedExtension.monoidalLinear
  GaloisBraidedExtension.rightRigid GaloisBraidedExtension.simpleUnit
  GaloisBraidedExtension.braiding GaloisBraidedExtension.finiteIndex
  GaloisBraidedExtension.inclusionAdditive GaloisBraidedExtension.inclusionLinear
  GaloisBraidedExtension.inclusionBraided GaloisBraidedExtension.inclusionFull
  GaloisBraidedExtension.inclusionFaithful

end Paper18.Category
