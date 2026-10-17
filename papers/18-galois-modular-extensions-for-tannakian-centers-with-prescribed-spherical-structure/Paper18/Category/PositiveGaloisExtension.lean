import Paper18.Category.GaloisBraidedExtension
import Paper18.Category.SphericalComparisonPositive

/-! # The actual positive extension output required in the second case

This defines the target for the positive Johnson--Freyd construction and
forgets it to the paper's actual modular-extension target. Existence is
not assumed or asserted here.
-/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u v' u' w'
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [RightRigidCategory C] [BraidedCategory C]

/-- An actual positive pivotal refinement of an actual braided extension,
including the canonical pivotal comparison on its actual inclusion. -/
structure PositiveGaloisExtension (J : PivotalStructure C) extends
    GaloisBraidedExtension.{v,u,v',u',w'} C where
  pivotal : PivotalStructure toGaloisBraidedExtension.ambient
  positive : pivotal.Positive
  preserves : PreservesPivotal toGaloisBraidedExtension.inclusion J pivotal

variable {J : PivotalStructure C} (E : PositiveGaloisExtension J)

/-- The positive target has the actual required spherical structure,
because positivity of actual categorical traces implies sphericality. -/
def PositiveGaloisExtension.toModularExtension :
    ModularExtension.{v,u,v',u',w'} J where
  ambient := E.ambient
  category := E.category
  preadditive := E.preadditive
  linear := E.linear
  kernels := E.kernels
  biproducts := E.biproducts
  finiteHom := E.finiteHom
  monoidal := E.monoidal
  monoidalPreadditive := E.monoidalPreadditive
  monoidalLinear := E.monoidalLinear
  rightRigid := E.rightRigid
  simpleUnit := E.simpleUnit
  braiding := E.braiding
  index := E.index
  finiteIndex := E.finiteIndex
  skeleton := E.skeleton
  pivotal := E.pivotal
  modular := ⟨E.pivotal.spherical_of_positive E.skeleton E.positive,E.nondegenerate⟩
  embedding :=
    { functor := E.inclusion
      pivotal := E.preserves }
  integralCentralizer := E.integralCentralizer

end Paper18.Category
