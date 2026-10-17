import Paper18.Category.ModuleFunctorFinite
import Paper18.Category.FixedBoundaryOddModule

/-! # Actual module-functor finite Hom spaces for homogeneous components -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasFiniteBiproducts C]
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom] (d : ZMod 2)

instance homogeneousActionLeft_additive (X : SignKernel.Positive χ) :
    (MonoidalLeftAction.actionLeft (HomogeneousCategory χ d) X).Additive where
  map_add := by
    intro Y Z f g
    change X.obj ◁ ((f : Y.obj ⟶ Z.obj) + g) = X.obj ◁ f + X.obj ◁ g
    exact (tensorLeft X.obj).map_add

instance homogeneousActionLeft_linear (X : SignKernel.Positive χ) :
    (MonoidalLeftAction.actionLeft (HomogeneousCategory χ d) X).Linear ℂ where
  map_smul {Y Z} f r := by
    change X.obj ◁ (r • (f : Y.obj ⟶ Z.obj)) = r • (X.obj ◁ f)
    exact (tensorLeft X.obj).map_smul r f

instance homogeneousActionRight_additive (Y : HomogeneousCategory χ d) :
    (MonoidalLeftAction.actionRight (SignKernel.Positive χ) Y).Additive where
  map_add := by
    intro X Z f g
    let a : X.obj ⟶ Z.obj := f
    let b : X.obj ⟶ Z.obj := g
    change (a + b) ▷ Y.obj = a ▷ Y.obj + b ▷ Y.obj
    exact (tensorRight Y.obj).map_add

instance homogeneousActionRight_linear (Y : HomogeneousCategory χ d) :
    (MonoidalLeftAction.actionRight (SignKernel.Positive χ) Y).Linear ℂ where
  map_smul {X Z} f r := by
    let a : X.obj ⟶ Z.obj := f
    change (r • a) ▷ Y.obj = r • (a ▷ Y.obj)
    exact (tensorRight Y.obj).map_smul r a

/-- The actual category of additive complex-linear strong module
endofunctors of an actual homogeneous component. -/
abbrev HomogeneousModuleEnd :=
  ModuleFunctor.Bundled (SignKernel.Positive χ) (HomogeneousCategory χ d)
    (HomogeneousCategory χ d)

section Finite
variable [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- Actual finite Hom spaces, deduced from the inherited actual simple
decomposition of the homogeneous component. -/
def homogeneousModuleEndFiniteHom (F G : HomogeneousModuleEnd χ d) :
    FiniteDimensional ℂ (F ⟶ G) :=
  ModuleFunctor.finiteDimensionalHom (homogeneousSkeleton χ d S) F G

end Finite
end Paper18.Category.FixedBoundary
