import Paper18.Category.ModuleFunctorFiniteRetract
import Paper18.Category.ModuleAlphaInductionRightTensor

/-! # Actual alpha objects for double right tensor functors

The genuine central flip and the genuine associator identify double
right tensoring with actual negative alpha induction. All comparisons
are actual module natural isomorphisms.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasFiniteBiproducts C]
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom] (d : ZMod 2)
  (p : C) (hp : Homogeneous χ d p) (n : HomogeneousCategory χ d)

/-- The actual neutral object whose right action is double right tensoring. -/
def neutralTensorRightObject : SignKernel.Positive χ :=
  ⟨p ⊗ n.obj, homogeneous_same_tensor_positive χ d n.obj n.property p hp⟩

/-- The ambient associator gives an actual ordinary natural isomorphism. -/
def rightTensorAssociatorIso :
    homogeneousRightTensor χ d (neutralTensorRightObject χ d p hp n) ≅
      (neutralTensorAction χ d p hp n).toFunctor :=
  NatIso.ofComponents (fun m => ObjectProperty.isoMk _ (α_ m.obj p n.obj).symm)
    (fun {m m'} f => by
      let a : m.obj ⟶ m'.obj := f
      change a ▷ (p ⊗ n.obj) ≫ (α_ m'.obj p n.obj).inv =
        (α_ m.obj p n.obj).inv ≫ (a ▷ p) ▷ n.obj
      exact associator_inv_naturality_left a p n.obj)

/-- The associator comparison satisfies genuine module naturality. -/
instance rightTensorAssociatorIso_moduleNatural :
    ModuleFunctor.IsModuleNatural (SignKernel.Positive χ)
      (rightTensorAssociatorIso χ d p hp n).hom where
  lineator X m := by
    change (α_ X.obj m.obj (p ⊗ n.obj)).inv ≫ (α_ (X.obj ⊗ m.obj) p n.obj).inv =
      X.obj ◁ (α_ m.obj p n.obj).inv ≫
        (α_ X.obj (m.obj ⊗ p) n.obj).inv ≫ (α_ X.obj m.obj p).inv ▷ n.obj
    monoidal

variable [BraidedCategory (SignKernel.Positive χ)]
  (L : SignKernel.Positive χ ⥤ Center C)
  (e : SignKernel.inclusion χ ≅ L ⋙ Center.forget C)

/-- Actual double right tensoring is actual negative alpha induction of
its actual neutral tensor object. -/
def negativeTensorActionIso (hL : NegativeCentralCompatibility χ L e) :
    (ModuleAlphaInduction.negative (SignKernel.Positive χ) (HomogeneousCategory χ d)).obj
        (neutralTensorRightObject χ d p hp n) ≅ neutralTensorAction χ d p hp n := by
  letI := negativeCentralFlip_moduleNatural χ d L e hL (neutralTensorRightObject χ d p hp n)
  let t := negativeCentralFlip χ d L e (neutralTensorRightObject χ d p hp n) ≪≫
    rightTensorAssociatorIso χ d p hp n
  letI : ModuleFunctor.IsModuleNatural (SignKernel.Positive χ) t.hom := by
    dsimp only [t, Iso.trans_hom]
    exact ModuleFunctor.moduleNatural_comp (SignKernel.Positive χ)
      (negativeCentralFlip χ d L e (neutralTensorRightObject χ d p hp n)).hom
      (rightTensorAssociatorIso χ d p hp n).hom
  exact ModuleFunctor.isoMk t

end Paper18.Category.FixedBoundary
