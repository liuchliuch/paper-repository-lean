import Paper18.Category.ModuleFunctorFiniteRetractBasic

/-! # Actual retract presentations of strong module functors

The genuine action lineator carries the normalized double-tensor
retract through any actual strong module functor. This constructs an
actual retract of a functor built from its value at one homogeneous
object; no semisimplicity of the module-functor category is assumed.
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
  (F : ModuleAlphaInduction.End (SignKernel.Positive χ) (HomogeneousCategory χ d))

/-- The actual strong lineators of F identify the two genuine double
right tensor module functors, including module naturality. -/
def neutralTensorLineatorIso :
    neutralTensorAction χ d p hp (F.toFunctor.obj n) ≅ neutralTensorAction χ d p hp n ⊗ F := by
  let Q := neutralRightTensor χ d p hp
  let a := MonoidalLeftAction.actionRight (SignKernel.Positive χ) n
  let t := Functor.isoWhiskerLeft Q (ModuleFunctor.actionLineatorIso
    (C := SignKernel.Positive χ) F.toFunctor n)
  letI : ModuleFunctor.IsModuleNatural (SignKernel.Positive χ) t.hom := by
    dsimp only [t, Functor.isoWhiskerLeft_hom]
    exact ModuleAlphaInduction.moduleNatural_whiskerLeft (F := Q)
      (ModuleFunctor.actionLineatorIso (C := SignKernel.Positive χ) F.toFunctor n).hom
  letI : ModuleFunctor.IsModuleNatural (SignKernel.Positive χ)
      (Functor.associator Q a F.toFunctor).inv :=
    ModuleFunctor.moduleNatural_inv (SignKernel.Positive χ) (Functor.associator Q a F.toFunctor)
  let e := t ≪≫ (Functor.associator Q a F.toFunctor).symm
  letI : ModuleFunctor.IsModuleNatural (SignKernel.Positive χ) e.hom := by
    dsimp only [e, Iso.trans_hom, Iso.symm_hom]
    exact ModuleFunctor.moduleNatural_comp (SignKernel.Positive χ) t.hom
      (Functor.associator Q a F.toFunctor).inv
  exact ModuleFunctor.isoMk e

/-- The actual functor F is an actual retract of double right tensoring
by p and its actual value F(n). -/
def neutralTensorFunctorRetract (cup : 𝟙_ C ⟶ p ⊗ n.obj)
    (cap : p ⊗ n.obj ⟶ 𝟙_ C) (h : cup ≫ cap = 𝟙 _) :
    Retract F (neutralTensorAction χ d p hp (F.toFunctor.obj n)) :=
  (neutralTensorRetractAfter χ d p hp n F cup cap h).trans
    (Retract.ofIso (neutralTensorLineatorIso χ d p hp n F).symm)

end Paper18.Category.FixedBoundary
