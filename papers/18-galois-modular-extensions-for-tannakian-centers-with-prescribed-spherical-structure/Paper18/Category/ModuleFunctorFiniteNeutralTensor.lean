import Paper18.Category.ModuleFunctorFiniteHomogeneous
import Paper18.Category.ModuleFunctorFiniteRegular
import Paper18.Category.ModuleAlphaInductionComposition

/-! # Actual neutral-valued right tensor functors

Right tensoring a homogeneous component by an object of the same parity
lands in the actual neutral full tensor subcategory. The strong module
lineator is the actual ambient associator.
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
  (p : C) (hp : Homogeneous χ d p)

include hp in
lemma homogeneous_same_tensor_positive (X : C) (hX : Homogeneous χ d X) :
    SignKernel.positiveProperty χ (X ⊗ p) := by
  have hd : d + d = 0 := by
    rcases Paper18.ZMod.two_eq_zero_or_one d with rfl | rfl <;> decide
  simpa only [hd] using homogeneous_tensor χ hX hp

/-- The actual right tensor functor from one homogeneous component to
its actual neutral tensor category. -/
def neutralRightTensor : HomogeneousCategory χ d ⥤ SignKernel.Positive χ where
  obj X := ⟨X.obj ⊗ p, homogeneous_same_tensor_positive χ d p hp X.obj X.property⟩
  map {X Y} f := (show X.obj ⟶ Y.obj from f) ▷ p
  map_id X := by change (𝟙 X.obj) ▷ p = 𝟙 _; simp
  map_comp {X Y Z} f g := by
    let a : X.obj ⟶ Y.obj := f
    let b : Y.obj ⟶ Z.obj := g
    change (a ≫ b) ▷ p = (a ▷ p) ≫ (b ▷ p)
    exact comp_whiskerRight a b p

instance neutralRightTensor_additive : (neutralRightTensor χ d p hp).Additive where
  map_add := by
    intro X Y f g
    let a : X.obj ⟶ Y.obj := f
    let b : X.obj ⟶ Y.obj := g
    change (a + b) ▷ p = _
    exact (tensorRight p).map_add

instance neutralRightTensor_linear : (neutralRightTensor χ d p hp).Linear ℂ where
  map_smul {X Y} f r := by
    let a : X.obj ⟶ Y.obj := f
    change (r • a) ▷ p = _
    exact (tensorRight p).map_smul r f

/-- Native strong module coherence is inherited from actual ambient
associator and unitor coherence. -/
instance neutralRightTensorLeftLinear :
    (neutralRightTensor χ d p hp).LeftLinear (SignKernel.Positive χ) where
  μₗ X Y := (α_ X.obj Y.obj p).inv
  μₗ_naturality_left {X X'} f Y := by
    let a : X.obj ⟶ X'.obj := f
    change (a ▷ (Y.obj ⊗ p)) ≫ (α_ X'.obj Y.obj p).inv =
      (α_ X.obj Y.obj p).inv ≫ ((a ▷ Y.obj) ▷ p)
    monoidal
  μₗ_naturality_right X {Y Y'} f := by
    let a : Y.obj ⟶ Y'.obj := f
    change (X.obj ◁ (a ▷ p)) ≫ (α_ X.obj Y'.obj p).inv =
      (α_ X.obj Y.obj p).inv ≫ ((X.obj ◁ a) ▷ p)
    monoidal
  μₗ_associativity X Y Z := by
    change (α_ (X.obj ⊗ Y.obj) Z.obj p).inv ≫ ((α_ X.obj Y.obj Z.obj).hom ▷ p) =
      (α_ X.obj Y.obj (Z.obj ⊗ p)).hom ≫ (X.obj ◁ (α_ Y.obj Z.obj p).inv) ≫
        (α_ X.obj (Y.obj ⊗ Z.obj) p).inv
    monoidal
  μₗ_unitality Y := by
    change (λ_ (Y.obj ⊗ p)).hom = (α_ (𝟙_ C) Y.obj p).inv ≫ ((λ_ Y.obj).hom ▷ p)
    monoidal
  δₗ X Y := (α_ X.obj Y.obj p).hom
  δₗ_naturality_left {X X'} f Y := by
    let a : X.obj ⟶ X'.obj := f
    change ((a ▷ Y.obj) ▷ p) ≫ (α_ X'.obj Y.obj p).hom =
      (α_ X.obj Y.obj p).hom ≫ (a ▷ (Y.obj ⊗ p))
    monoidal
  δₗ_naturality_right X {Y Y'} f := by
    let a : Y.obj ⟶ Y'.obj := f
    change ((X.obj ◁ a) ▷ p) ≫ (α_ X.obj Y'.obj p).hom =
      (α_ X.obj Y.obj p).hom ≫ (X.obj ◁ (a ▷ p))
    monoidal
  δₗ_associativity X Y Z := by
    change (α_ (X.obj ⊗ Y.obj) Z.obj p).hom ≫ (α_ X.obj Y.obj (Z.obj ⊗ p)).hom =
      ((α_ X.obj Y.obj Z.obj).hom ▷ p) ≫ (α_ X.obj (Y.obj ⊗ Z.obj) p).hom ≫
        (X.obj ◁ (α_ Y.obj Z.obj p).hom)
    monoidal
  δₗ_unitality_inv Y := by
    change (λ_ (Y.obj ⊗ p)).inv = ((λ_ Y.obj).inv ▷ p) ≫ (α_ (𝟙_ C) Y.obj p).hom
    monoidal
  μₗ_comp_δₗ X Y := (α_ X.obj Y.obj p).inv_hom_id
  δₗ_comp_μₗ X Y := (α_ X.obj Y.obj p).hom_inv_id

/-- The actual neutral-valued right tensor functor, bundled with all
proved native strong module and complex-linear structure. -/
def neutralRightTensorBundled :
    ModuleFunctor.Bundled (SignKernel.Positive χ) (HomogeneousCategory χ d)
      (SignKernel.Positive χ) where
  toFunctor := neutralRightTensor χ d p hp
  leftLinear := inferInstance
  additive := inferInstance
  linear := inferInstance

end Paper18.Category.FixedBoundary
