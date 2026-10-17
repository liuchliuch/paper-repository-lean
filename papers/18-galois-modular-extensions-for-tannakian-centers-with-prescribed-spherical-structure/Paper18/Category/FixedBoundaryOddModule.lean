import Paper18.Category.SignKernelBasic
import Paper18.Category.FixedBoundaryModuleRegular

/-!
# Actual homogeneous module categories

The neutral full tensor subcategory acts on each actual homogeneous full
subcategory by the ambient tensor product. All action coherences are the
ambient associator and unitor equations. Finite semisimplicity is inherited
from actual ambient decompositions.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasFiniteBiproducts C]
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom] (d : ZMod 2)

instance homogeneousAdditiveProperty : IsAdditiveFullProperty (Homogeneous χ d) where
  of_retract r hY := SignKernel.homogeneous_retract χ r hY
  biproduct f hf := homogeneous_biproduct χ f d hf

/-- Tensor a genuine neutral object with a genuine homogeneous object. -/
def homogeneousActionObj (X : SignKernel.Positive χ) (Y : HomogeneousCategory χ d) :
    HomogeneousCategory χ d :=
  ⟨X.obj ⊗ Y.obj, by simpa using homogeneous_tensor χ X.property Y.property⟩

/-- The actual neutral action on an actual homogeneous component. -/
instance homogeneousLeftAction :
    MonoidalLeftAction (SignKernel.Positive χ) (HomogeneousCategory χ d) where
  actionObj := homogeneousActionObj χ d
  actionHomLeft {X X'} f Y := (show X.obj ⟶ X'.obj from f) ▷ Y.obj
  actionHomRight X {Y Y'} g := X.obj ◁ (show Y.obj ⟶ Y'.obj from g)
  actionHom {X X'} {Y Y'} f g :=
    (show X.obj ⟶ X'.obj from f) ⊗ₘ (show Y.obj ⟶ Y'.obj from g)
  actionAssocIso X Y Z := ObjectProperty.isoMk (Homogeneous χ d) (α_ X.obj Y.obj Z.obj)
  actionUnitIso Y := ObjectProperty.isoMk (Homogeneous χ d) (λ_ Y.obj)
  actionHom_def {X X'} {Y Y'} f g := by
    exact MonoidalCategory.tensorHom_def (show X.obj ⟶ X'.obj from f)
      (show Y.obj ⟶ Y'.obj from g)
  actionHomRight_id X Y := by change X.obj ◁ 𝟙 Y.obj = 𝟙 _; simp
  id_actionHomLeft X Y := by change 𝟙 X.obj ▷ Y.obj = 𝟙 _; simp
  actionHom_comp {X X' X''} {Y Y' Y''} f₁ f₂ g₁ g₂ := by
    let a : X.obj ⟶ X'.obj := f₁
    let b : X'.obj ⟶ X''.obj := f₂
    let c : Y.obj ⟶ Y'.obj := g₁
    let e : Y'.obj ⟶ Y''.obj := g₂
    change ((a ≫ b) ⊗ₘ (c ≫ e)) = (a ⊗ₘ c) ≫ (b ⊗ₘ e)
    exact (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).symm
  actionAssocIso_hom_naturality {X X' Y Y'} {Z Z'} f g h := by
    let a : X.obj ⟶ X'.obj := f
    let b : Y.obj ⟶ Y'.obj := g
    let c : Z.obj ⟶ Z'.obj := h
    change ((a ⊗ₘ b) ⊗ₘ c) ≫ (α_ X'.obj Y'.obj Z'.obj).hom =
      (α_ X.obj Y.obj Z.obj).hom ≫ (a ⊗ₘ (b ⊗ₘ c))
    exact associator_naturality a b c
  actionUnitIso_hom_naturality {Y Y'} f := by
    let a : Y.obj ⟶ Y'.obj := f
    change (λ_ Y.obj).hom ≫ a = (𝟙_ C ◁ a) ≫ (λ_ Y'.obj).hom
    exact (leftUnitor_naturality a).symm
  whiskerLeft_actionHomLeft X {Z Z'} f Y := by
    let a : Z.obj ⟶ Z'.obj := f
    change (X.obj ◁ a) ▷ Y.obj =
      (α_ X.obj Z.obj Y.obj).hom ≫ (X.obj ◁ (a ▷ Y.obj)) ≫ (α_ X.obj Z'.obj Y.obj).inv
    monoidal
  whiskerRight_actionHomLeft {Z Z'} X f Y := by
    let a : Z.obj ⟶ Z'.obj := f
    change (a ▷ X.obj) ▷ Y.obj =
      (α_ Z.obj X.obj Y.obj).hom ≫ (a ▷ (X.obj ⊗ Y.obj)) ≫ (α_ Z'.obj X.obj Y.obj).inv
    monoidal
  associator_actionHom X Y Z W := by
    change (α_ X.obj Y.obj Z.obj).hom ▷ W.obj ≫
      (α_ X.obj (Y.obj ⊗ Z.obj) W.obj).hom ≫
      (X.obj ◁ (α_ Y.obj Z.obj W.obj).hom) =
      (α_ (X.obj ⊗ Y.obj) Z.obj W.obj).hom ≫
        (α_ X.obj Y.obj (Z.obj ⊗ W.obj)).hom
    monoidal
  leftUnitor_actionHom X Y := by
    change (λ_ X.obj).hom ▷ Y.obj =
      (α_ (𝟙_ C) X.obj Y.obj).hom ≫ (λ_ (X.obj ⊗ Y.obj)).hom
    monoidal
  rightUnitor_actionHom X Y := by
    change (ρ_ X.obj).hom ▷ Y.obj =
      (α_ X.obj (𝟙_ C) Y.obj).hom ≫ (X.obj ◁ (λ_ Y.obj).hom)
    monoidal

section Semisimple
variable [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

instance homogeneousFiniteHom (X Y : HomogeneousCategory χ d) :
    FiniteDimensional ℂ (X ⟶ Y) := inferInstanceAs (FiniteDimensional ℂ (X.obj ⟶ Y.obj))

def homogeneousHasKernels : HasKernels (HomogeneousCategory χ d) :=
  S.fullSubcategoryHasKernels (Homogeneous χ d)

def homogeneousSkeleton : FiniteSemisimpleSkeleton (HomogeneousCategory χ d)
    {i : ι // Homogeneous χ d (S.simpleObject i)} :=
  S.fullSubcategorySkeleton (Homogeneous χ d)

end Semisimple
end Paper18.Category.FixedBoundary
