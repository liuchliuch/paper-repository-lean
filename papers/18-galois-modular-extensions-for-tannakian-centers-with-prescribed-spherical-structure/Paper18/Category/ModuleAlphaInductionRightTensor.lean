import Paper18.Category.ModuleAlphaInductionFlip
import Paper18.Category.ModuleFunctorFiniteAlphaFull

/-! # Actual right tensoring and its negative alpha-induction flip -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [CategoryTheory.Limits.HasFiniteBiproducts C]
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom] (d : ZMod 2)

/-- Right tensoring an actual homogeneous object with an actual neutral object. -/
def homogeneousRightTensor (Z : SignKernel.Positive χ) :
    HomogeneousCategory χ d ⥤ HomogeneousCategory χ d where
  obj m := ⟨m.obj ⊗ Z.obj, by
    simpa using homogeneous_tensor χ m.property Z.property⟩
  map {m n} f := (show m.obj ⟶ n.obj from f) ▷ Z.obj
  map_id m := by
    change 𝟙 m.obj ▷ Z.obj = _
    rw [id_whiskerRight]
    rfl
  map_comp {m n p} f g := by
    change ((show m.obj ⟶ n.obj from f) ≫ (show n.obj ⟶ p.obj from g)) ▷ Z.obj = _
    rw [comp_whiskerRight]
    rfl

instance homogeneousRightTensorLeftLinear (Z : SignKernel.Positive χ) :
    (homogeneousRightTensor χ d Z).LeftLinear (SignKernel.Positive χ) where
  μₗ X m := (α_ X.obj m.obj Z.obj).inv
  μₗ_naturality_left {X X'} f m := by
    change ((show X.obj ⟶ X'.obj from f) ▷ (m.obj ⊗ Z.obj)) ≫ (α_ X'.obj m.obj Z.obj).inv =
      (α_ X.obj m.obj Z.obj).inv ≫ (((show X.obj ⟶ X'.obj from f) ▷ m.obj) ▷ Z.obj)
    monoidal
  μₗ_naturality_right X {m n} f := by
    change (X.obj ◁ ((show m.obj ⟶ n.obj from f) ▷ Z.obj)) ≫ (α_ X.obj n.obj Z.obj).inv =
      (α_ X.obj m.obj Z.obj).inv ≫ ((X.obj ◁ (show m.obj ⟶ n.obj from f)) ▷ Z.obj)
    monoidal
  μₗ_associativity X Y m := by
    change (α_ (X.obj ⊗ Y.obj) m.obj Z.obj).inv ≫ ((α_ X.obj Y.obj m.obj).hom ▷ Z.obj) =
      (α_ X.obj Y.obj (m.obj ⊗ Z.obj)).hom ≫ (X.obj ◁ (α_ Y.obj m.obj Z.obj).inv) ≫
        (α_ X.obj (Y.obj ⊗ m.obj) Z.obj).inv
    monoidal
  μₗ_unitality m := by
    change (λ_ (m.obj ⊗ Z.obj)).hom = (α_ (𝟙_ C) m.obj Z.obj).inv ≫ ((λ_ m.obj).hom ▷ Z.obj)
    monoidal
  δₗ X m := (α_ X.obj m.obj Z.obj).hom
  δₗ_naturality_left {X X'} f m := by
    change (((show X.obj ⟶ X'.obj from f) ▷ m.obj) ▷ Z.obj) ≫ (α_ X'.obj m.obj Z.obj).hom =
      (α_ X.obj m.obj Z.obj).hom ≫ ((show X.obj ⟶ X'.obj from f) ▷ (m.obj ⊗ Z.obj))
    monoidal
  δₗ_naturality_right X {m n} f := by
    change ((X.obj ◁ (show m.obj ⟶ n.obj from f)) ▷ Z.obj) ≫ (α_ X.obj n.obj Z.obj).hom =
      (α_ X.obj m.obj Z.obj).hom ≫ (X.obj ◁ ((show m.obj ⟶ n.obj from f) ▷ Z.obj))
    monoidal
  δₗ_associativity X Y m := by
    change (α_ (X.obj ⊗ Y.obj) m.obj Z.obj).hom ≫ (α_ X.obj Y.obj (m.obj ⊗ Z.obj)).hom =
      ((α_ X.obj Y.obj m.obj).hom ▷ Z.obj) ≫ (α_ X.obj (Y.obj ⊗ m.obj) Z.obj).hom ≫
        (X.obj ◁ (α_ Y.obj m.obj Z.obj).hom)
    monoidal
  δₗ_unitality_inv m := by
    change (λ_ (m.obj ⊗ Z.obj)).inv = ((λ_ m.obj).inv ▷ Z.obj) ≫ (α_ (𝟙_ C) m.obj Z.obj).hom
    monoidal
  μₗ_comp_δₗ X m := (α_ X.obj m.obj Z.obj).inv_hom_id
  δₗ_comp_μₗ X m := (α_ X.obj m.obj Z.obj).hom_inv_id

instance homogeneousRightTensor_additive (Z : SignKernel.Positive χ) :
    (homogeneousRightTensor χ d Z).Additive where
  map_add {m n} f g := by
    change ((show m.obj ⟶ n.obj from f) + (show m.obj ⟶ n.obj from g)) ▷ Z.obj = _
    simpa only [homogeneousRightTensor] using MonoidalPreadditive.add_whiskerRight (X := Z.obj) (show m.obj ⟶ n.obj from f) (show m.obj ⟶ n.obj from g)

instance homogeneousRightTensor_linear (Z : SignKernel.Positive χ) :
    (homogeneousRightTensor χ d Z).Linear ℂ where
  map_smul {m n} f r := by
    change (r • (show m.obj ⟶ n.obj from f)) ▷ Z.obj = _
    simpa only [homogeneousRightTensor] using MonoidalLinear.smul_whiskerRight r (show m.obj ⟶ n.obj from f) Z.obj

variable [BraidedCategory (SignKernel.Positive χ)]
  (L : SignKernel.Positive χ ⥤ Center C)
  (e : SignKernel.inclusion χ ≅ L ⋙ Center.forget C)
local notation "K" => ModuleFunctor.strictCenterFunctor L (SignKernel.inclusion χ) e
local notation "Alpha" => ModuleAlphaInduction.negative (SignKernel.Positive χ) (HomogeneousCategory χ d)

/-- The genuine neutral central lift crosses every homogeneous object. -/
def negativeCentralFlip (Z : SignKernel.Positive χ) :
    ((Alpha).obj Z).toFunctor ≅ homogeneousRightTensor χ d Z :=
  NatIso.ofComponents
    (fun m => ObjectProperty.isoMk _ (((K).obj Z).2.β m.obj))
    (fun f => ((K).obj Z).2.naturality (show _ ⟶ _ from f))

@[simp] theorem negativeCentralFlip_hom_app (Z : SignKernel.Positive χ)
    (m : HomogeneousCategory χ d) :
    (negativeCentralFlip χ d L e Z).hom.app m = (((K).obj Z).2.β m.obj).hom := rfl

instance negativeCentralFlip_moduleNatural
    (hL : NegativeCentralCompatibility χ L e) (Z : SignKernel.Positive χ) :
    ModuleFunctor.IsModuleNatural (SignKernel.Positive χ)
      (negativeCentralFlip χ d L e Z).hom where
  lineator X m := by
    rw [ModuleAlphaInduction.negative_μ]
    have hi : ((K).obj Z).2.β X.obj =
        (SignKernel.inclusion χ).mapIso (β_ X Z).symm := Iso.ext (hL Z X)
    have hh := ModuleAlphaInduction.centralFlip_lineator ((K).obj Z) X.obj m.obj
    rw [hi] at hh
    simpa only [Category.assoc] using hh

end Paper18.Category.FixedBoundary
