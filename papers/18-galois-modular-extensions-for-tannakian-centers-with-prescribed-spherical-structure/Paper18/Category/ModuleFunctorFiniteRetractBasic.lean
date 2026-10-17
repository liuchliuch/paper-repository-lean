import Paper18.Category.ModuleFunctorFiniteNeutralTensor
import Paper18.Category.ModuleFunctorFiniteActionIso
import Paper18.Category.ModuleAlphaInductionEnd

/-! # Genuine module-natural cup and cap transformations

A normalized actual cup and cap split the identity homogeneous module
functor through right tensoring twice. All naturality and module
coherence equations are proved using the ambient monoidal coherence.
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

/-- Actual double right tensoring, first into the neutral category and
then into the actual homogeneous component. -/
def neutralTensorAction : ModuleAlphaInduction.End (SignKernel.Positive χ)
    (HomogeneousCategory χ d) where
  toFunctor := neutralRightTensor χ d p hp ⋙
    MonoidalLeftAction.actionRight (SignKernel.Positive χ) n
  leftLinear := inferInstance
  additive := inferInstance
  linear := inferInstance

/-- The actual cap, applied after actual double right tensoring. -/
def neutralTensorCapNat (cap : p ⊗ n.obj ⟶ 𝟙_ C) :
    (neutralTensorAction χ d p hp n).toFunctor ⟶ 𝟭 (HomogeneousCategory χ d) where
  app m := by
    change (m.obj ⊗ p) ⊗ n.obj ⟶ m.obj
    exact (α_ m.obj p n.obj).hom ≫ m.obj ◁ cap ≫ (ρ_ m.obj).hom
  naturality {m m'} f := by
    let a : m.obj ⟶ m'.obj := f
    change ((a ▷ p) ▷ n.obj) ≫
        ((α_ m'.obj p n.obj).hom ≫ m'.obj ◁ cap ≫ (ρ_ m'.obj).hom) =
      ((α_ m.obj p n.obj).hom ≫ m.obj ◁ cap ≫ (ρ_ m.obj).hom) ≫ a
    simp only [Category.assoc]
    rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, rightUnitor_naturality]

/-- The cap is a genuine module natural transformation. -/
instance neutralTensorCapNat_moduleNatural (cap : p ⊗ n.obj ⟶ 𝟙_ C) :
    ModuleFunctor.IsModuleNatural (SignKernel.Positive χ)
      (neutralTensorCapNat χ d p hp n cap) where
  lineator X m := by
    change ((α_ X.obj (m.obj ⊗ p) n.obj).inv ≫ (α_ X.obj m.obj p).inv ▷ n.obj) ≫
        ((α_ (X.obj ⊗ m.obj) p n.obj).hom ≫ (X.obj ⊗ m.obj) ◁ cap ≫
          (ρ_ (X.obj ⊗ m.obj)).hom) =
      X.obj ◁ ((α_ m.obj p n.obj).hom ≫ m.obj ◁ cap ≫ (ρ_ m.obj).hom) ≫ 𝟙 _
    monoidal

/-- The actual cup supplies the reverse actual natural transformation. -/
def neutralTensorCupNat (cup : 𝟙_ C ⟶ p ⊗ n.obj) :
    𝟭 (HomogeneousCategory χ d) ⟶ (neutralTensorAction χ d p hp n).toFunctor where
  app m := by
    change m.obj ⟶ (m.obj ⊗ p) ⊗ n.obj
    exact (ρ_ m.obj).inv ≫ m.obj ◁ cup ≫ (α_ m.obj p n.obj).inv
  naturality {m m'} f := by
    let a : m.obj ⟶ m'.obj := f
    change a ≫ ((ρ_ m'.obj).inv ≫ m'.obj ◁ cup ≫ (α_ m'.obj p n.obj).inv) =
      ((ρ_ m.obj).inv ≫ m.obj ◁ cup ≫ (α_ m.obj p n.obj).inv) ≫ ((a ▷ p) ▷ n.obj)
    simp only [Category.assoc]
    rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
      associator_inv_naturality_left]

/-- The cup is a genuine module natural transformation. -/
instance neutralTensorCupNat_moduleNatural (cup : 𝟙_ C ⟶ p ⊗ n.obj) :
    ModuleFunctor.IsModuleNatural (SignKernel.Positive χ)
      (neutralTensorCupNat χ d p hp n cup) where
  lineator X m := by
    change 𝟙 _ ≫ ((ρ_ (X.obj ⊗ m.obj)).inv ≫ (X.obj ⊗ m.obj) ◁ cup ≫
        (α_ (X.obj ⊗ m.obj) p n.obj).inv) =
      X.obj ◁ ((ρ_ m.obj).inv ≫ m.obj ◁ cup ≫ (α_ m.obj p n.obj).inv) ≫
        ((α_ X.obj (m.obj ⊗ p) n.obj).inv ≫ (α_ X.obj m.obj p).inv ▷ n.obj)
    monoidal

/-- Normalization of the actual cup and cap splits the identity
homogeneous functor in the actual category of strong module functors. -/
lemma neutralTensorCup_cap (cup : 𝟙_ C ⟶ p ⊗ n.obj) (cap : p ⊗ n.obj ⟶ 𝟙_ C)
    (h : cup ≫ cap = 𝟙 _) :
    neutralTensorCupNat χ d p hp n cup ≫ neutralTensorCapNat χ d p hp n cap = 𝟙 _ := by
  ext m
  change ((ρ_ m.obj).inv ≫ m.obj ◁ cup ≫ (α_ m.obj p n.obj).inv) ≫
      ((α_ m.obj p n.obj).hom ≫ m.obj ◁ cap ≫ (ρ_ m.obj).hom) = 𝟙 m.obj
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc, h,
    whiskerLeft_id, Category.id_comp, Iso.inv_hom_id]

/-- The actual normalized cup/cap splitting, bundled as an actual
retract in the category of strong module endofunctors. -/
def neutralTensorRetract (cup : 𝟙_ C ⟶ p ⊗ n.obj) (cap : p ⊗ n.obj ⟶ 𝟙_ C)
    (h : cup ≫ cap = 𝟙 _) :
    Retract (ModuleAlphaInduction.endUnit (SignKernel.Positive χ) (HomogeneousCategory χ d))
      (neutralTensorAction χ d p hp n) where
  i := ⟨neutralTensorCupNat χ d p hp n cup,
    show ModuleFunctor.IsModuleNatural _ _ from inferInstance⟩
  r := ⟨neutralTensorCapNat χ d p hp n cap,
    show ModuleFunctor.IsModuleNatural _ _ from inferInstance⟩
  retract := by
    apply ModuleFunctor.bundled_hom_ext
    exact neutralTensorCup_cap χ d p hp n cup cap h

/-- Applying an actual strong module endofunctor to the genuine
normalized cup/cap splitting preserves the actual retract. -/
def neutralTensorRetractAfter (F : ModuleAlphaInduction.End (SignKernel.Positive χ)
      (HomogeneousCategory χ d))
    (cup : 𝟙_ C ⟶ p ⊗ n.obj) (cap : p ⊗ n.obj ⟶ 𝟙_ C)
    (h : cup ≫ cap = 𝟙 _) :
    Retract F (neutralTensorAction χ d p hp n ⊗ F) :=
  (Retract.ofIso (λ_ F).symm).trans
    ((neutralTensorRetract χ d p hp n cup cap h).map (tensorRight F))

end Paper18.Category.FixedBoundary
