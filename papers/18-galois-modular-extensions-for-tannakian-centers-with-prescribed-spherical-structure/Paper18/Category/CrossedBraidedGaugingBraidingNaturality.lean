import Paper18.Category.CrossedBraidedGaugingBraidingComponents

/-! # Genuine naturality of the assembled gauging crossing -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.CrossedBraidedGauging.CrossedBraiding
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasKernels C] [HasFiniteBiproducts C]
  {P : Grading G C} {A : WeakAction G C}
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  {Q : GradedAction P A} (B : CrossedBraiding P A Q)

/-- The assembled map retains the actual original map on every actual
homogeneous object, independently of its chosen kernel-image realization. -/
@[simp] theorem halfSwapIso_homogeneous (g : G) (X : C) (hX : P.Homogeneous g X)
    (Y : A.Equivariant) : (B.halfSwapIso X Y).hom = (B.blockIso g X hX Y).hom := by
  letI : IsIso (P.componentInclusion g X) := (P.componentIso g X hX).isIso_hom
  apply (cancel_epi (P.componentInclusion g X ▷ Y.obj)).mp
  rw [B.halfSwapIso_component,
    B.blockIso_naturality_left g (P.component_homogeneous g X) hX (P.componentInclusion g X) Y]

/-- The actual assembled crossing is natural in every raw first object. -/
@[reassoc] theorem halfSwapIso_naturality_left {X X' : C} (f : X ⟶ X')
    (Y : A.Equivariant) :
    (f ▷ Y.obj) ≫ (B.halfSwapIso X' Y).hom =
      (B.halfSwapIso X Y).hom ≫ (Y.obj ◁ f) := by
  apply P.tensorRight_hom_ext
  intro g
  let fg := (P.componentFunctor g).map f
  have hn := congrArg (fun q => q ▷ Y.obj) (P.componentFunctor_map_inclusion g f)
  simp only [comp_whiskerRight] at hn
  calc
    (P.componentInclusion g X ▷ Y.obj) ≫ ((f ▷ Y.obj) ≫ (B.halfSwapIso X' Y).hom) =
        (fg ▷ Y.obj) ≫ (P.componentInclusion g X' ▷ Y.obj) ≫ (B.halfSwapIso X' Y).hom := by
      rw [← Category.assoc, ← hn]
      dsimp only [fg]
      exact Category.assoc _ _ _
    _ = (fg ▷ Y.obj) ≫
        (B.blockIso g (P.component g X') (P.component_homogeneous g X') Y).hom ≫
          (Y.obj ◁ P.componentInclusion g X') := by rw [B.halfSwapIso_component]
    _ = (B.blockIso g (P.component g X) (P.component_homogeneous g X) Y).hom ≫
        (Y.obj ◁ fg) ≫ (Y.obj ◁ P.componentInclusion g X') := by
      rw [← Category.assoc, B.blockIso_naturality_left g
        (P.component_homogeneous g X) (P.component_homogeneous g X') fg Y, Category.assoc]
    _ = (B.blockIso g (P.component g X) (P.component_homogeneous g X) Y).hom ≫
        (Y.obj ◁ P.componentInclusion g X) ≫ (Y.obj ◁ f) := by
      rw [← whiskerLeft_comp, P.componentFunctor_map_inclusion, whiskerLeft_comp]
    _ = (P.componentInclusion g X ▷ Y.obj) ≫
        ((B.halfSwapIso X Y).hom ≫ (Y.obj ◁ f)) := by
      simpa only [Category.assoc] using
        (congrArg (fun k => k ≫ (Y.obj ◁ f)) (B.halfSwapIso_component g X Y)).symm

/-- The actual assembled crossing is natural in genuine equivariant
morphisms in the second variable. -/
@[reassoc] theorem halfSwapIso_naturality_right (X : C)
    {Y Y' : A.Equivariant} (f : Y ⟶ Y') :
    (X ◁ f.hom) ≫ (B.halfSwapIso X Y').hom =
      (B.halfSwapIso X Y).hom ≫ (f.hom ▷ X) := by
  apply P.tensorRight_hom_ext
  intro g
  calc
    (P.componentInclusion g X ▷ Y.obj) ≫ ((X ◁ f.hom) ≫ (B.halfSwapIso X Y').hom) =
        (P.component g X ◁ f.hom) ≫ (P.componentInclusion g X ▷ Y'.obj) ≫
          (B.halfSwapIso X Y').hom := by
      rw [← Category.assoc, ← whisker_exchange, Category.assoc]
    _ = (P.component g X ◁ f.hom) ≫
        (B.blockIso g (P.component g X) (P.component_homogeneous g X) Y').hom ≫
          (Y'.obj ◁ P.componentInclusion g X) := by rw [B.halfSwapIso_component]
    _ = (B.blockIso g (P.component g X) (P.component_homogeneous g X) Y).hom ≫
        (f.hom ▷ P.component g X) ≫ (Y'.obj ◁ P.componentInclusion g X) := by
      rw [← Category.assoc, B.blockIso_naturality_right, Category.assoc]
    _ = (B.blockIso g (P.component g X) (P.component_homogeneous g X) Y).hom ≫
        (Y.obj ◁ P.componentInclusion g X) ≫ (f.hom ▷ X) := by
      rw [← whisker_exchange]
    _ = (P.componentInclusion g X ▷ Y.obj) ≫
        ((B.halfSwapIso X Y).hom ≫ (f.hom ▷ X)) := by
      simpa only [Category.assoc] using
        (congrArg (fun k => k ≫ (f.hom ▷ X)) (B.halfSwapIso_component g X Y)).symm

end Paper18.Category.CrossedBraidedGauging.CrossedBraiding
