import Paper18.Category.CrossedBraidedGaugingHexagonBlocks
import Paper18.Category.EquivariantInduction

/-! # The actual neutral crossing with arbitrary objects -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe v u w
namespace Paper18.Category.CrossedBraidedGauging.CrossedBraiding
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  {P : Grading G C} {A : WeakAction G C}
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  {Q : GradedAction P A} (B : CrossedBraiding P A Q)

/-- A neutral object has an actual crossing with every object, by the
specified weak-action unit comparison. -/
def neutralIso (X : C) (hX : P.Homogeneous 1 X) (Y : C) : X ⊗ Y ≅ Y ⊗ X :=
  B.crossing 1 X hX Y ≪≫ whiskerRightIso (A.unitIso.app Y) X

@[simp] theorem neutralIso_hom (X : C) (hX : P.Homogeneous 1 X) (Y : C) :
    (B.neutralIso X hX Y).hom =
      (B.crossing 1 X hX Y).hom ≫ (A.unitIso.hom.app Y ▷ X) := rfl

@[reassoc] theorem neutralIso_naturality_left {X X' : C}
    (hX : P.Homogeneous 1 X) (hX' : P.Homogeneous 1 X') (f : X ⟶ X') (Y : C) :
    (f ▷ Y) ≫ (B.neutralIso X' hX' Y).hom =
      (B.neutralIso X hX Y).hom ≫ (Y ◁ f) := by
  simp only [neutralIso_hom]
  rw [← Category.assoc, B.naturality_left 1 hX hX' f Y, Category.assoc, whisker_exchange]
  simp only [Category.assoc]
  rfl

@[reassoc] theorem neutralIso_naturality_right (X : C) (hX : P.Homogeneous 1 X)
    {Y Y' : C} (f : Y ⟶ Y') :
    (X ◁ f) ≫ (B.neutralIso X hX Y').hom =
      (B.neutralIso X hX Y).hom ≫ (f ▷ X) := by
  simp only [neutralIso_hom]
  rw [← Category.assoc, B.naturality_right, Category.assoc,
    ← comp_whiskerRight, A.unitIso.hom.naturality f]
  change (B.crossing 1 X hX Y).hom ≫ ((A.unitIso.hom.app Y ≫ f) ▷ X) = _
  simp only [comp_whiskerRight, Category.assoc]

@[simp] theorem neutralIso_unit_left (Y : C) :
    (B.neutralIso (𝟙_ C) P.homogeneous_unit Y).hom =
      (λ_ Y).hom ≫ (ρ_ Y).inv := by
  rw [neutralIso_hom, B.unit_left]
  simp only [Category.assoc]
  rw [← rightUnitor_inv_naturality]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rfl

@[simp] theorem neutralIso_eq_block (X : C) (hX : P.Homogeneous 1 X)
    (Y : A.Equivariant) :
    (B.neutralIso X hX Y.obj).hom = (B.blockIso 1 X hX Y).hom := by
  simp only [neutralIso_hom, blockIso_hom, Y.unit]

/-- The neutral crossing satisfies the actual half-braiding hexagon with
arbitrary, possibly nonneutral, objects. -/
theorem neutralIso_tensor_right (X : C) (hX : P.Homogeneous 1 X) (Y Z : C) :
    (B.neutralIso X hX (Y ⊗ Z)).hom =
      (α_ X Y Z).inv ≫ ((B.neutralIso X hX Y).hom ▷ Z) ≫
        (α_ Y X Z).hom ≫ (Y ◁ (B.neutralIso X hX Z).hom) ≫ (α_ Y Z X).inv := by
  have hu : A.unitIso.hom.app (Y ⊗ Z) =
      δ (A.ρ 1) Y Z ≫ (A.unitIso.hom.app Y ⊗ₘ A.unitIso.hom.app Z) := by
    simpa using monoidalNatTrans_delta A.unitIso.hom Y Z
  rw [neutralIso_hom, hu, B.hexagon_right]
  simp only [comp_whiskerRight, Category.assoc]
  rw [← comp_whiskerRight_assoc, Functor.Monoidal.μ_δ, id_whiskerRight, Category.id_comp]
  simp only [neutralIso_hom]
  simp only [tensorHom_def', comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [← associator_inv_naturality_middle_assoc,
    ← associator_inv_naturality_left, whisker_exchange_assoc, whisker_exchange_assoc,
    ← associator_naturality_left_assoc]
  rfl

section Induction
variable [CategoryTheory.Limits.HasFiniteBiproducts C]
  [∀ g : G, (A.ρ g).Additive]

/-- The second neutral hexagon on an actual equivariant test object. -/
theorem neutralIso_tensor_left_equivariant (X Y : C)
    (hX : P.Homogeneous 1 X) (hY : P.Homogeneous 1 Y) (Z : A.Equivariant) :
    (B.neutralIso (X ⊗ Y) (by simpa using P.homogeneous_tensor hX hY) Z.obj).hom =
      (α_ X Y Z.obj).hom ≫ (X ◁ (B.neutralIso Y hY Z.obj).hom) ≫
        (α_ X Z.obj Y).inv ≫ ((B.neutralIso X hX Z.obj).hom ▷ Y) ≫
          (α_ Z.obj X Y).hom := by
  simpa only [one_mul, B.neutralIso_eq_block] using
    B.blockIso_tensor_left 1 1 X Y hX hY Z

/-- Genuine induction is dominant, so naturality extends the other
neutral hexagon from equivariant test objects to arbitrary actual ones. -/
theorem neutralIso_tensor_left (X Y : C)
    (hX : P.Homogeneous 1 X) (hY : P.Homogeneous 1 Y) (Z : C) :
    (B.neutralIso (X ⊗ Y) (by simpa using P.homogeneous_tensor hX hY) Z).hom =
      (α_ X Y Z).hom ≫ (X ◁ (B.neutralIso Y hY Z).hom) ≫
        (α_ X Z Y).inv ≫ ((B.neutralIso X hX Z).hom ▷ Y) ≫
          (α_ Z X Y).hom := by
  let r := A.inductionRetract Z
  let sm : SplitMono (r.i ▷ (X ⊗ Y)) :=
    ⟨r.r ▷ (X ⊗ Y), by rw [← comp_whiskerRight, r.retract, id_whiskerRight]⟩
  letI : Mono (r.i ▷ (X ⊗ Y)) := sm.mono
  apply (cancel_mono (r.i ▷ (X ⊗ Y))).mp
  simp only [Category.assoc]
  rw [← associator_naturality_left r.i X Y]
  rw [← comp_whiskerRight_assoc, ← B.neutralIso_naturality_right X hX r.i]
  simp only [comp_whiskerRight, Category.assoc]
  rw [← associator_inv_naturality_middle_assoc]
  rw [← whiskerLeft_comp_assoc, ← B.neutralIso_naturality_right Y hY r.i]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [← associator_naturality_right_assoc]
  rw [← B.neutralIso_naturality_right]
  erw [B.neutralIso_tensor_left_equivariant X Y hX hY (A.induction Z)]
  rfl

end Induction

end Paper18.Category.CrossedBraidedGauging.CrossedBraiding
