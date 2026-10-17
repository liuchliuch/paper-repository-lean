import Paper18.Category.CrossedBraidedGaugingEquivariance
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # Genuine braiding on the equivariantization of a crossed category

The underlying graded category is only monoidal. The equivariant braiding
is derived from the actual crossed isomorphisms and actual degree
decomposition, and all its structural equations are proved here.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Functor.LaxMonoidal Functor.OplaxMonoidal
universe v u w
namespace Paper18.Category.CrossedBraidedGauging.CrossedBraiding
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasKernels C] [HasFiniteBiproducts C]
  {P : Grading G C} {A : WeakAction G C}
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  [∀ g : G, (A.ρ g).Additive]
  {Q : GradedAction P A} (B : CrossedBraiding P A Q)

/-- The actual closed crossed isomorphism is an equivariant morphism. -/
theorem halfSwapIso_comm (X Y : A.Equivariant) (a : G) :
    (A.ρ a).map (B.halfSwapIso X.obj Y).hom ≫
        ((Y ⊗ X).structureIso a).hom =
      ((X ⊗ Y).structureIso a).hom ≫ (B.halfSwapIso X.obj Y).hom := by
  change (A.ρ a).map (B.halfSwapIso X.obj Y).hom ≫
      (δ (A.ρ a) Y.obj X.obj ≫
        ((Y.structureIso a).hom ⊗ₘ (X.structureIso a).hom)) =
    (δ (A.ρ a) X.obj Y.obj ≫
      ((X.structureIso a).hom ⊗ₘ (Y.structureIso a).hom)) ≫
        (B.halfSwapIso X.obj Y).hom
  apply (cancel_epi (μ (A.ρ a) X.obj Y.obj)).mp
  simp only [Category.assoc]
  rw [Functor.Monoidal.μ_δ_assoc]
  rw [tensorHom_def (Y.structureIso a).hom (X.structureIso a).hom,
    tensorHom_def' (X.structureIso a).hom (Y.structureIso a).hom]
  simp only [Category.assoc]
  rw [B.halfSwapIso_action_assoc]
  rw [B.halfSwapIso_naturality_left]

/-- The actual equivariant braiding, with the assembled map as its actual
underlying morphism. -/
def equivariantBraiding (X Y : A.Equivariant) : X ⊗ Y ≅ Y ⊗ X :=
  WeakAction.Equivariant.mkIso A (B.halfSwapIso X.obj Y) (B.halfSwapIso_comm X Y)

@[simp] theorem equivariantBraiding_hom (X Y : A.Equivariant) :
    (B.equivariantBraiding X Y).hom.hom = (B.halfSwapIso X.obj Y).hom := rfl

@[simp] theorem gauging_whiskerLeft_hom (X : A.Equivariant)
    {Y Z : A.Equivariant} (f : Y ⟶ Z) : (X ◁ f).hom = X.obj ◁ f.hom := by
  change (𝟙 X.obj ⊗ₘ f.hom) = _
  simp only [id_tensorHom]

@[simp] theorem gauging_whiskerRight_hom {X Y : A.Equivariant}
    (f : X ⟶ Y) (Z : A.Equivariant) : (f ▷ Z).hom = f.hom ▷ Z.obj := by
  change (f.hom ⊗ₘ 𝟙 Z.obj) = _
  simp only [tensorHom_id]

/-- A genuine finite crossed braiding gives a genuine braiding on actual
equivariant objects. No braiding on the underlying category is assumed. -/
def equivariantBraidedCategory : BraidedCategory A.Equivariant where
  braiding := B.equivariantBraiding
  braiding_naturality_right X {Y Z} f := by
    apply WeakAction.Equivariant.Hom.ext
    simpa only [WeakAction.Equivariant.comp_hom, gauging_whiskerLeft_hom,
      gauging_whiskerRight_hom, equivariantBraiding_hom] using
        B.halfSwapIso_naturality_right X.obj f
  braiding_naturality_left {X Y} f Z := by
    apply WeakAction.Equivariant.Hom.ext
    simpa only [WeakAction.Equivariant.comp_hom, gauging_whiskerLeft_hom,
      gauging_whiskerRight_hom, equivariantBraiding_hom] using
        B.halfSwapIso_naturality_left f.hom Z
  hexagon_forward X Y Z := by
    apply WeakAction.Equivariant.Hom.ext
    simp only [WeakAction.Equivariant.comp_hom, gauging_whiskerLeft_hom,
      gauging_whiskerRight_hom, equivariantBraiding_hom]
    change (α_ X.obj Y.obj Z.obj).hom ≫ (B.halfSwapIso X.obj (Y ⊗ Z)).hom ≫
      (α_ Y.obj Z.obj X.obj).hom = _
    rw [B.halfSwapIso_tensor_right]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]
    rfl
  hexagon_reverse X Y Z := by
    apply WeakAction.Equivariant.Hom.ext
    simp only [WeakAction.Equivariant.comp_hom, gauging_whiskerLeft_hom,
      gauging_whiskerRight_hom, equivariantBraiding_hom]
    change (α_ X.obj Y.obj Z.obj).inv ≫ (B.halfSwapIso (X.obj ⊗ Y.obj) Z).hom ≫
      (α_ Z.obj X.obj Y.obj).inv = _
    rw [B.halfSwapIso_tensor_left]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
    rfl

end Paper18.Category.CrossedBraidedGauging.CrossedBraiding
