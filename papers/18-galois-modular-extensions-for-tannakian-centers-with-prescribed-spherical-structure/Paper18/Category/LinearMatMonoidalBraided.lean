import Paper18.Category.LinearMatMonoidalEmbedding
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # The actual braiding on the matrix additive envelope -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
universe v u
namespace Paper18.Category.LinearMat
variable {C : Type u} [Category.{v} C] [Preadditive C]

lemma indexEquivIso_inv {X Y : Mat_ C} (e : X.ι ≃ Y.ι)
    (f : ∀ i, X.X i ≅ Y.X (e i)) :
    (indexEquivIso e f).inv = indexEquivHom (X := Y) (Y := X) e.symm
      (fun j => eqToHom (congrArg Y.X (e.apply_symm_apply j).symm) ≫ (f (e.symm j)).inv) := by
  ext j i
  obtain ⟨k, rfl⟩ := e.surjective j
  by_cases h : k = i
  · subst i
    simp [indexEquivIso, indexEquivHom]
  · have he : e i ≠ e k := fun hi => h (e.injective hi).symm
    simp [indexEquivIso, indexEquivHom, h, he]

variable [MonoidalCategory C] [MonoidalPreadditive C]

@[simp] lemma associator_inv (X Y Z : Mat_ C) :
    (α_ X Y Z).inv = indexEquivHom
      (X := X ⊗ (Y ⊗ Z)) (Y := (X ⊗ Y) ⊗ Z)
      (Equiv.prodAssoc X.ι Y.ι Z.ι).symm
      (fun p => (α_ (X.X p.1) (Y.X p.2.1) (Z.X p.2.2)).inv) := by
  change (associatorIso X Y Z).inv = _
  rw [associatorIso, indexEquivIso_inv]
  congr 1
  funext p
  simp

variable [BraidedCategory C]

def braidingIso (X Y : Mat_ C) : X ⊗ Y ≅ Y ⊗ X :=
  indexEquivIso (Equiv.prodComm X.ι Y.ι) (fun p => β_ (X.X p.1) (Y.X p.2))

lemma braiding_natural {X X' Y Y' : Mat_ C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g) ≫ (braidingIso X' Y').hom = (braidingIso X Y).hom ≫ (g ⊗ₘ f) := by
  change (f ⊗ₘ g) ≫ indexEquivHom (X := X' ⊗ Y') (Y := Y' ⊗ X') (Equiv.prodComm X'.ι Y'.ι)
    (fun p => (β_ (X'.X p.1) (Y'.X p.2)).hom) = _
  ext ⟨i,j⟩ ⟨k,l⟩
  have hh := comp_indexEquivHom_apply (X := X ⊗ Y) (Y := X' ⊗ Y') (Z := Y' ⊗ X')
    (f ⊗ₘ g) (Equiv.prodComm X'.ι Y'.ι)
    (fun p => (β_ (X'.X p.1) (Y'.X p.2)).hom) (i,j) (l,k)
  erw [hh, indexEquivHom_comp_apply]
  exact BraidedCategory.braiding_naturality (f i l) (g j k)

lemma hexagon_forward (X Y Z : Mat_ C) :
    (α_ X Y Z).hom ≫ (braidingIso X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
      ((braidingIso X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ (braidingIso X Z).hom) := by
  simp only [← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom]
  rw [← indexEquivHom_refl Z, ← indexEquivHom_refl Y]
  simp only [associator_hom, braidingIso, indexEquivIso_hom,
    tensorMap_indexEquivHom, indexEquivHom_comp]
  congr 1
  funext p
  simpa only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] using
    BraidedCategory.hexagon_forward (X.X p.1.1) (Y.X p.1.2) (Z.X p.2)

lemma hexagon_reverse (X Y Z : Mat_ C) :
    (α_ X Y Z).inv ≫ (braidingIso (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
      (X ◁ (braidingIso Y Z).hom) ≫ (α_ X Z Y).inv ≫ ((braidingIso X Z).hom ▷ Y) := by
  simp only [← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom]
  rw [← indexEquivHom_refl X, ← indexEquivHom_refl Y]
  simp only [associator_inv, braidingIso, indexEquivIso_hom,
    tensorMap_indexEquivHom, indexEquivHom_comp]
  congr 1
  funext p
  simpa only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] using
    BraidedCategory.hexagon_reverse (X.X p.1) (Y.X p.2.1) (Z.X p.2.2)

instance braidedCategory : BraidedCategory (Mat_ C) where
  braiding := braidingIso
  braiding_naturality_right X _ _ f := by
    simpa only [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id] using
      braiding_natural (𝟙 X) f
  braiding_naturality_left f X := by
    simpa only [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id] using
      braiding_natural f (𝟙 X)
  hexagon_forward := hexagon_forward
  hexagon_reverse := hexagon_reverse

/-- The actual singleton strong monoidal embedding preserves the braiding. -/
instance embeddingBraided : (Mat_.embedding C).Braided where
  braided X Y := by
    change (embeddingTensorIso X Y).hom ≫ (Mat_.embedding C).map (β_ X Y).hom =
      (braidingIso ((Mat_.embedding C).obj X) ((Mat_.embedding C).obj Y)).hom ≫
        (embeddingTensorIso Y X).hom
    ext ⟨⟨⟩,⟨⟩⟩ ⟨⟩
    simp [embeddingTensorIso, Mat_.comp_apply, Mat_.embedding, braidingIso,
      indexEquivHom, Fintype.sum_prod_type]

end Paper18.Category.LinearMat
