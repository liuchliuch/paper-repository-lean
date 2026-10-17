import Paper18.Category.LinearTensorAdditive
import Mathlib.CategoryTheory.Monoidal.Linear

/-! # Sparse matrices indexed by equivalences -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u
namespace Paper18.Category.LinearMat
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A matrix supported on the graph of an equivalence of finite index types. -/
def indexEquivHom {X Y : Mat_ C} (e : X.ι ≃ Y.ι)
    (f : ∀ i, X.X i ⟶ Y.X (e i)) : X ⟶ Y := fun i j =>
  if h : e i = j then f i ≫ eqToHom (congrArg Y.X h) else 0

@[simp] lemma indexEquivHom_apply {X Y : Mat_ C} (e : X.ι ≃ Y.ι)
    (f : ∀ i, X.X i ⟶ Y.X (e i)) (i : X.ι) :
    indexEquivHom e f i (e i) = f i := by simp [indexEquivHom]

lemma indexEquivHom_apply_of_ne {X Y : Mat_ C} (e : X.ι ≃ Y.ι)
    (f : ∀ i, X.X i ⟶ Y.X (e i)) (i : X.ι) (j : Y.ι) (h : e i ≠ j) :
    indexEquivHom e f i j = 0 := by simp [indexEquivHom, h]

@[simp] lemma indexEquivHom_comp_apply {X Y Z : Mat_ C} (e : X.ι ≃ Y.ι)
    (f : ∀ i, X.X i ⟶ Y.X (e i)) (g : Y ⟶ Z) (i : X.ι) (k : Z.ι) :
    (indexEquivHom e f ≫ g) i k = f i ≫ g (e i) k := by
  simp [Mat_.comp_apply, indexEquivHom, dite_comp]

@[simp] lemma comp_indexEquivHom_apply {X Y Z : Mat_ C} (f : X ⟶ Y)
    (e : Y.ι ≃ Z.ι) (g : ∀ j, Y.X j ⟶ Z.X (e j)) (i : X.ι) (j : Y.ι) :
    (f ≫ indexEquivHom e g) i (e j) = f i j ≫ g j := by
  simp [Mat_.comp_apply, indexEquivHom, Equiv.apply_eq_iff_eq, comp_dite]

/-- Reindexing an actual finite family by actual component isomorphisms. -/
def indexEquivIso {X Y : Mat_ C} (e : X.ι ≃ Y.ι)
    (f : ∀ i, X.X i ≅ Y.X (e i)) : X ≅ Y where
  hom := indexEquivHom e (fun i => (f i).hom)
  inv j i := if h : e i = j then eqToHom (congrArg Y.X h.symm) ≫ (f i).inv else 0
  hom_inv_id := by
    ext i k
    rw [indexEquivHom_comp_apply]
    by_cases h : i = k
    · subst k
      simp
    · have h' : e k ≠ e i := fun he => h (e.injective he).symm
      simp [h', Mat_.id_apply, h]
  inv_hom_id := by
    ext j k
    obtain ⟨i, rfl⟩ := e.surjective j
    obtain ⟨l, rfl⟩ := e.surjective k
    rw [comp_indexEquivHom_apply]
    by_cases h : l = i
    · subst l
      simp
    · have h' : e l ≠ e i := fun he => h (e.injective he)
      have h'' : e i ≠ e l := Ne.symm h'
      simp [h', Mat_.id_apply, h'']

@[simp] lemma indexEquivIso_hom {X Y : Mat_ C} (e : X.ι ≃ Y.ι)
    (f : ∀ i, X.X i ≅ Y.X (e i)) :
    (indexEquivIso e f).hom = indexEquivHom e (fun i => (f i).hom) := rfl

lemma indexEquivHom_comp {X Y Z : Mat_ C} (e : X.ι ≃ Y.ι) (d : Y.ι ≃ Z.ι)
    (f : ∀ i, X.X i ⟶ Y.X (e i)) (g : ∀ j, Y.X j ⟶ Z.X (d j)) :
    indexEquivHom e f ≫ indexEquivHom d g =
      indexEquivHom (e.trans d) (fun i => f i ≫ g (e i)) := by
  ext i k
  rw [indexEquivHom_comp_apply]
  by_cases h : d (e i) = k
  · subst k
    simp [indexEquivHom]
  · simp [indexEquivHom, h]

@[simp] lemma indexEquivHom_refl (X : Mat_ C) :
    indexEquivHom (Equiv.refl X.ι) (fun i => 𝟙 (X.X i)) = 𝟙 X := by
  ext i j
  by_cases h : i = j
  · subst j; simp [indexEquivHom]
  · simp [indexEquivHom, Mat_.id_apply, h]

end Paper18.Category.LinearMat
