import Paper18.Category.LinearMatMonoidalBasic

/-! # The actual monoidal category of finite matrices -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u
namespace Paper18.Category.LinearMat
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C]

/-- Tensor objects have the product index set and componentwise tensor fibers. -/
abbrev tensorObject (X Y : Mat_ C) : Mat_ C := ⟨X.ι × Y.ι, fun p => X.X p.1 ⊗ Y.X p.2⟩

/-- The tensor product of matrices is their componentwise Kronecker tensor. -/
def tensorMap {X X' Y Y' : Mat_ C} (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorObject X Y ⟶ tensorObject X' Y' := fun p q => f p.1 q.1 ⊗ₘ g p.2 q.2

def associatorIso (X Y Z : Mat_ C) :
    tensorObject (tensorObject X Y) Z ≅ tensorObject X (tensorObject Y Z) :=
  indexEquivIso (Equiv.prodAssoc X.ι Y.ι Z.ι)
    (fun p => α_ (X.X p.1.1) (Y.X p.1.2) (Z.X p.2))

def leftUnitorIso (X : Mat_ C) : tensorObject ((Mat_.embedding C).obj (𝟙_ C)) X ≅ X :=
  indexEquivIso (Equiv.punitProd X.ι) (fun p => λ_ (X.X p.2))

def rightUnitorIso (X : Mat_ C) : tensorObject X ((Mat_.embedding C).obj (𝟙_ C)) ≅ X :=
  indexEquivIso (Equiv.prodPUnit X.ι) (fun p => ρ_ (X.X p.1))

abbrev monoidalStruct : MonoidalCategoryStruct (Mat_ C) where
  tensorObj := tensorObject
  tensorHom := tensorMap
  whiskerLeft X _ _ f := tensorMap (𝟙 X) f
  whiskerRight f X := tensorMap f (𝟙 X)
  tensorUnit := (Mat_.embedding C).obj (𝟙_ C)
  associator := associatorIso
  leftUnitor := leftUnitorIso
  rightUnitor := rightUnitorIso

attribute [local instance] monoidalStruct

@[simp] lemma tensorMap_apply {X X' Y Y' : Mat_ C} (f : X ⟶ X') (g : Y ⟶ Y')
    (p : X.ι × Y.ι) (q : X'.ι × Y'.ι) :
    (f ⊗ₘ g) p q = f p.1 q.1 ⊗ₘ g p.2 q.2 := rfl

lemma tensorMap_id (X Y : Mat_ C) : (𝟙 X) ⊗ₘ (𝟙 Y) = 𝟙 (X ⊗ Y) := by
  ext ⟨i,k⟩ ⟨j,l⟩
  change (𝟙 X) i j ⊗ₘ (𝟙 Y) k l = (𝟙 (tensorObject X Y)) (i,k) (j,l)
  by_cases h : i = j
  · subst j
    by_cases h' : k = l
    · subst l; simp
    · have hp : (i,k) ≠ (i,l) := fun he => h' (congrArg Prod.snd he)
      rw [Mat_.id_apply_of_ne (tensorObject X Y) _ _ hp, Mat_.id_apply_of_ne _ _ _ h']
      simp
  · have hp : (i,k) ≠ (j,l) := fun he => h (congrArg Prod.fst he)
    rw [Mat_.id_apply_of_ne (tensorObject X Y) _ _ hp, Mat_.id_apply_of_ne _ _ _ h]
    simp

lemma tensorMap_comp {X Y Z X' Y' Z' : Mat_ C}
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : Y ⟶ Z) (k : Y' ⟶ Z') :
    (f ⊗ₘ g) ≫ (h ⊗ₘ k) = (f ≫ h) ⊗ₘ (g ≫ k) := by
  ext ⟨i,i'⟩ ⟨j,j'⟩
  change (∑ p : Y.ι × Y'.ι, (f i p.1 ⊗ₘ g i' p.2) ≫
    (h p.1 j ⊗ₘ k p.2 j')) =
    (∑ l, f i l ≫ h l j) ⊗ₘ (∑ l, g i' l ≫ k l j')
  simp only [MonoidalCategory.tensorHom_comp_tensorHom, Fintype.sum_prod_type,
    sum_tensor, tensor_sum]
  rw [Finset.sum_comm]

lemma tensorMap_indexEquivHom {X X' Y Y' : Mat_ C}
    (e : X.ι ≃ X'.ι) (d : Y.ι ≃ Y'.ι)
    (f : ∀ i, X.X i ⟶ X'.X (e i)) (g : ∀ i, Y.X i ⟶ Y'.X (d i)) :
    (indexEquivHom e f) ⊗ₘ (indexEquivHom d g) =
      indexEquivHom (X := tensorObject X Y) (Y := tensorObject X' Y')
        (e.prodCongr d) (fun p => f p.1 ⊗ₘ g p.2) := by
  ext ⟨i,k⟩ ⟨j,l⟩
  by_cases h : e i = j
  · subst j
    by_cases h' : d k = l
    · subst l; simp [indexEquivHom]
    · simp [indexEquivHom, h', Prod.mk.injEq]
  · simp [indexEquivHom, h, Prod.mk.injEq]

@[simp] lemma associator_hom (X Y Z : Mat_ C) :
    (α_ X Y Z).hom = indexEquivHom
      (X := tensorObject (tensorObject X Y) Z) (Y := tensorObject X (tensorObject Y Z))
      (Equiv.prodAssoc X.ι Y.ι Z.ι)
      (fun p => (α_ (X.X p.1.1) (Y.X p.1.2) (Z.X p.2)).hom) := rfl

@[simp] lemma leftUnitor_hom (X : Mat_ C) :
    (λ_ X).hom = indexEquivHom
      (X := tensorObject ((Mat_.embedding C).obj (𝟙_ C)) X) (Y := X)
      (Equiv.punitProd X.ι)
      (fun p => (λ_ (X.X p.2)).hom) := rfl

@[simp] lemma rightUnitor_hom (X : Mat_ C) :
    (ρ_ X).hom = indexEquivHom
      (X := tensorObject X ((Mat_.embedding C).obj (𝟙_ C))) (Y := X)
      (Equiv.prodPUnit X.ι)
      (fun p => (ρ_ (X.X p.1)).hom) := rfl


lemma associator_natural {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Mat_ C}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (h : X₃ ⟶ Y₃) :
    ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ Y₁ Y₂ Y₃).hom =
      (α_ X₁ X₂ X₃).hom ≫ (f ⊗ₘ (g ⊗ₘ h)) := by
  rw [associator_hom, associator_hom]
  ext ⟨⟨i,j⟩,k⟩ ⟨l,⟨m,n⟩⟩
  have hl := comp_indexEquivHom_apply
    (X := tensorObject (tensorObject X₁ X₂) X₃)
    (Y := tensorObject (tensorObject Y₁ Y₂) Y₃)
    (Z := tensorObject Y₁ (tensorObject Y₂ Y₃))
    (((f ⊗ₘ g) ⊗ₘ h)) (Equiv.prodAssoc Y₁.ι Y₂.ι Y₃.ι)
    (fun p => (α_ (Y₁.X p.1.1) (Y₂.X p.1.2) (Y₃.X p.2)).hom)
    ((i,j),k) ((l,m),n)
  erw [hl, indexEquivHom_comp_apply]
  exact MonoidalCategory.associator_naturality (f i l) (g j m) (h k n)

lemma leftUnitor_natural {X Y : Mat_ C} (f : X ⟶ Y) :
    ((𝟙 (𝟙_ (Mat_ C))) ⊗ₘ f) ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
  ext ⟨⟨⟩,i⟩ j
  rw [leftUnitor_hom, leftUnitor_hom]
  erw [comp_indexEquivHom_apply ((𝟙 (𝟙_ (Mat_ C))) ⊗ₘ f) (Equiv.punitProd Y.ι) _ (PUnit.unit,i) (PUnit.unit,j), indexEquivHom_comp_apply]
  simp only [tensorMap_apply, Mat_.id_apply_self, MonoidalCategory.id_tensorHom]
  change (𝟙_ C) ◁ f i j ≫ (λ_ (Y.X j)).hom = (λ_ (X.X i)).hom ≫ f i j
  exact MonoidalCategory.leftUnitor_naturality (f i j)

lemma rightUnitor_natural {X Y : Mat_ C} (f : X ⟶ Y) :
    (f ⊗ₘ (𝟙 (𝟙_ (Mat_ C)))) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
  ext ⟨i,⟨⟩⟩ j
  rw [rightUnitor_hom, rightUnitor_hom]
  erw [comp_indexEquivHom_apply (f ⊗ₘ (𝟙 (𝟙_ (Mat_ C)))) (Equiv.prodPUnit Y.ι) _ (i,PUnit.unit) (j,PUnit.unit), indexEquivHom_comp_apply]
  simp only [tensorMap_apply, Mat_.id_apply_self, MonoidalCategory.tensorHom_id]
  change f i j ▷ (𝟙_ C) ≫ (ρ_ (Y.X j)).hom = (ρ_ (X.X i)).hom ≫ f i j
  exact MonoidalCategory.rightUnitor_naturality (f i j)

lemma pentagon (W X Y Z : Mat_ C) :
    ((α_ W X Y).hom ⊗ₘ 𝟙 Z) ≫ (α_ W (X ⊗ Y) Z).hom ≫
      (𝟙 W ⊗ₘ (α_ X Y Z).hom) =
      (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := by
  rw [← indexEquivHom_refl Z, ← indexEquivHom_refl W]
  simp only [associator_hom, tensorMap_indexEquivHom, indexEquivHom_comp]
  congr 1
  funext p
  simpa only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] using
      MonoidalCategory.pentagon (W.X p.1.1.1) (X.X p.1.1.2) (Y.X p.1.2) (Z.X p.2)

lemma triangle (X Y : Mat_ C) :
    (α_ X (𝟙_ (Mat_ C)) Y).hom ≫ (𝟙 X ⊗ₘ (λ_ Y).hom) =
      (ρ_ X).hom ⊗ₘ 𝟙 Y := by
  rw [← indexEquivHom_refl X, ← indexEquivHom_refl Y]
  simp only [associator_hom, leftUnitor_hom, rightUnitor_hom,
    tensorMap_indexEquivHom, indexEquivHom_comp]
  congr 1
  funext p
  simpa only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] using
      MonoidalCategory.triangle (X.X p.1.1) (Y.X p.2)

instance monoidalCategory : MonoidalCategory (Mat_ C) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := tensorMap_id)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := tensorMap_comp)
    (associator_naturality := associator_natural)
    (leftUnitor_naturality := leftUnitor_natural)
    (rightUnitor_naturality := rightUnitor_natural)
    (pentagon := pentagon)
    (triangle := triangle)

@[simp] lemma tensor_index (X Y : Mat_ C) : (X ⊗ Y).ι = (X.ι × Y.ι) := rfl
@[simp] lemma tensor_fiber (X Y : Mat_ C) (p : X.ι × Y.ι) :
    (X ⊗ Y).X p = X.X p.1 ⊗ Y.X p.2 := rfl
@[simp] lemma unit_index : (𝟙_ (Mat_ C)).ι = PUnit := rfl
@[simp] lemma unit_fiber (p : (𝟙_ (Mat_ C)).ι) : (𝟙_ (Mat_ C)).X p = 𝟙_ C := rfl

@[simp] lemma whiskerLeft_apply (X : Mat_ C) {Y Z : Mat_ C} (f : Y ⟶ Z)
    (p : X.ι × Y.ι) (q : X.ι × Z.ι) :
    (X ◁ f) p q = (𝟙 X) p.1 q.1 ⊗ₘ f p.2 q.2 := rfl

@[simp] lemma whiskerRight_apply {X Y : Mat_ C} (f : X ⟶ Y) (Z : Mat_ C)
    (p : X.ι × Z.ι) (q : Y.ι × Z.ι) :
    (f ▷ Z) p q = f p.1 q.1 ⊗ₘ (𝟙 Z) p.2 q.2 := rfl

end Paper18.Category.LinearMat
