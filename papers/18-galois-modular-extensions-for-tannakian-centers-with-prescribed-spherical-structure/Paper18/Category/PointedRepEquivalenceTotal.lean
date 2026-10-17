import Paper18.Category.PointedRigid
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-! # The actual total-vector functor of finite graded vector spaces -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
namespace Paper18.Category.PointedVec
variable {A : Type} [Fintype A] [AddGroup A]
open GradedObject.Monoidal

/-- Forget the grading by taking the actual finite biproduct of its fibers. -/
def totalFunctor : PointedVec A ⥤ FGModuleCat ℂ where
  obj X := ⨁ X
  map f := biproduct.map f
  map_id X := by ext a b; simp
  map_comp f g := by ext a b; simp [Category.assoc]

instance totalFunctor_additive : (totalFunctor (A := A)).Additive where
  map_add := by
    intro X Y f g
    change biproduct.map (fun a => f a + g a) = biproduct.map f + biproduct.map g
    apply biproduct.hom_ext'
    intro a
    apply biproduct.hom_ext
    intro b
    simp

instance totalFunctor_linear : (totalFunctor (A := A)).Linear ℂ where
  map_smul := by
    intro X Y f r
    change biproduct.map (fun a => r • f a) = r • biproduct.map f
    apply biproduct.hom_ext'
    intro a
    apply biproduct.hom_ext
    intro b
    simp

omit [AddGroup A] in
@[reassoc (attr := simp)]
lemma totalFunctor_ι_map {X Y : PointedVec A} (f : X ⟶ Y) (a : A) :
    biproduct.ι X a ≫ totalFunctor.map f = f a ≫ biproduct.ι Y a :=
  biproduct.ι_map f a

instance totalFunctor_faithful : (totalFunctor (A := A)).Faithful where
  map_injective {X Y} f g h := by
    funext a
    have hh := congrArg (fun k => biproduct.ι X a ≫ k ≫ biproduct.π Y a) h
    simpa [Category.assoc] using hh

/-- Tensor product distributes over the actual finite biproduct fibers. -/
def totalTensorHom (X Y : PointedVec A) :
    (⨁ X) ⊗ (⨁ Y) ⟶ ⨁ (tensorObj X Y) :=
  (rightDistributor X (⨁ Y)).hom ≫ biproduct.desc (fun a =>
    (leftDistributor (X a) Y).hom ≫ biproduct.desc (fun b =>
      ιTensorObj X Y a b (a + b) rfl ≫ biproduct.ι (tensorObj X Y) (a + b)))

@[reassoc (attr := simp)]
lemma totalTensorHom_ι (X Y : PointedVec A) (a b : A) :
    (biproduct.ι X a ⊗ₘ biproduct.ι Y b) ≫ totalTensorHom X Y =
      ιTensorObj X Y a b (a + b) rfl ≫ biproduct.ι (tensorObj X Y) (a + b) := by
  rw [tensorHom_def', totalTensorHom, Category.assoc]
  rw [biproduct_ι_comp_rightDistributor_hom_assoc, biproduct.ι_desc]
  rw [biproduct_ι_comp_leftDistributor_hom_assoc, biproduct.ι_desc]

omit [AddGroup A] in
/-- Homogeneous tensor inclusions jointly detect maps out of total tensors. -/
lemma totalTensor_hom_ext (X Y : PointedVec A) {W : FGModuleCat ℂ}
    (f g : (⨁ X) ⊗ (⨁ Y) ⟶ W)
    (h : ∀ a b, (biproduct.ι X a ⊗ₘ biproduct.ι Y b) ≫ f =
      (biproduct.ι X a ⊗ₘ biproduct.ι Y b) ≫ g) : f = g := by
  apply (cancel_epi (rightDistributor X (⨁ Y)).inv).mp
  apply biproduct.hom_ext'
  intro a
  simp only [biproduct_ι_comp_rightDistributor_inv_assoc]
  apply (cancel_epi (leftDistributor (X a) Y).inv).mp
  apply biproduct.hom_ext'
  intro b
  simp only [biproduct_ι_comp_leftDistributor_inv_assoc]
  simpa only [← tensorHom_def'_assoc] using h a b

/-- The inverse tensor comparison uses the actual convolution coproduct. -/
def totalTensorInv (X Y : PointedVec A) :
    (⨁ (tensorObj X Y)) ⟶ (⨁ X) ⊗ (⨁ Y) :=
  biproduct.desc (fun _ => tensorObjDesc
    (fun a b _ => biproduct.ι X a ⊗ₘ biproduct.ι Y b))

@[reassoc (attr := simp)]
lemma totalTensorInv_ι (X Y : PointedVec A) (a b k : A) (h : a + b = k) :
    ιTensorObj X Y a b k h ≫ biproduct.ι (tensorObj X Y) k ≫ totalTensorInv X Y =
      biproduct.ι X a ⊗ₘ biproduct.ι Y b := by
  simp [totalTensorInv]

/-- The actual strong tensor comparison for the total-vector functor. -/
def totalTensorIso (X Y : PointedVec A) :
    (⨁ X) ⊗ (⨁ Y) ≅ ⨁ (tensorObj X Y) where
  hom := totalTensorHom X Y
  inv := totalTensorInv X Y
  hom_inv_id := by
    apply totalTensor_hom_ext X Y
    intro a b
    simp only [Category.comp_id]
    erw [totalTensorHom_ι_assoc, totalTensorInv_ι]
  inv_hom_id := by
    apply biproduct.hom_ext'
    intro k
    apply tensorObj_ext
    intro a b h
    subst k
    simp only [Category.comp_id]
    erw [totalTensorInv_ι_assoc, totalTensorHom_ι]

/-- The total object of the grading unit is canonically the ordinary unit. -/
def totalUnitIso : 𝟙_ (FGModuleCat ℂ) ≅ ⨁ (𝟙_ (PointedVec A)) where
  hom := unitFiberIso.inv ≫ biproduct.ι (𝟙_ (PointedVec A)) 0
  inv := biproduct.π (𝟙_ (PointedVec A)) 0 ≫ unitFiberIso.hom
  hom_inv_id := by simp
  inv_hom_id := by
    apply biproduct.hom_ext'
    intro a
    by_cases ha : a = 0
    · subst a; simp
    · have hz : IsZero ((𝟙_ (PointedVec A)) a) :=
        (GradedObject.isInitialSingleObjApply 0 (𝟙_ (FGModuleCat ℂ)) a ha).isZero
      exact hz.eq_of_src _ _

lemma totalTensorHom_naturality {X X' Y Y' : PointedVec A}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (totalFunctor.map f ⊗ₘ totalFunctor.map g) ≫ totalTensorHom X' Y' =
      totalTensorHom X Y ≫ totalFunctor.map (f ⊗ₘ g) := by
  apply totalTensor_hom_ext X Y
  intro a b
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc, totalFunctor_ι_map, totalFunctor_ι_map,
    ← MonoidalCategory.tensorHom_comp_tensorHom_assoc, totalTensorHom_ι]
  rw [totalTensorHom_ι_assoc, totalFunctor_ι_map]
  change _ = ιTensorObj X Y a b (a + b) rfl ≫
    GradedObject.Monoidal.tensorHom f g (a + b) ≫
      biproduct.ι (tensorObj X' Y') (a + b)
  rw [ι_tensorHom_assoc]

omit [AddGroup A] in
/-- A finite homogeneous resolution also detects maps out of triple tensors. -/
lemma totalTriple_hom_ext (X Y Z : PointedVec A) {W : FGModuleCat ℂ}
    (f g : ((⨁ X) ⊗ (⨁ Y)) ⊗ (⨁ Z) ⟶ W)
    (h : ∀ a b c,
      ((biproduct.ι X a ⊗ₘ biproduct.ι Y b) ⊗ₘ biproduct.ι Z c) ≫ f =
      ((biproduct.ι X a ⊗ₘ biproduct.ι Y b) ⊗ₘ biproduct.ι Z c) ≫ g) : f = g := by
  have hr (m : ((⨁ X) ⊗ (⨁ Y)) ⊗ (⨁ Z) ⟶ W) :
      ∑ a, ∑ b, ∑ c,
        ((biproduct.π X a ⊗ₘ biproduct.π Y b) ⊗ₘ biproduct.π Z c) ≫
          (((biproduct.ι X a ⊗ₘ biproduct.ι Y b) ⊗ₘ biproduct.ι Z c) ≫ m) = m := by
    simp only [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [← Preadditive.sum_comp, ← CategoryTheory.tensor_sum,
      ← CategoryTheory.sum_tensor, biproduct.total, MonoidalCategory.id_tensorHom_id,
      Category.id_comp]
  rw [← hr f, ← hr g]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [h a b c]

end Paper18.Category.PointedVec
