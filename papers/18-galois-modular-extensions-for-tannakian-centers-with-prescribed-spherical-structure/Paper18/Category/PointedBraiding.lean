import Paper18.Category.PointedBasic

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Category
open Classical

namespace Paper18.Category

/-- A complex bicharacter, with nonzero values encoded as units. -/
structure ComplexBicharacter (A : Type) [AddCommGroup A] where
  val : A → A → ℂˣ
  add_left : ∀ a b c, val (a + b) c = val a c * val b c
  add_right : ∀ a b c, val a (b + c) = val a b * val a c

namespace PointedVec

variable {A : Type} [Fintype A] [AddCommGroup A]
  (c : ComplexBicharacter A)

open GradedObject.Monoidal

local instance : MonoidalCategory (GradedObject A (FGModuleCat ℂ)) :=
  GradedObject.monoidalCategory

/-- Braiding on actual convolution tensors, multiplying the ordinary flip on
the `(a,b)` homogeneous summand by the bicharacter value `c(a,b)`. -/
def bicharacterBraiding (X Y : PointedVec A) :
    GradedObject.Monoidal.tensorObj X Y ≅ GradedObject.Monoidal.tensorObj Y X where
  hom k := tensorObjDesc (fun i j hij =>
    (c.val i j : ℂ) • ((β_ (X i) (Y j)).hom ≫
      ιTensorObj Y X j i k (by simpa only [add_comm j i] using hij)))
  inv k := tensorObjDesc (fun i j hij =>
    (↑((c.val j i)⁻¹) : ℂ) • ((β_ (X j) (Y i)).inv ≫
      ιTensorObj X Y j i k (by simpa only [add_comm j i] using hij)))
  hom_inv_id := by
    apply GradedObject.hom_ext
    intro k
    apply tensorObj_ext
    intro i j h
    simp
  inv_hom_id := by
    apply GradedObject.hom_ext
    intro k
    apply tensorObj_ext
    intro i j h
    simp

@[reassoc (attr := simp)]
lemma inclusion_bicharacterBraiding (X Y : PointedVec A) (i j k : A) (h : i + j = k) :
    ιTensorObj X Y i j k h ≫ (bicharacterBraiding c X Y).hom k =
      (c.val i j : ℂ) • ((β_ (X i) (Y j)).hom ≫
        ιTensorObj Y X j i k (by simpa only [add_comm j i] using h)) := by
  simp [bicharacterBraiding]

lemma bicharacterBraiding_naturality_right
    (X : PointedVec A) {Y Z : PointedVec A} (f : Y ⟶ Z) :
    X ◁ f ≫ (bicharacterBraiding c X Z).hom =
      (bicharacterBraiding c X Y).hom ≫ f ▷ X := by
  apply GradedObject.hom_ext
  intro k
  apply tensorObj_ext
  intro i j h
  change ιTensorObj X Y i j k h ≫
      (GradedObject.Monoidal.whiskerLeft X f k ≫ (bicharacterBraiding c X Z).hom k) =
    ιTensorObj X Y i j k h ≫
      ((bicharacterBraiding c X Y).hom k ≫ GradedObject.Monoidal.whiskerRight f X k)
  simp
  have hn := BraidedCategory.braiding_naturality_right (C := FGModuleCat ℂ) (X i) (f j)
  simpa only [Category.assoc] using congrArg
    (fun t => (c.val i j : ℂ) • (t ≫ ιTensorObj Z X j i k (by simpa [add_comm] using h))) hn

lemma bicharacterBraiding_naturality_left
    {X Y : PointedVec A} (f : X ⟶ Y) (Z : PointedVec A) :
    f ▷ Z ≫ (bicharacterBraiding c Y Z).hom =
      (bicharacterBraiding c X Z).hom ≫ Z ◁ f := by
  apply GradedObject.hom_ext
  intro k
  apply tensorObj_ext
  intro i j h
  change ιTensorObj X Z i j k h ≫
      (GradedObject.Monoidal.whiskerRight f Z k ≫ (bicharacterBraiding c Y Z).hom k) =
    ιTensorObj X Z i j k h ≫
      ((bicharacterBraiding c X Z).hom k ≫ GradedObject.Monoidal.whiskerLeft Z f k)
  simp
  have hn := BraidedCategory.braiding_naturality_left (C := FGModuleCat ℂ) (f i) (Z j)
  simpa only [Category.assoc] using congrArg
    (fun t => (c.val i j : ℂ) • (t ≫ ιTensorObj Z Y j i k (by simpa [add_comm] using h))) hn

set_option maxHeartbeats 1000000 in
lemma bicharacter_hexagon_forward (X Y Z : PointedVec A) :
    (α_ X Y Z).hom ≫ (bicharacterBraiding c X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
      (bicharacterBraiding c X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫
        Y ◁ (bicharacterBraiding c X Z).hom := by
  apply GradedObject.hom_ext
  intro k
  apply tensorObj₃'_ext (X₁ := X) (X₂ := Y) (X₃ := Z)
  intro i₁ i₂ i₃ h
  change ιTensorObj₃' X Y Z i₁ i₂ i₃ k h ≫
      ((GradedObject.Monoidal.associator X Y Z).hom k ≫
        (bicharacterBraiding c X (GradedObject.Monoidal.tensorObj Y Z)).hom k ≫
        (GradedObject.Monoidal.associator Y Z X).hom k) =
    ιTensorObj₃' X Y Z i₁ i₂ i₃ k h ≫
      (GradedObject.Monoidal.whiskerRight (bicharacterBraiding c X Y).hom Z k ≫
        (GradedObject.Monoidal.associator Y X Z).hom k ≫
        GradedObject.Monoidal.whiskerLeft Y (bicharacterBraiding c X Z).hom k)
  conv_lhs =>
    rw [ιTensorObj₃'_associator_hom_assoc,
      ιTensorObj₃_eq X Y Z i₁ i₂ i₃ k h _ rfl,
      assoc, inclusion_bicharacterBraiding_assoc]
    simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc]
    rw [← MonoidalCategory.id_tensorHom,
      BraidedCategory.braiding_naturality_assoc,
      BraidedCategory.braiding_tensor_right_hom,
      assoc, assoc, assoc, assoc, Iso.hom_inv_id_assoc,
      MonoidalCategory.tensorHom_id,
      ← ιTensorObj₃'_eq_assoc Y Z X i₂ i₃ i₁ k
        (by rw [add_comm _ i₁, ← add_assoc, h]) _ rfl,
      ιTensorObj₃'_associator_hom, Iso.inv_hom_id_assoc]
  conv_rhs =>
    rw [ιTensorObj₃'_eq X Y Z i₁ i₂ i₃ k h _ rfl,
      assoc, ι_tensorHom_assoc, ← MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc, id_comp,
      inclusion_bicharacterBraiding]
    rw [GradedObject.categoryOfGradedObjects_id,
      MonoidalCategory.tensorHom_id, MonoidalLinear.smul_whiskerRight,
      Linear.smul_comp, MonoidalCategory.comp_whiskerRight, assoc,
      ← ιTensorObj₃'_eq_assoc Y X Z i₂ i₁ i₃ k
        (by rw [add_comm i₂ i₁, h]) (i₁ + i₂) (add_comm i₂ i₁),
      ιTensorObj₃'_associator_hom_assoc,
      ιTensorObj₃_eq Y X Z i₂ i₁ i₃ k (by rw [add_comm i₂ i₁, h]) _ rfl,
      assoc, ι_tensorHom,
      GradedObject.categoryOfGradedObjects_id,
      ← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom,
      ← MonoidalCategory.id_tensor_comp_assoc,
      inclusion_bicharacterBraiding]
    rw [MonoidalCategory.id_tensorHom, MonoidalLinear.whiskerLeft_smul,
      MonoidalCategory.whiskerLeft_comp]
    simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc]
    rw [← ιTensorObj₃_eq Y Z X i₂ i₃ i₁ k
      (by rw [add_comm _ i₁, ← add_assoc, h]) (i₁ + i₃) (add_comm _ _)]
    simp only [MonoidalLinear.whiskerLeft_smul, MonoidalLinear.smul_whiskerRight,
      Linear.smul_comp, Linear.comp_smul]
  rw [c.add_right]
  simp only [Units.val_mul, mul_smul, MonoidalCategory.tensorHom_id]

set_option maxHeartbeats 1000000 in
lemma bicharacter_hexagon_reverse (X Y Z : PointedVec A) :
    (α_ X Y Z).inv ≫ (bicharacterBraiding c (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
      X ◁ (bicharacterBraiding c Y Z).hom ≫ (α_ X Z Y).inv ≫
        (bicharacterBraiding c X Z).hom ▷ Y := by
  apply GradedObject.hom_ext
  intro k
  apply tensorObj₃_ext (X₁ := X) (X₂ := Y) (X₃ := Z)
  intro i₁ i₂ i₃ h
  change ιTensorObj₃ X Y Z i₁ i₂ i₃ k h ≫
      ((GradedObject.Monoidal.associator X Y Z).inv k ≫
        (bicharacterBraiding c (GradedObject.Monoidal.tensorObj X Y) Z).hom k ≫
        (GradedObject.Monoidal.associator Z X Y).inv k) =
    ιTensorObj₃ X Y Z i₁ i₂ i₃ k h ≫
      (GradedObject.Monoidal.whiskerLeft X (bicharacterBraiding c Y Z).hom k ≫
        (GradedObject.Monoidal.associator X Z Y).inv k ≫
        GradedObject.Monoidal.whiskerRight (bicharacterBraiding c X Z).hom Y k)
  conv_lhs =>
    rw [ιTensorObj₃_associator_inv_assoc,
      ιTensorObj₃'_eq X Y Z i₁ i₂ i₃ k h _ rfl,
      assoc, inclusion_bicharacterBraiding_assoc]
    simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc]
    rw [← MonoidalCategory.tensorHom_id,
      BraidedCategory.braiding_naturality_assoc,
      BraidedCategory.braiding_tensor_left_hom,
      assoc, assoc, assoc, assoc, Iso.inv_hom_id_assoc,
      MonoidalCategory.id_tensorHom,
      ← ιTensorObj₃_eq_assoc Z X Y i₃ i₁ i₂ k (by rw [add_assoc, add_comm i₃, h]) _ rfl,
      ιTensorObj₃_associator_inv, Iso.hom_inv_id_assoc]
  conv_rhs =>
    rw [ιTensorObj₃_eq X Y Z i₁ i₂ i₃ k h _ rfl,
      assoc, ι_tensorHom_assoc, ← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc, id_comp,
      inclusion_bicharacterBraiding,
      GradedObject.categoryOfGradedObjects_id,
      MonoidalCategory.id_tensorHom, MonoidalLinear.whiskerLeft_smul,
      Linear.smul_comp, MonoidalCategory.whiskerLeft_comp, assoc,
      ← ιTensorObj₃_eq_assoc X Z Y i₁ i₃ i₂ k
        (by rw [add_assoc, add_comm i₃, ← add_assoc, h]) (i₂ + i₃) (add_comm _ _),
      ιTensorObj₃_associator_inv_assoc,
      ιTensorObj₃'_eq X Z Y i₁ i₃ i₂ k (by rw [add_assoc, add_comm i₃, ← add_assoc, h]) _ rfl,
      assoc, ι_tensorHom, GradedObject.categoryOfGradedObjects_id,
      ← MonoidalCategory.id_tensorHom, ← MonoidalCategory.tensorHom_id,
      ← MonoidalCategory.comp_tensor_id_assoc,
      inclusion_bicharacterBraiding]
    rw [MonoidalCategory.tensorHom_id, MonoidalLinear.smul_whiskerRight,
      MonoidalCategory.comp_whiskerRight]
    simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc]
    rw [← ιTensorObj₃'_eq Z X Y i₃ i₁ i₂ k (by rw [add_assoc, add_comm i₃, h])
      (i₁ + i₃) (add_comm _ _)]
  rw [c.add_left]
  simp only [Units.val_mul, mul_smul, MonoidalCategory.id_tensorHom]
  rw [smul_comm]

/-- The bicharacter supplies a coherent braiding on the actual category of
finite-dimensional graded complex vector spaces. -/
def bicharacterBraidedCategory : BraidedCategory (PointedVec A) where
  braiding := bicharacterBraiding c
  braiding_naturality_right := bicharacterBraiding_naturality_right c
  braiding_naturality_left := bicharacterBraiding_naturality_left c
  hexagon_forward := bicharacter_hexagon_forward c
  hexagon_reverse := bicharacter_hexagon_reverse c

end PointedVec
end Paper18.Category
