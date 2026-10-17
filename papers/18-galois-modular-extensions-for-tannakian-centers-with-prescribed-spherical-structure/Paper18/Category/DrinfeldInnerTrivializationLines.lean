import Paper18.Category.PointedSkeleton
import Mathlib.CategoryTheory.Monoidal.Center

/-! # Actual convolution coordinates for crossing a homogeneous line -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits GradedObject.Monoidal
namespace Paper18.Category.DrinfeldInner
open PointedVec
variable {A : Type} [Fintype A] [AddGroup A]

/-- Projection onto the sole supported convolution summand of `X ⊗ δₖ`. -/
def rightLineProjection (X : PointedVec A) (k s : A) :
    (X ⊗ simpleObject A k) s ⟶ X (s - k) :=
  tensorObjDesc (fun a b h => if hb : b = k then by
    subst b
    exact X a ◁ (simpleFiberIso A k).hom ≫ (ρ_ (X a)).hom ≫
      eqToHom (congrArg X (by rw [← h]; simp))
    else 0)

/-- Inclusion of the sole supported convolution summand of `X ⊗ δₖ`. -/
def rightLineInclusion (X : PointedVec A) (k s : A) :
    X (s - k) ⟶ (X ⊗ simpleObject A k) s :=
  (ρ_ (X (s - k))).inv ≫ X (s - k) ◁ (simpleFiberIso A k).inv ≫
    tensorInclusion A X (simpleObject A k) (s - k) k s (sub_add_cancel s k)

@[reassoc (attr := simp)]
lemma inclusion_rightLineProjection (X : PointedVec A) (k s a : A) (h : a + k = s) :
    tensorInclusion A X (simpleObject A k) a k s h ≫ rightLineProjection X k s =
      X a ◁ (simpleFiberIso A k).hom ≫ (ρ_ (X a)).hom ≫
        eqToHom (congrArg X (by rw [← h]; simp)) := by
  simp [rightLineProjection, tensorInclusion]

lemma rightLineInclusion_projection (X : PointedVec A) (k s : A) :
    rightLineInclusion X k s ≫ rightLineProjection X k s = 𝟙 _ := by
  simp only [rightLineInclusion, Category.assoc, inclusion_rightLineProjection,
    eqToHom_refl, comp_id]
  rw [← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, id_comp,
    Iso.inv_hom_id]

lemma rightLineProjection_inclusion (X : PointedVec A) (k s : A) :
    rightLineProjection X k s ≫ rightLineInclusion X k s = 𝟙 _ := by
  apply tensor_hom_ext A X (simpleObject A k)
  intro a b h
  by_cases hb : b = k
  · subst b
    have ha : a = s - k := by rw [← h]; simp
    subst a
    simp only [rightLineInclusion, Category.assoc, inclusion_rightLineProjection_assoc,
      eqToHom_refl, id_comp, comp_id]
    rw [Iso.hom_inv_id_assoc, ← whiskerLeft_comp_assoc, Iso.hom_inv_id,
      whiskerLeft_id, id_comp]
  · exact ((tensorLeft (X a)).map_isZero (simpleFiber_isZero A k b hb)).eq_of_src _ _

/-- The actual right tensor-by-line convolution fiber is the shifted original fiber. -/
def rightLineFiberIso (X : PointedVec A) (k s : A) :
    (X ⊗ simpleObject A k) s ≅ X (s - k) where
  hom := rightLineProjection X k s
  inv := rightLineInclusion X k s
  hom_inv_id := rightLineProjection_inclusion X k s
  inv_hom_id := rightLineInclusion_projection X k s

/-- Projection onto the sole supported convolution summand of `δₖ ⊗ X`. -/
def leftLineProjection (X : PointedVec A) (k s : A) :
    (simpleObject A k ⊗ X) s ⟶ X (-k + s) :=
  tensorObjDesc (fun a b h => if ha : a = k then by
    subst a
    exact (simpleFiberIso A k).hom ▷ X b ≫ (λ_ (X b)).hom ≫
      eqToHom (congrArg X (by rw [← h]; simp))
    else 0)

def leftLineInclusion (X : PointedVec A) (k s : A) :
    X (-k + s) ⟶ (simpleObject A k ⊗ X) s :=
  (λ_ (X (-k + s))).inv ≫ (simpleFiberIso A k).inv ▷ X (-k + s) ≫
    tensorInclusion A (simpleObject A k) X k (-k + s) s (by simp)

@[reassoc (attr := simp)]
lemma inclusion_leftLineProjection (X : PointedVec A) (k s b : A) (h : k + b = s) :
    tensorInclusion A (simpleObject A k) X k b s h ≫ leftLineProjection X k s =
      (simpleFiberIso A k).hom ▷ X b ≫ (λ_ (X b)).hom ≫
        eqToHom (congrArg X (by rw [← h]; simp)) := by
  simp [leftLineProjection, tensorInclusion]

lemma leftLineInclusion_projection (X : PointedVec A) (k s : A) :
    leftLineInclusion X k s ≫ leftLineProjection X k s = 𝟙 _ := by
  simp only [leftLineInclusion, Category.assoc, inclusion_leftLineProjection,
    eqToHom_refl, comp_id]
  rw [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, id_comp,
    Iso.inv_hom_id]

lemma leftLineProjection_inclusion (X : PointedVec A) (k s : A) :
    leftLineProjection X k s ≫ leftLineInclusion X k s = 𝟙 _ := by
  apply tensor_hom_ext A (simpleObject A k) X
  intro a b h
  by_cases ha : a = k
  · subst a
    have hb : b = -k + s := by rw [← h]; simp
    subst b
    simp only [leftLineInclusion, Category.assoc, inclusion_leftLineProjection_assoc,
      eqToHom_refl, id_comp, comp_id]
    rw [Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc, Iso.hom_inv_id,
      id_whiskerRight, id_comp]
  · exact ((tensorRight (X b)).map_isZero (simpleFiber_isZero A k a ha)).eq_of_src _ _

def leftLineFiberIso (X : PointedVec A) (k s : A) :
    (simpleObject A k ⊗ X) s ≅ X (-k + s) where
  hom := leftLineProjection X k s
  inv := leftLineInclusion X k s
  hom_inv_id := leftLineProjection_inclusion X k s
  inv_hom_id := leftLineInclusion_projection X k s

@[reassoc]
lemma rightLineProjection_naturality {X Y : PointedVec A} (f : X ⟶ Y) (k s : A) :
    GradedObject.Monoidal.tensorHom f (𝟙 (simpleObject A k)) s ≫ rightLineProjection Y k s =
      rightLineProjection X k s ≫ f (s - k) := by
  apply tensor_hom_ext A X (simpleObject A k)
  intro a b h
  by_cases hb : b = k
  · subst b
    have ha : a = s - k := by rw [← h]; simp
    subst a
    change ιTensorObj X (simpleObject A k) (s-k) k s h ≫
      GradedObject.Monoidal.tensorHom f (𝟙 (simpleObject A k)) s ≫
        rightLineProjection Y k s =
      ιTensorObj X (simpleObject A k) (s-k) k s h ≫ rightLineProjection X k s ≫ f (s-k)
    rw [ι_tensorHom_assoc]
    erw [inclusion_rightLineProjection,
      inclusion_rightLineProjection_assoc]
    simp only [eqToHom_refl, comp_id, PointedVec.id_apply, MonoidalCategory.tensorHom_id]
    rw [← whisker_exchange_assoc]
    erw [MonoidalCategory.rightUnitor_naturality]
    simp only [id_comp]
  · exact ((tensorLeft (X a)).map_isZero (simpleFiber_isZero A k b hb)).eq_of_src _ _

@[reassoc]
lemma leftLineProjection_naturality {X Y : PointedVec A} (f : X ⟶ Y) (k s : A) :
    GradedObject.Monoidal.tensorHom (𝟙 (simpleObject A k)) f s ≫ leftLineProjection Y k s =
      leftLineProjection X k s ≫ f (-k + s) := by
  apply tensor_hom_ext A (simpleObject A k) X
  intro a b h
  by_cases ha : a = k
  · subst a
    have hb : b = -k + s := by rw [← h]; simp
    subst b
    change ιTensorObj (simpleObject A k) X k (-k+s) s h ≫
      GradedObject.Monoidal.tensorHom (𝟙 (simpleObject A k)) f s ≫
        leftLineProjection Y k s =
      ιTensorObj (simpleObject A k) X k (-k+s) s h ≫ leftLineProjection X k s ≫ f (-k+s)
    rw [ι_tensorHom_assoc]
    erw [inclusion_leftLineProjection,
      inclusion_leftLineProjection_assoc]
    simp only [eqToHom_refl, comp_id, PointedVec.id_apply, MonoidalCategory.id_tensorHom]
    rw [whisker_exchange_assoc]
    erw [MonoidalCategory.leftUnitor_naturality]
    simp only [id_comp]
  · exact ((tensorRight (X b)).map_isZero (simpleFiber_isZero A k a ha)).eq_of_src _ _

@[reassoc]
lemma rightLineInclusion_naturality {X Y : PointedVec A} (f : X ⟶ Y) (k s : A) :
    f (s - k) ≫ rightLineInclusion Y k s =
      rightLineInclusion X k s ≫ GradedObject.Monoidal.tensorHom f (𝟙 (simpleObject A k)) s := by
  apply (cancel_mono (rightLineFiberIso Y k s).hom).mp
  change (_ ≫ _) ≫ rightLineProjection Y k s = (_ ≫ _) ≫ rightLineProjection Y k s
  rw [Category.assoc, rightLineInclusion_projection, comp_id, Category.assoc,
    rightLineProjection_naturality, ← Category.assoc, rightLineInclusion_projection, id_comp]

@[reassoc]
lemma leftLineInclusion_naturality {X Y : PointedVec A} (f : X ⟶ Y) (k s : A) :
    f (-k + s) ≫ leftLineInclusion Y k s =
      leftLineInclusion X k s ≫ GradedObject.Monoidal.tensorHom (𝟙 (simpleObject A k)) f s := by
  apply (cancel_mono (leftLineFiberIso Y k s).hom).mp
  change (_ ≫ _) ≫ leftLineProjection Y k s = (_ ≫ _) ≫ leftLineProjection Y k s
  rw [Category.assoc, leftLineInclusion_projection, comp_id, Category.assoc,
    leftLineProjection_naturality, ← Category.assoc, leftLineInclusion_projection, id_comp]

end Paper18.Category.DrinfeldInner
