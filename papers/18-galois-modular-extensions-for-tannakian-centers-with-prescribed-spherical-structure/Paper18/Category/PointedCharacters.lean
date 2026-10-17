import Paper18.Category.PointedBasic
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical

namespace Paper18.Category.PointedVec

variable {A : Type} [Fintype A] [AddGroup A]

/-- Multiplication by a degree-dependent scalar is a genuine endomorphism
of each graded vector space. -/
def degreeMap (s : A → ℂ) (X : PointedVec A) : X ⟶ X := fun a => s a • 𝟙 (X a)

omit [Fintype A] [AddGroup A] in
@[simp] lemma degreeMap_apply (s : A → ℂ) (X : PointedVec A) (a : A) :
    degreeMap s X a = s a • 𝟙 (X a) := rfl

omit [Fintype A] [AddGroup A] in
lemma degreeMap_naturality (s : A → ℂ) {X Y : PointedVec A} (f : X ⟶ Y) :
    f ≫ degreeMap s Y = degreeMap s X ≫ f := by
  funext a
  simp [degreeMap]

/-- A nowhere-zero degree function acts by a natural automorphism on the
actual category of graded finite-dimensional vector spaces. -/
def degreeAutomorphism (s : A → ℂ) (hs : ∀ a, s a ≠ 0) :
    𝟭 (PointedVec A) ≅ 𝟭 (PointedVec A) where
  hom :=
    { app := degreeMap s
      naturality := fun {X Y} f => degreeMap_naturality s f }
  inv :=
    { app := degreeMap (fun a => (s a)⁻¹)
      naturality := fun {X Y} f => degreeMap_naturality _ f }
  hom_inv_id := by
    ext X
    funext a
    simp [degreeMap, ← mul_smul, hs]
  inv_hom_id := by
    ext X
    funext a
    simp [degreeMap, ← mul_smul, hs]

lemma scalar_tensor (X Y : FGModuleCat ℂ) (r s : ℂ) :
    (r • 𝟙 X) ⊗ₘ (s • 𝟙 Y) = (r * s) • 𝟙 (X ⊗ Y) := by
  rw [MonoidalCategory.tensorHom_def]
  simp [mul_smul]
  exact smul_comm s r _

/-- An additive character acts compatibly with the convolution tensor. -/
lemma characterMap_tensor (χ : AddChar A ℂ) (X Y : PointedVec A) :
    degreeMap χ (X ⊗ Y) = degreeMap χ X ⊗ₘ degreeMap χ Y := by
  apply GradedObject.hom_ext
  intro k
  apply GradedObject.Monoidal.tensorObj_ext
  intro i j h
  change GradedObject.Monoidal.ιTensorObj X Y i j k h ≫ degreeMap χ (X ⊗ Y) k =
    GradedObject.Monoidal.ιTensorObj X Y i j k h ≫
      GradedObject.Monoidal.tensorHom (degreeMap χ X) (degreeMap χ Y) k
  rw [GradedObject.Monoidal.ι_tensorHom]
  simp only [degreeMap_apply, scalar_tensor, Linear.comp_smul, Linear.smul_comp,
    Category.id_comp]
  subst k
  rw [χ.map_add_eq_mul]
  exact congrArg (fun t => (χ i * χ j) • t) (Category.comp_id _)

lemma characterMap_unit (χ : AddChar A ℂ) :
    degreeMap χ (𝟙_ (PointedVec A)) = 𝟙 (𝟙_ (PointedVec A)) := by
  funext a
  by_cases ha : a = 0
  · subst a
    simp [degreeMap]
  · have hz : IsZero ((𝟙_ (PointedVec A)) a) :=
      (GradedObject.isInitialSingleObjApply 0 (𝟙_ (FGModuleCat ℂ)) a ha).isZero
    exact hz.eq_of_src _ _

/-- The character automorphism supplies the genuine natural isomorphism used
to modify pivotal structures. -/
def characterAutomorphism (χ : AddChar A ℂ) : 𝟭 (PointedVec A) ≅ 𝟭 (PointedVec A) :=
  degreeAutomorphism χ (fun a => (χ.val_isUnit a).ne_zero)

instance characterAutomorphism_monoidal (χ : AddChar A ℂ) :
    (characterAutomorphism χ).hom.IsMonoidal where
  unit := by
    change 𝟙 _ ≫ degreeMap χ (𝟙_ (PointedVec A)) = 𝟙 _
    rw [Category.id_comp, characterMap_unit]
  tensor X Y := by
    change 𝟙 _ ≫ degreeMap χ (X ⊗ Y) =
      (degreeMap χ X ⊗ₘ degreeMap χ Y) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id, characterMap_tensor]

omit [Fintype A] [AddGroup A] in
lemma degreeMap_on_simple (s : A → ℂ) (a : A) :
    (GradedObject.singleObjApplyIso a (FGModuleCat.of ℂ ℂ)).inv ≫
        degreeMap s (simpleObject A a) a ≫
        (GradedObject.singleObjApplyIso a (FGModuleCat.of ℂ ℂ)).hom =
      s a • 𝟙 (FGModuleCat.of ℂ ℂ) := by
  simp only [degreeMap, Linear.comp_smul, Linear.smul_comp]
  let e := GradedObject.singleObjApplyIso a (FGModuleCat.of ℂ ℂ)
  have hm : e.inv ≫ 𝟙 ((simpleObject A a) a) ≫ e.hom = e.inv ≫ e.hom :=
    congrArg (fun f => e.inv ≫ f) (Category.id_comp e.hom)
  exact congrArg (fun f => s a • f) (hm.trans e.inv_hom_id)

omit [Fintype A] [AddGroup A] in
lemma degreeMap_simple_injective (s t : A → ℂ) (a : A)
    (h : degreeMap s (simpleObject A a) = degreeMap t (simpleObject A a)) : s a = t a := by
  have hh := congrArg (fun f =>
    (GradedObject.singleObjApplyIso a (FGModuleCat.of ℂ ℂ)).inv ≫ f ≫
      (GradedObject.singleObjApplyIso a (FGModuleCat.of ℂ ℂ)).hom) (congrFun h a)
  dsimp only at hh
  rw [degreeMap_on_simple, degreeMap_on_simple] at hh
  have hval := congrArg (fun f : End (FGModuleCat.of ℂ ℂ) => f.hom 1) hh
  change s a * 1 = t a * 1 at hval
  simpa using hval

end Paper18.Category.PointedVec
