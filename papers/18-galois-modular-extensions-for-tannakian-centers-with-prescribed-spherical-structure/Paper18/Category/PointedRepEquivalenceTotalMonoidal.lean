import Paper18.Category.PointedRepEquivalenceTotal

/-! # Coherent tensor structure of the actual total-vector functor -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
namespace Paper18.Category.PointedVec
variable {A : Type} [Fintype A] [AddGroup A]
open GradedObject.Monoidal

@[reassoc]
lemma totalTensorHom_ι_of_add (X Y : PointedVec A) (a b k : A) (h : a + b = k) :
    (biproduct.ι X a ⊗ₘ biproduct.ι Y b) ≫ totalTensorHom X Y =
      ιTensorObj X Y a b k h ≫ biproduct.ι (tensorObj X Y) k := by
  subst k
  exact totalTensorHom_ι X Y a b

set_option maxHeartbeats 800000 in
lemma totalTensorHom_associativity (X Y Z : PointedVec A) :
    totalTensorHom X Y ▷ (⨁ Z) ≫ totalTensorHom (X ⊗ Y) Z ≫
        totalFunctor.map (α_ X Y Z).hom =
      (α_ (⨁ X) (⨁ Y) (⨁ Z)).hom ≫ (⨁ X) ◁ totalTensorHom Y Z ≫
        totalTensorHom X (Y ⊗ Z) := by
  apply totalTriple_hom_ext X Y Z
  intro a b c
  conv_lhs =>
    rw [← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom_assoc]
    rw [Category.comp_id, totalTensorHom_ι]
    rw [← Category.id_comp (biproduct.ι Z c),
      ← MonoidalCategory.tensorHom_comp_tensorHom_assoc]
    erw [totalTensorHom_ι_assoc]
    rw [MonoidalCategory.tensorHom_id, totalFunctor_ι_map]
    change ιTensorObj X Y a b (a + b) rfl ▷ Z c ≫
      ιTensorObj (tensorObj X Y) Z (a + b) c ((a + b) + c) rfl ≫
      (GradedObject.Monoidal.associator X Y Z).hom ((a + b) + c) ≫
      biproduct.ι (tensorObj X (tensorObj Y Z)) ((a + b) + c)
    rw [← ιTensorObj₃'_eq_assoc X Y Z a b c ((a + b) + c) rfl (a + b) rfl,
      ιTensorObj₃'_associator_hom_assoc]
  conv_rhs =>
    rw [MonoidalCategory.associator_naturality_assoc]
    rw [← MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom_assoc]
    rw [Category.comp_id, totalTensorHom_ι]
    rw [← Category.id_comp (biproduct.ι X a),
      ← MonoidalCategory.tensorHom_comp_tensorHom_assoc]
    erw [totalTensorHom_ι_of_add X (Y ⊗ Z) a (b + c) ((a + b) + c)
      (add_assoc a b c).symm]
    rw [MonoidalCategory.id_tensorHom]
    erw [← ιTensorObj₃_eq_assoc X Y Z a b c ((a + b) + c) rfl (b + c) rfl]
  rfl

lemma totalTensorHom_left_unitality (X : PointedVec A) :
    (λ_ (⨁ X)).hom = (totalUnitIso (A := A)).hom ▷ (⨁ X) ≫
      totalTensorHom (𝟙_ (PointedVec A)) X ≫ totalFunctor.map (λ_ X).hom := by
  apply (cancel_epi (leftDistributor (𝟙_ (FGModuleCat ℂ)) X).inv).mp
  apply biproduct.hom_ext'
  intro a
  simp only [biproduct_ι_comp_leftDistributor_inv_assoc]
  change _ = (𝟙_ (FGModuleCat ℂ)) ◁ biproduct.ι X a ≫
    (unitFiberIso.inv ≫ biproduct.ι (𝟙_ (PointedVec A)) 0) ▷ (⨁ X) ≫ _
  rw [← MonoidalCategory.tensorHom_def'_assoc,
    ← Category.id_comp (biproduct.ι X a),
    ← MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    totalTensorHom_ι_of_add_assoc (𝟙_ (PointedVec A)) X 0 a a (zero_add a)]
  rw [MonoidalCategory.tensorHom_id, totalFunctor_ι_map]
  change _ = unitFiberIso.inv ▷ X a ≫
    ιTensorObj (𝟙_ (PointedVec A)) X 0 a a (zero_add a) ≫
      (GradedObject.Monoidal.leftUnitor X).hom a ≫ biproduct.ι X a
  rw [inclusion_leftUnitor_assoc, ← comp_whiskerRight_assoc, Iso.inv_hom_id,
    id_whiskerRight, Category.id_comp]
  exact leftUnitor_naturality (biproduct.ι X a)

lemma totalTensorHom_right_unitality (X : PointedVec A) :
    (ρ_ (⨁ X)).hom = (⨁ X) ◁ (totalUnitIso (A := A)).hom ≫
      totalTensorHom X (𝟙_ (PointedVec A)) ≫ totalFunctor.map (ρ_ X).hom := by
  apply (cancel_epi (rightDistributor X (𝟙_ (FGModuleCat ℂ))).inv).mp
  apply biproduct.hom_ext'
  intro a
  simp only [biproduct_ι_comp_rightDistributor_inv_assoc]
  change _ = biproduct.ι X a ▷ (𝟙_ (FGModuleCat ℂ)) ≫
    (⨁ X) ◁ (unitFiberIso.inv ≫ biproduct.ι (𝟙_ (PointedVec A)) 0) ≫ _
  rw [← MonoidalCategory.tensorHom_def_assoc,
    ← Category.id_comp (biproduct.ι X a),
    ← MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    totalTensorHom_ι_of_add_assoc X (𝟙_ (PointedVec A)) a 0 a (add_zero a)]
  rw [MonoidalCategory.id_tensorHom, totalFunctor_ι_map]
  change _ = X a ◁ unitFiberIso.inv ≫
    ιTensorObj X (𝟙_ (PointedVec A)) a 0 a (add_zero a) ≫
      (GradedObject.Monoidal.rightUnitor X).hom a ≫ biproduct.ι X a
  rw [inclusion_rightUnitor_assoc, ← whiskerLeft_comp_assoc, Iso.inv_hom_id,
    whiskerLeft_id, Category.id_comp]
  exact rightUnitor_naturality (biproduct.ι X a)

def totalFunctorCoreMonoidal : (totalFunctor (A := A)).CoreMonoidal where
  εIso := totalUnitIso
  μIso := totalTensorIso
  μIso_hom_natural_left f X := by
    simpa only [CategoryTheory.Functor.map_id, MonoidalCategory.tensorHom_id] using
      totalTensorHom_naturality f (𝟙 X)
  μIso_hom_natural_right X f := by
    simpa only [CategoryTheory.Functor.map_id, MonoidalCategory.id_tensorHom] using
      totalTensorHom_naturality (𝟙 X) f
  associativity := totalTensorHom_associativity
  left_unitality := totalTensorHom_left_unitality
  right_unitality := totalTensorHom_right_unitality

instance totalFunctor_monoidal : (totalFunctor (A := A)).Monoidal :=
  totalFunctorCoreMonoidal.toMonoidal

end Paper18.Category.PointedVec
