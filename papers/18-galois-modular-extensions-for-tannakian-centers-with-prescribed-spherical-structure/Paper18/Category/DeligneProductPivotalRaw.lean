import Paper18.Category.LinearTensorBraided
import Paper18.Category.LinearTensorRigid
import Paper18.Category.PivotalBalancing
import Paper18.Category.PivotalBalancingDimensions

/-! # Actual componentwise balancing on the linear tensor category -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped TensorProduct
universe v u v' u'
namespace Paper18.Category.LinearTensor
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [BraidedCategory D]

lemma whiskerLeft_tmul (X : LinearTensor C D) {Y Z : LinearTensor C D}
    (f : Y.left ⟶ Z.left) (g : Y.right ⟶ Z.right) :
    X ◁ (show Y ⟶ Z from f ⊗ₜ[ℂ] g) =
      (show X ⊗ Y ⟶ X ⊗ Z from (X.left ◁ f) ⊗ₜ[ℂ] (X.right ◁ g)) := by
  simpa only [MonoidalCategory.id_tensorHom] using
    tensorLinear_tmul X Y X Z (𝟙 X.left) (𝟙 X.right) f g

lemma whiskerRight_tmul {X Y : LinearTensor C D}
    (f : X.left ⟶ Y.left) (g : X.right ⟶ Y.right) (Z : LinearTensor C D) :
    (show X ⟶ Y from f ⊗ₜ[ℂ] g) ▷ Z =
      (show X ⊗ Z ⟶ Y ⊗ Z from (f ▷ Z.left) ⊗ₜ[ℂ] (g ▷ Z.right)) := by
  simpa only [MonoidalCategory.tensorHom_id] using
    tensorLinear_tmul X Z Y Z f g (𝟙 Z.left) (𝟙 Z.right)

lemma comp_tmul {X Y Z : LinearTensor C D}
    (f : X.left ⟶ Y.left) (g : X.right ⟶ Y.right)
    (h : Y.left ⟶ Z.left) (k : Y.right ⟶ Z.right) :
    (show X ⟶ Y from f ⊗ₜ[ℂ] g) ≫ (show Y ⟶ Z from h ⊗ₜ[ℂ] k) =
      (show X ⟶ Z from (f ≫ h) ⊗ₜ[ℂ] (g ≫ k)) :=
  compLinear_tmul X Y Z f g h k

lemma evaluation_raw (X : LinearTensor C D) :
    (ε_ X (dual (LinearTensor C D) X)) =
      (ε_ X.left (dual C X.left)) ⊗ₜ[ℂ] (ε_ X.right (dual D X.right)) := rfl

/-- Chosen duality sends an actual pure tensor to the pure tensor of
the actual rigid mates. -/
lemma dualMap_tmul {X Y : LinearTensor C D}
    (f : X.left ⟶ Y.left) (g : X.right ⟶ Y.right) :
    dualMap (LinearTensor C D) (f ⊗ₜ[ℂ] g) =
      (dualMap C f) ⊗ₜ[ℂ] (dualMap D g) := by
  apply pairing_hom_ext (inferInstanceAs (ExactPairing X (dual (LinearTensor C D) X)))
  rw [rightAdjointMate_comp_evaluation]
  rw [whiskerLeft_tmul (dual (LinearTensor C D) Y) (Y := X) (Z := Y),
    whiskerRight_tmul (X := dual (LinearTensor C D) Y)
      (Y := dual (LinearTensor C D) X), evaluation_raw, evaluation_raw]
  rw [comp_tmul (X := dual (LinearTensor C D) Y ⊗ X)
      (Y := dual (LinearTensor C D) Y ⊗ Y) (Z := 𝟙_ (LinearTensor C D)),
    comp_tmul (X := dual (LinearTensor C D) Y ⊗ X)
      (Y := dual (LinearTensor C D) X ⊗ X) (Z := 𝟙_ (LinearTensor C D))]
  change ((Y.leftᘁ ◁ f) ≫ ε_ Y.left Y.leftᘁ) ⊗ₜ[ℂ]
      ((Y.rightᘁ ◁ g) ≫ ε_ Y.right Y.rightᘁ) =
    ((dualMap C f ▷ X.left) ≫ ε_ X.left X.leftᘁ) ⊗ₜ[ℂ]
      ((dualMap D g ▷ X.right) ≫ ε_ X.right X.rightᘁ)
  exact congrArg₂ (TensorProduct.tmul ℂ)
    (rightAdjointMate_comp_evaluation f).symm
    (rightAdjointMate_comp_evaluation g).symm

variable (J : PivotalStructure C) (K : PivotalStructure D)

def productTwist : 𝟭 (LinearTensor C D) ≅ 𝟭 (LinearTensor C D) :=
  NatIso.ofComponents (fun X => isoOfPair (J.twistIso X.left) (K.twistIso X.right))
    (fun {X Y} f => by
      change f ≫ (isoOfPair (J.twistIso Y.left) (K.twistIso Y.right)).hom =
        (isoOfPair (J.twistIso X.left) (K.twistIso X.right)).hom ≫ f
      induction f using TensorProduct.induction_on with
      | zero => simp
      | tmul f g =>
        change (f ≫ (J.twistIso Y.left).hom) ⊗ₜ[ℂ]
            (g ≫ (K.twistIso Y.right).hom) =
          ((J.twistIso X.left).hom ≫ f) ⊗ₜ[ℂ] ((K.twistIso X.right).hom ≫ g)
        exact congrArg₂ (TensorProduct.tmul ℂ) (J.twist_naturality f) (K.twist_naturality g)
      | add f g hf hg =>
        exact (Preadditive.add_comp X Y Y f g _).trans
          ((congrArg₂ (fun a b => a + b) hf hg).trans (Preadditive.comp_add X X Y _ f g).symm))

lemma productTwist_unit : (productTwist J K).hom.app (𝟙_ (LinearTensor C D)) =
    𝟙 (𝟙_ (LinearTensor C D)) := by
  change (J.twistIso (𝟙_ C)).hom ⊗ₜ[ℂ] (K.twistIso (𝟙_ D)).hom =
    (𝟙 (𝟙_ C)) ⊗ₜ[ℂ] (𝟙 (𝟙_ D))
  rw [J.twist_unit, K.twist_unit]

lemma productTwist_tensor (X Y : LinearTensor C D) :
    (productTwist J K).hom.app (X ⊗ Y) =
      (doubleBraiding X Y).hom ≫
        ((productTwist J K).hom.app X ⊗ₘ (productTwist J K).hom.app Y) := by
  change (J.twistIso (X.left ⊗ Y.left)).hom ⊗ₜ[ℂ]
      (K.twistIso (X.right ⊗ Y.right)).hom =
    ((doubleBraiding X.left Y.left).hom ≫
      ((J.twistIso X.left).hom ⊗ₘ (J.twistIso Y.left).hom)) ⊗ₜ[ℂ]
    ((doubleBraiding X.right Y.right).hom ≫
      ((K.twistIso X.right).hom ⊗ₘ (K.twistIso Y.right).hom))
  exact congrArg₂ (TensorProduct.tmul ℂ) (J.twist_tensor X.left Y.left)
    (K.twist_tensor X.right Y.right)

/-- The actual pivotal structure is recovered from the actual balancing,
so the chosen dual tensor coherence is automatic. -/
def productPivotal : PivotalStructure (LinearTensor C D) :=
  pivotalOfBalancing (productTwist J K) (productTwist_unit J K) (productTwist_tensor J K)

@[simp] lemma productPivotal_twist : (productPivotal J K).twistNatIso = productTwist J K :=
  pivotalOfBalancing_twist _ _ _

lemma productTwist_dual (hJ : J.TwistSelfDual) (hK : K.TwistSelfDual)
    (X : LinearTensor C D) :
    (productTwist J K).hom.app (dual (LinearTensor C D) X) =
      dualMap (LinearTensor C D) ((productTwist J K).hom.app X) := by
  change (J.twistIso (dual C X.left)).hom ⊗ₜ[ℂ] (K.twistIso (dual D X.right)).hom =
    dualMap (LinearTensor C D) (show X ⟶ X from
      (J.twistIso X.left).hom ⊗ₜ[ℂ] (K.twistIso X.right).hom)
  rw [dualMap_tmul (X := X) (Y := X), hJ X.left, hK X.right]

end Paper18.Category.LinearTensor
