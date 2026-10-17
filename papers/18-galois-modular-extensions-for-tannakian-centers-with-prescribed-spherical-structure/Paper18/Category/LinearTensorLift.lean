import Paper18.Category.LinearTensorBasic
import Mathlib.CategoryTheory.Linear.FunctorCategory

/-! # Extending bilinear functors over actual tensor-product Hom spaces -/
noncomputable section
open CategoryTheory
open scoped TensorProduct
universe v u v' u' v'' u''
namespace Paper18.Category.LinearTensor
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  {E : Type u''} [Category.{v''} E] [Preadditive E] [Linear ℂ E]
  (F : C ⥤ D ⥤ E) [F.Additive] [F.Linear ℂ]
  [∀ X : C, (F.obj X).Additive] [∀ X : C, (F.obj X).Linear ℂ]

/-- The actual bilinear map underlying a separately linear bifunctor. -/
def liftHomBilinear (X Y : LinearTensor C D) :
    (X.left ⟶ Y.left) →ₗ[ℂ] (X.right ⟶ Y.right) →ₗ[ℂ]
      (F.obj X.left).obj X.right ⟶ (F.obj Y.left).obj Y.right where
  toFun f :=
    { toFun := fun g => (F.map f).app X.right ≫ (F.obj Y.left).map g
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

def liftHom (X Y : LinearTensor C D) : Hom X Y →ₗ[ℂ]
    ((F.obj X.left).obj X.right ⟶ (F.obj Y.left).obj Y.right) :=
  TensorProduct.lift (liftHomBilinear F X Y)

@[simp] lemma liftHom_tmul (X Y : LinearTensor C D)
    (f : X.left ⟶ Y.left) (g : X.right ⟶ Y.right) :
    liftHom F X Y (f ⊗ₜ[ℂ] g) = (F.map f).app X.right ≫ (F.obj Y.left).map g := rfl

lemma liftHom_comp (X Y Z : LinearTensor C D) (f : Hom X Y) (g : Hom Y Z) :
    liftHom F X Z (compLinear X Y Z f g) = liftHom F X Y f ≫ liftHom F Y Z g := by
  induction f using TensorProduct.induction_on with
  | zero => simp
  | tmul f₁ f₂ =>
    induction g using TensorProduct.induction_on with
    | zero => simp
    | tmul g₁ g₂ =>
      simp only [compLinear_tmul, liftHom_tmul, Functor.map_comp,
        NatTrans.comp_app, Category.assoc]
      rw [← (F.map g₁).naturality_assoc f₂]
    | add a b ha hb => simp_all [Preadditive.comp_add]
  | add a b ha hb => simp_all [Preadditive.add_comp]

/-- The complex-linear extension of an actual bilinear bifunctor. -/
def lift : LinearTensor C D ⥤ E where
  obj X := (F.obj X.left).obj X.right
  map f := liftHom F _ _ f
  map_id X := by simp
  map_comp {X Y Z} f g := liftHom_comp F X Y Z f g

instance : (lift F).Additive where
  map_add := by intros; exact (liftHom F _ _).map_add _ _

instance : (lift F).Linear ℂ where
  map_smul := by intros; exact (liftHom F _ _).map_smul _ _

end Paper18.Category.LinearTensor
