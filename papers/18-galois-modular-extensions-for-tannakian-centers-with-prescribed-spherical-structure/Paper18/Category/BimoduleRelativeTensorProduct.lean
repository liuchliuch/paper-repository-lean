import Paper18.Category.BimoduleRelativeTensorEquivalence
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Actual relative tensor products for arbitrary native bimodules

The ambient tensor adjunctions preserve the actual balancing coequalizers.
The existing two-sided bimodule construction then installs both outer
actions on that actual quotient. No braiding or commutativity is used.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

attribute [local instance 2000] RightRigidCategory.rightDual LeftRigidCategory.leftDual

instance tensorLeft_preservesColimits [LeftRigidCategory D] (X : D) :
    PreservesColimitsOfSize.{0,0} (tensorLeft X) :=
  (tensorLeftAdjunction (ᘁX) X).leftAdjoint_preservesColimits

instance tensorRight_preservesColimits [RightRigidCategory D] (X : D) :
    PreservesColimitsOfSize.{0,0} (tensorRight X) :=
  (tensorRightAdjunction X Xᘁ).leftAdjoint_preservesColimits

variable [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
  {R S T : D} [MonObj R] [MonObj S] [MonObj T]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- The actual balanced coequalizer, equipped with both actual outer
actions and expressed as a native iterated internal module. -/
def tensor (M : Native R S) (N : Native S T) : Native R T :=
  fromBimodObj R T ((toBimodObj R S M).tensorBimod (toBimodObj S T N))

/-- The actual quotient map imposing the two actual middle actions. -/
def π (M : Native R S) (N : Native S T) : M.X.X ⊗ N.X.X ⟶ (tensor M N).X.X :=
  coequalizer.π (γ[mop S,M.X].hom ▷ N.X.X)
    ((α_ M.X.X S N.X.X).hom ≫ M.X.X ◁ γ[S,N.X.X])

instance π_epi (M : Native R S) (N : Native S T) : Epi (π M N) := by
  unfold π
  infer_instance

@[reassoc]
lemma condition (M : Native R S) (N : Native S T) :
    γ[mop S,M.X].hom ▷ N.X.X ≫ π M N =
      (α_ M.X.X S N.X.X).hom ≫ M.X.X ◁ γ[S,N.X.X] ≫ π M N := by
  simpa only [π, assoc] using coequalizer.condition
    (γ[mop S,M.X].hom ▷ N.X.X)
    ((α_ M.X.X S N.X.X).hom ≫ M.X.X ◁ γ[S,N.X.X])

/-- Actual balanced maps descend uniquely through the actual quotient. -/
def desc (M : Native R S) (N : Native S T) {W : D} (f : M.X.X ⊗ N.X.X ⟶ W)
    (hf : γ[mop S,M.X].hom ▷ N.X.X ≫ f =
      (α_ M.X.X S N.X.X).hom ≫ M.X.X ◁ γ[S,N.X.X] ≫ f) :
    (tensor M N).X.X ⟶ W := coequalizer.desc f (by simpa only [assoc] using hf)

@[reassoc (attr := simp)]
lemma π_desc (M : Native R S) (N : Native S T) {W : D} (f : M.X.X ⊗ N.X.X ⟶ W)
    (hf : γ[mop S,M.X].hom ▷ N.X.X ≫ f =
      (α_ M.X.X S N.X.X).hom ≫ M.X.X ◁ γ[S,N.X.X] ≫ f) :
    π M N ≫ desc M N f hf = f := coequalizer.π_desc _ _

lemma hom_ext (M : Native R S) (N : Native S T) {W : D}
    {f g : (tensor M N).X.X ⟶ W} (h : π M N ≫ f = π M N ≫ g) : f = g :=
  (cancel_epi (π M N)).mp h

@[reassoc]
lemma π_left (M : Native R S) (N : Native S T) :
    R ◁ π M N ≫ γ[R,(tensor M N).X.X] =
      (α_ R M.X.X N.X.X).inv ≫ γ[R,M.X.X] ▷ N.X.X ≫ π M N := by
  exact Bimod.TensorBimod.whiskerLeft_π_actLeft (toBimodObj R S M) (toBimodObj S T N)

@[reassoc]
lemma π_right (M : Native R S) (N : Native S T) :
    π M N ▷ T ≫ γ[mop T,(tensor M N).X].hom =
      (α_ M.X.X N.X.X T).hom ≫ M.X.X ◁ γ[mop T,N.X].hom ≫ π M N := by
  exact Bimod.TensorBimod.π_tensor_id_actRight (toBimodObj R S M) (toBimodObj S T N)

end Paper18.Category.BimoduleRelativeTensor
