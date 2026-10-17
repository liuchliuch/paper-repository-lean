import Paper18.Category.RelativeTensorBimod
import Paper18.Category.SeparableModulesLinear

/-! # The actual universal balanced Hom property of relative tensor -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj
universe v u
namespace Paper18.Category.RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [HasCoequalizers C] {A : C} [MonObj A] [IsCommMonObj A]
  (M N : Mod_ C A)

/-- The two actual action maps imposing the balancing relation. -/
def parallelLeft : (M.X ⊗ A) ⊗ N.X ⟶ M.X ⊗ N.X := rightAction M ▷ N.X
def parallelRight : (M.X ⊗ A) ⊗ N.X ⟶ M.X ⊗ N.X :=
  (α_ M.X A N.X).hom ≫ (M.X ◁ γ[A,N.X])

/-- An actual underlying map is balanced when the two algebra actions have
the same composite with it. -/
def Balanced {Z : C} (f : M.X ⊗ N.X ⟶ Z) : Prop :=
  parallelLeft M N ≫ f = parallelRight M N ≫ f

/-- The actual balancing quotient. -/
def π : M.X ⊗ N.X ⟶ (tensorObj M N).X := coequalizer.π _ _

instance π_epi : Epi (π M N) := by unfold π; infer_instance

@[reassoc]
theorem condition : parallelLeft M N ≫ π M N = parallelRight M N ≫ π M N :=
  coequalizer.condition _ _

/-- The actual universal balanced descent. -/
def desc {Z : C} (f : M.X ⊗ N.X ⟶ Z) (hf : Balanced M N f) :
    (tensorObj M N).X ⟶ Z := coequalizer.desc f hf

@[reassoc (attr := simp)]
theorem π_desc {Z : C} (f : M.X ⊗ N.X ⟶ Z) (hf : Balanced M N f) :
    π M N ≫ desc M N f hf = f := coequalizer.π_desc _ _

/-- A map from the actual relative tensor is determined by its balanced
composite with the actual quotient. -/
theorem hom_ext {Z : C} {f g : (tensorObj M N).X ⟶ Z}
    (h : π M N ≫ f = π M N ≫ g) : f = g := coequalizer.hom_ext h

/-- The quotient represents actual balanced maps. -/
def homEquiv (Z : C) : ((tensorObj M N).X ⟶ Z) ≃
    {f : M.X ⊗ N.X ⟶ Z // Balanced M N f} where
  toFun f := ⟨π M N ≫ f, by
    unfold Balanced
    simpa only [Category.assoc] using congrArg (fun k => k ≫ f) (condition M N)⟩
  invFun f := desc M N f.val f.property
  left_inv f := by apply hom_ext M N; simp
  right_inv f := by apply Subtype.ext; exact π_desc M N f.val f.property

/-- The actual left action on the relative tensor is characterized by the
ordinary action on its first tensor factor. -/
@[reassoc]
theorem π_action : (A ◁ π M N) ≫ γ[A,(tensorObj M N).X] =
    (α_ A M.X N.X).inv ≫ γ[A,M.X] ▷ N.X ≫ π M N :=
  Bimod.TensorBimod.whiskerLeft_π_actLeft (toBimodObj M) (toBimodObj N)

/-- A balanced ambient map descends to an actual module map when it
intertwines the actual action on its first input factor. -/
def descModule (P : Mod_ C A) (f : M.X ⊗ N.X ⟶ P.X) (hf : Balanced M N f)
    (hlin : (α_ A M.X N.X).inv ≫ γ[A,M.X] ▷ N.X ≫ f =
      (A ◁ f) ≫ γ[A,P.X]) : tensorObj M N ⟶ P :=
  Mod_.Hom.mk' (desc M N f hf) (by
    change γ[A,(tensorObj M N).X] ≫ desc M N f hf =
      (A ◁ desc M N f hf) ≫ γ[A,P.X]
    letI : Epi (A ◁ π M N) :=
      inferInstanceAs (Epi ((tensorLeft A).map
        (coequalizer.π (parallelLeft M N) (parallelRight M N))))
    apply (cancel_epi (A ◁ π M N)).mp
    rw [π_action_assoc, π_desc, ← whiskerLeft_comp_assoc, π_desc]
    exact hlin)

section Linear
variable [Preadditive C] [Linear ℂ C]

/-- Balanced morphisms form an actual subspace of the ambient Hom space. -/
def balancedSubmodule (Z : C) : Submodule ℂ (M.X ⊗ N.X ⟶ Z) where
  carrier := {f | Balanced M N f}
  zero_mem' := by unfold Balanced; simp
  add_mem' := by
    intro f g hf hg
    change parallelLeft M N ≫ f = parallelRight M N ≫ f at hf
    change parallelLeft M N ≫ g = parallelRight M N ≫ g at hg
    change parallelLeft M N ≫ (f + g) = parallelRight M N ≫ (f + g)
    simp [Preadditive.comp_add, hf, hg]
  smul_mem' := by
    intro c f hf
    change parallelLeft M N ≫ f = parallelRight M N ≫ f at hf
    change parallelLeft M N ≫ (c • f) = parallelRight M N ≫ (c • f)
    simp [hf]

/-- The balanced universal property is an actual complex-linear equivalence. -/
def homLinearEquiv (Z : C) : ((tensorObj M N).X ⟶ Z) ≃ₗ[ℂ] balancedSubmodule M N Z where
  toEquiv := homEquiv M N Z
  map_add' f g := by
    apply Subtype.ext
    change π M N ≫ (f + g) = π M N ≫ f + π M N ≫ g
    rw [Preadditive.comp_add]
  map_smul' c f := by
    apply Subtype.ext
    change π M N ≫ (c • f) = c • (π M N ≫ f)
    simp

end Linear
end Paper18.Category.RelativeTensor
