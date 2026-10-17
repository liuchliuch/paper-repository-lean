import Paper18.Category.PointedRelativeCenterObstructionBasic

/-! # Actual complex-linear morphisms in the quasi relative center -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction.RelativeObject
open FiniteCohomologyKilling
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G] (p : Γ →* G)
  (ψ : ThreeCochain Γ ℂˣ)
local notation "V" => PointedVec (Additive Γ)

/-- Actual relative-central arrows form the actual subspace of graded
linear maps commuting with all specified neutral half-braidings. -/
def homSubmodule (X Y : RelativeObject p ψ) : Submodule ℂ (X.1 ⟶ Y.1) where
  carrier := {f | ∀ (U : V) (hU : Supported p 1 U),
    f ▷ U ≫ (Y.2.β U hU).hom = (X.2.β U hU).hom ≫ U ◁ f}
  zero_mem' := by intro U hU; simp
  add_mem' := by intro f g hf hg U hU; simp [hf U hU, hg U hU]
  smul_mem' := by intro c f hf U hU; simp [hf U hU]

def homEquivSubmodule (X Y : RelativeObject p ψ) : (X ⟶ Y) ≃ homSubmodule p ψ X Y where
  toFun f := ⟨f.f, f.comm⟩
  invFun f := ⟨f.val, f.property⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

instance homAddCommGroup (X Y : RelativeObject p ψ) : AddCommGroup (X ⟶ Y) :=
  (homEquivSubmodule p ψ X Y).addCommGroup
instance homModule (X Y : RelativeObject p ψ) : Module ℂ (X ⟶ Y) :=
  Equiv.module ℂ (homEquivSubmodule p ψ X Y)

@[simp] lemma zero_f (X Y : RelativeObject p ψ) : (0 : X ⟶ Y).f = 0 := rfl
@[simp] lemma add_f {X Y : RelativeObject p ψ} (f g : X ⟶ Y) : (f + g).f = f.f + g.f := rfl
@[simp] lemma smul_f {X Y : RelativeObject p ψ} (c : ℂ) (f : X ⟶ Y) :
    (c • f).f = c • f.f := rfl

instance preadditive : Preadditive (RelativeObject p ψ) where
  add_comp := by intro X Y Z f g h; apply ext p ψ; simp [Preadditive.add_comp]
  comp_add := by intro X Y Z f g h; apply ext p ψ; simp [Preadditive.comp_add]
instance linear : Linear ℂ (RelativeObject p ψ) where
  smul_comp := by intro X Y Z c f g; apply ext p ψ; simp
  comp_smul := by intro X Y Z f c g; apply ext p ψ; simp
instance forget_additive : (forget p ψ).Additive where
  map_add := by intros; rfl
instance forget_linear : (forget p ψ).Linear ℂ where
  map_smul _ _ := rfl

def homLinearEquivSubmodule (X Y : RelativeObject p ψ) :
    (X ⟶ Y) ≃ₗ[ℂ] homSubmodule p ψ X Y where
  toEquiv := homEquivSubmodule p ψ X Y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance hom_finiteDimensional (X Y : RelativeObject p ψ) : FiniteDimensional ℂ (X ⟶ Y) :=
  (homLinearEquivSubmodule p ψ X Y).symm.finiteDimensional

end Paper18.Category.PointedRelativeCenterObstruction.RelativeObject
