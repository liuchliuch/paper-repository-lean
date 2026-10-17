import Paper18.Category.RepresentationZ2Eigenspaces

/-! # Actual order-two actions from involutions -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category
namespace Paper18.Category.RepresentationZ2

@[simp] lemma generator_ne_one : generator ≠ (1 : H) := by decide

lemma eq_one_or_generator (g : H) : g = 1 ∨ g = generator :=
  (show ∀ g : H, g = 1 ∨ g = generator by decide) g

/-- A categorical linear involution defines an actual representation of C₂. -/
def actionOfInvolution (V : FGModuleCat ℂ) (s : V ⟶ V) (hs : s ≫ s = 𝟙 V) : FDRep ℂ H where
  V := V
  ρ :=
    { toFun := fun g => if g = 1 then 𝟙 V else s
      map_one' := by simp
      map_mul' g h := by
        rcases eq_one_or_generator g with rfl | rfl <;>
          rcases eq_one_or_generator h with rfl | rfl <;>
          simp [End.mul_def, hs] }

@[simp] lemma actionOfInvolution_generator (V : FGModuleCat ℂ)
    (s : V ⟶ V) (hs : s ≫ s = 𝟙 V) :
    (actionOfInvolution V s hs).ρ generator = s.hom := by
  change (if generator = 1 then 𝟙 V else s).hom = s.hom
  simp

/-- An intertwiner of the two involutions is a genuine representation morphism. -/
def mapOfInvolution {V W : FGModuleCat ℂ} (s : V ⟶ V) (t : W ⟶ W)
    (hs : s ≫ s = 𝟙 V) (ht : t ≫ t = 𝟙 W)
    (f : V ⟶ W) (hf : s ≫ f = f ≫ t) :
    actionOfInvolution V s hs ⟶ actionOfInvolution W t ht where
  hom := f
  comm g := by
    rcases eq_one_or_generator g with rfl | rfl
    · simp
    · simpa [actionOfInvolution] using hf

end Paper18.Category.RepresentationZ2
