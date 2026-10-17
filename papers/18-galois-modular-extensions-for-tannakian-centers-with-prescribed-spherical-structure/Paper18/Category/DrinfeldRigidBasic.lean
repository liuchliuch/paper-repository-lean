import Paper18.Category.DrinfeldBasic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Dual half-braiding from actual rigid transposition

The maps below are the partial transposes of the inverse half-braiding.
They are built using the chosen evaluation and coevaluation, rather than
assuming a dual object in the center.
-/
noncomputable section
universe v u
namespace Paper18.Category.Drinfeld

open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The inverse naturality equation for an actual half-braiding. -/
lemma halfBraiding_inv_naturality {X U V : C} (b : HalfBraiding X) (f : U ⟶ V) :
    (f ▷ X) ≫ (b.β V).inv = (b.β U).inv ≫ (X ◁ f) := by
  apply (cancel_epi (b.β U).hom).mp
  rw [← HalfBraiding.naturality_assoc]
  simp

/-- Inverting the half-braiding hexagon yields the reverse hexagon. -/
lemma halfBraiding_inv_monoidal {X : C} (b : HalfBraiding X) (U V : C) :
    (b.β (U ⊗ V)).inv =
      (α_ U V X).hom ≫ (U ◁ (b.β V).inv) ≫ (α_ U X V).inv ≫
        ((b.β U).inv ▷ V) ≫ (α_ X U V).hom := by
  have h : b.β (U ⊗ V) = (α_ X U V).symm ≪≫
      whiskerRightIso (b.β U) V ≪≫ α_ U X V ≪≫
        whiskerLeftIso U (b.β V) ≪≫ (α_ U V X).symm := by
    apply Iso.ext
    exact b.monoidal U V
  rw [h]
  simp only [Iso.trans_inv, Iso.symm_inv, whiskerLeftIso_inv, whiskerRightIso_inv, assoc]

variable [RightRigidCategory C] (Z : Center C)

/-- Closing the original inverse half-braiding with the right evaluation. -/
def dualHalfBraidingCap (U : C) : (Z.1ᘁ ⊗ U) ⊗ Z.1 ⟶ U :=
  (α_ Z.1ᘁ U Z.1).hom ≫ Z.1ᘁ ◁ (Z.2.β U).inv ≫
    (α_ Z.1ᘁ Z.1 U).inv ≫ ε_ Z.1 Z.1ᘁ ▷ U ≫ (λ_ U).hom

/-- Partial transposition bends the original central object strand around
its actual evaluation and coevaluation. -/
def dualHalfBraidingHom (U : C) : Z.1ᘁ ⊗ U ⟶ U ⊗ Z.1ᘁ :=
  tensorRightHomEquiv (Z.1ᘁ ⊗ U) Z.1 Z.1ᘁ U (dualHalfBraidingCap Z U)

/-- The evaluation identity characterizing the partial transpose. -/
lemma dualHalfBraidingHom_cap (U : C) :
    dualHalfBraidingHom Z U ▷ Z.1 ≫ (α_ U Z.1ᘁ Z.1).hom ≫
      U ◁ ε_ Z.1 Z.1ᘁ ≫ (ρ_ U).hom = dualHalfBraidingCap Z U := by
  exact (tensorRightHomEquiv (Z.1ᘁ ⊗ U) Z.1 Z.1ᘁ U).symm_apply_apply _

/-- Equality of candidate dual commutation maps can be checked after closing
with the actual evaluation. -/
lemma dualHalfBraiding_hom_ext {T U : C} {f g : T ⟶ U ⊗ Z.1ᘁ}
    (h : f ▷ Z.1 ≫ (α_ U Z.1ᘁ Z.1).hom ≫ U ◁ ε_ Z.1 Z.1ᘁ ≫ (ρ_ U).hom =
      g ▷ Z.1 ≫ (α_ U Z.1ᘁ Z.1).hom ≫ U ◁ ε_ Z.1 Z.1ᘁ ≫ (ρ_ U).hom) : f = g :=
  (tensorRightHomEquiv T Z.1 Z.1ᘁ U).symm.injective h

/-- Naturality of the evaluation-closed inverse half-braiding. -/
lemma dualHalfBraidingCap_naturality {U V : C} (f : U ⟶ V) :
    (Z.1ᘁ ◁ f) ▷ Z.1 ≫ dualHalfBraidingCap Z V =
      dualHalfBraidingCap Z U ≫ f := by
  calc
    _ = 𝟙 _ ⊗≫ (Z.1ᘁ : C) ◁ ((f ▷ Z.1) ≫ (Z.2.β V).inv) ⊗≫
        ε_ Z.1 Z.1ᘁ ▷ V ⊗≫ 𝟙 V := by
      dsimp [dualHalfBraidingCap]
      monoidal
    _ = 𝟙 _ ⊗≫ (Z.1ᘁ : C) ◁ (Z.2.β U).inv ⊗≫
        ((Z.1ᘁ ⊗ Z.1) ◁ f ≫ ε_ Z.1 Z.1ᘁ ▷ V) ⊗≫ 𝟙 V := by
      rw [halfBraiding_inv_naturality]
      monoidal
    _ = _ := by
      rw [whisker_exchange]
      dsimp [dualHalfBraidingCap]
      monoidal

/-- Naturality of the candidate dual half-braiding is derived from the
actual rigid Hom adjunction. -/
lemma dualHalfBraidingHom_naturality {U V : C} (f : U ⟶ V) :
    (Z.1ᘁ ◁ f) ≫ dualHalfBraidingHom Z V =
      dualHalfBraidingHom Z U ≫ (f ▷ Z.1ᘁ) := by
  apply (tensorRightHomEquiv (Z.1ᘁ ⊗ U) Z.1 Z.1ᘁ V).symm.injective
  rw [tensorRightHomEquiv_symm_naturality]
  rw [show dualHalfBraidingHom Z U ≫ (f ▷ Z.1ᘁ) =
      tensorRightHomEquiv _ _ _ _ (dualHalfBraidingCap Z U ≫ f) from
        (tensorRightHomEquiv_naturality _ f).symm]
  simp only [dualHalfBraidingHom, Equiv.symm_apply_apply]
  exact dualHalfBraidingCap_naturality Z f

/-- The candidate has the forced unit component of a half-braiding. -/
lemma dualHalfBraidingHom_unit :
    dualHalfBraidingHom Z (𝟙_ C) = (ρ_ Z.1ᘁ).hom ≫ (λ_ Z.1ᘁ).inv := by
  apply dualHalfBraiding_hom_ext Z
  rw [dualHalfBraidingHom_cap]
  have hu : Z.2.β (𝟙_ C) = ρ_ Z.1 ≪≫ (λ_ Z.1).symm := by
    apply Iso.ext
    exact halfBraiding_unit Z.1 Z.2
  dsimp [dualHalfBraidingCap]
  rw [hu]
  simp only [Iso.trans_inv, Iso.symm_inv]
  monoidal

/-- The dual half-braiding hexagon follows by closing with the actual
evaluation and using the inverse hexagon of the original half-braiding. -/
lemma dualHalfBraidingHom_monoidal (U V : C) :
    dualHalfBraidingHom Z (U ⊗ V) =
      (α_ Z.1ᘁ U V).inv ≫ (dualHalfBraidingHom Z U ▷ V) ≫
        (α_ U Z.1ᘁ V).hom ≫ (U ◁ dualHalfBraidingHom Z V) ≫
          (α_ U V Z.1ᘁ).inv := by
  apply dualHalfBraiding_hom_ext Z
  rw [dualHalfBraidingHom_cap]
  symm
  calc
    _ = 𝟙 ((Z.1ᘁ ⊗ (U ⊗ V)) ⊗ Z.1) ⊗≫
        dualHalfBraidingHom Z U ▷ (V ⊗ Z.1) ⊗≫
        U ◁ (dualHalfBraidingHom Z V ▷ Z.1 ≫ (α_ V Z.1ᘁ Z.1).hom ≫
          V ◁ ε_ Z.1 Z.1ᘁ ≫ (ρ_ V).hom) ⊗≫ 𝟙 (U ⊗ V) := by
      monoidal
    _ = 𝟙 ((Z.1ᘁ ⊗ (U ⊗ V)) ⊗ Z.1) ⊗≫
        (dualHalfBraidingHom Z U ▷ (V ⊗ Z.1) ≫
          (U ⊗ Z.1ᘁ) ◁ (Z.2.β V).inv) ⊗≫
        U ◁ ε_ Z.1 Z.1ᘁ ▷ V ⊗≫ 𝟙 (U ⊗ V) := by
      rw [dualHalfBraidingHom_cap]
      dsimp [dualHalfBraidingCap]
      monoidal
    _ = 𝟙 ((Z.1ᘁ ⊗ (U ⊗ V)) ⊗ Z.1) ⊗≫
        (Z.1ᘁ ⊗ U) ◁ (Z.2.β V).inv ⊗≫
        (dualHalfBraidingHom Z U ▷ Z.1 ≫ (α_ U Z.1ᘁ Z.1).hom ≫
          U ◁ ε_ Z.1 Z.1ᘁ ≫ (ρ_ U).hom) ▷ V ⊗≫ 𝟙 (U ⊗ V) := by
      rw [← whisker_exchange]
      monoidal
    _ = dualHalfBraidingCap Z (U ⊗ V) := by
      rw [dualHalfBraidingHom_cap]
      dsimp [dualHalfBraidingCap]
      rw [halfBraiding_inv_monoidal]
      monoidal

end Paper18.Category.Drinfeld
