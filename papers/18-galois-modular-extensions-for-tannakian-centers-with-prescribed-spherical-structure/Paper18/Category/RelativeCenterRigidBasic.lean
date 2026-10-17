import Paper18.Category.RelativeCenterUnit
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Dual half-braiding from actual rigid transposition

The maps below are the partial transposes of the inverse half-braiding.
They are built using the chosen evaluation and coevaluation, rather than
assuming a dual object in the center.
-/
noncomputable section
universe v u
namespace Paper18.Category.RelativeCenter

open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {P : ObjectProperty C} [P.IsMonoidal]

/-- The inverse naturality equation for an actual half-braiding. -/
lemma halfBraiding_inv_naturality {X U V : C} (b : RelativeHalfBraiding P X) (hU : P U) (hV : P V) (f : U ⟶ V) :
    (f ▷ X) ≫ (b.β V hV).inv = (b.β U hU).inv ≫ (X ◁ f) := by
  apply (cancel_epi (b.β U hU).hom).mp
  rw [← RelativeHalfBraiding.naturality_assoc b hU hV f]
  simp

/-- Inverting the half-braiding hexagon yields the reverse hexagon. -/
lemma halfBraiding_inv_monoidal {X : C} (b : RelativeHalfBraiding P X) (U V : C) (hU : P U) (hV : P V) :
    (b.β (U ⊗ V) (ObjectProperty.prop_tensor hU hV)).inv =
      (α_ U V X).hom ≫ (U ◁ (b.β V hV).inv) ≫ (α_ U X V).inv ≫
        ((b.β U hU).inv ▷ V) ≫ (α_ X U V).hom := by
  have h : b.β (U ⊗ V) (ObjectProperty.prop_tensor hU hV) = (α_ X U V).symm ≪≫
      whiskerRightIso (b.β U hU) V ≪≫ α_ U X V ≪≫
        whiskerLeftIso U (b.β V hV) ≪≫ (α_ U V X).symm := by
    apply Iso.ext
    exact b.monoidal U V hU hV
  rw [h]
  simp only [Iso.trans_inv, Iso.symm_inv, whiskerLeftIso_inv, whiskerRightIso_inv, assoc]

variable [RightRigidCategory C] (Z : RelativeCenter P)

/-- Closing the original inverse half-braiding with the right evaluation. -/
def dualHalfBraidingCap (U : C) (hU : P U) : (Z.1ᘁ ⊗ U) ⊗ Z.1 ⟶ U :=
  (α_ Z.1ᘁ U Z.1).hom ≫ Z.1ᘁ ◁ (Z.2.β U hU).inv ≫
    (α_ Z.1ᘁ Z.1 U).inv ≫ ε_ Z.1 Z.1ᘁ ▷ U ≫ (λ_ U).hom

/-- Partial transposition bends the original central object strand around
its actual evaluation and coevaluation. -/
def dualHalfBraidingHom (U : C) (hU : P U) : Z.1ᘁ ⊗ U ⟶ U ⊗ Z.1ᘁ :=
  tensorRightHomEquiv (Z.1ᘁ ⊗ U) Z.1 Z.1ᘁ U (dualHalfBraidingCap Z U hU)

/-- The evaluation identity characterizing the partial transpose. -/
lemma dualHalfBraidingHom_cap (U : C) (hU : P U) :
    dualHalfBraidingHom Z U hU ▷ Z.1 ≫ (α_ U Z.1ᘁ Z.1).hom ≫
      U ◁ ε_ Z.1 Z.1ᘁ ≫ (ρ_ U).hom = dualHalfBraidingCap Z U hU := by
  exact (tensorRightHomEquiv (Z.1ᘁ ⊗ U) Z.1 Z.1ᘁ U).symm_apply_apply _

/-- Equality of candidate dual commutation maps can be checked after closing
with the actual evaluation. -/
lemma dualHalfBraiding_hom_ext {T U : C} {f g : T ⟶ U ⊗ Z.1ᘁ}
    (h : f ▷ Z.1 ≫ (α_ U Z.1ᘁ Z.1).hom ≫ U ◁ ε_ Z.1 Z.1ᘁ ≫ (ρ_ U).hom =
      g ▷ Z.1 ≫ (α_ U Z.1ᘁ Z.1).hom ≫ U ◁ ε_ Z.1 Z.1ᘁ ≫ (ρ_ U).hom) : f = g :=
  (tensorRightHomEquiv T Z.1 Z.1ᘁ U).symm.injective h

/-- Naturality of the evaluation-closed inverse half-braiding. -/
lemma dualHalfBraidingCap_naturality {U V : C} (hU : P U) (hV : P V) (f : U ⟶ V) :
    (Z.1ᘁ ◁ f) ▷ Z.1 ≫ dualHalfBraidingCap Z V hV =
      dualHalfBraidingCap Z U hU ≫ f := by
  calc
    _ = 𝟙 _ ⊗≫ (Z.1ᘁ : C) ◁ ((f ▷ Z.1) ≫ (Z.2.β V hV).inv) ⊗≫
        ε_ Z.1 Z.1ᘁ ▷ V ⊗≫ 𝟙 V := by
      dsimp [dualHalfBraidingCap]
      monoidal
    _ = 𝟙 _ ⊗≫ (Z.1ᘁ : C) ◁ (Z.2.β U hU).inv ⊗≫
        ((Z.1ᘁ ⊗ Z.1) ◁ f ≫ ε_ Z.1 Z.1ᘁ ▷ V) ⊗≫ 𝟙 V := by
      rw [halfBraiding_inv_naturality Z.2 hU hV f]
      monoidal
    _ = _ := by
      rw [whisker_exchange]
      dsimp [dualHalfBraidingCap]
      monoidal

/-- Naturality of the candidate dual half-braiding is derived from the
actual rigid Hom adjunction. -/
lemma dualHalfBraidingHom_naturality {U V : C} (hU : P U) (hV : P V) (f : U ⟶ V) :
    (Z.1ᘁ ◁ f) ≫ dualHalfBraidingHom Z V hV =
      dualHalfBraidingHom Z U hU ≫ (f ▷ Z.1ᘁ) := by
  apply (tensorRightHomEquiv (Z.1ᘁ ⊗ U) Z.1 Z.1ᘁ V).symm.injective
  rw [tensorRightHomEquiv_symm_naturality]
  rw [show dualHalfBraidingHom Z U hU ≫ (f ▷ Z.1ᘁ) =
      tensorRightHomEquiv _ _ _ _ (dualHalfBraidingCap Z U hU ≫ f) from
        (tensorRightHomEquiv_naturality _ f).symm]
  simp only [dualHalfBraidingHom, Equiv.symm_apply_apply]
  exact dualHalfBraidingCap_naturality Z hU hV f

/-- The candidate has the forced unit component of a half-braiding. -/
lemma dualHalfBraidingHom_unit :
    dualHalfBraidingHom Z (𝟙_ C) (ObjectProperty.prop_unit P) = (ρ_ Z.1ᘁ).hom ≫ (λ_ Z.1ᘁ).inv := by
  apply dualHalfBraiding_hom_ext Z
  rw [dualHalfBraidingHom_cap (hU := ObjectProperty.prop_unit P)]
  have hu : Z.2.β (𝟙_ C) (ObjectProperty.prop_unit P) = ρ_ Z.1 ≪≫ (λ_ Z.1).symm := by
    apply Iso.ext
    exact Z.2.unit
  dsimp [dualHalfBraidingCap]
  rw [hu]
  simp only [Iso.trans_inv, Iso.symm_inv]
  monoidal

/-- The dual half-braiding hexagon follows by closing with the actual
evaluation and using the inverse hexagon of the original half-braiding. -/
lemma dualHalfBraidingHom_monoidal (U V : C) (hU : P U) (hV : P V) :
    dualHalfBraidingHom Z (U ⊗ V) (ObjectProperty.prop_tensor hU hV) =
      (α_ Z.1ᘁ U V).inv ≫ (dualHalfBraidingHom Z U hU ▷ V) ≫
        (α_ U Z.1ᘁ V).hom ≫ (U ◁ dualHalfBraidingHom Z V hV) ≫
          (α_ U V Z.1ᘁ).inv := by
  apply dualHalfBraiding_hom_ext Z
  rw [dualHalfBraidingHom_cap (hU := ObjectProperty.prop_tensor hU hV)]
  symm
  calc
    _ = 𝟙 ((Z.1ᘁ ⊗ (U ⊗ V)) ⊗ Z.1) ⊗≫
        dualHalfBraidingHom Z U hU ▷ (V ⊗ Z.1) ⊗≫
        U ◁ (dualHalfBraidingHom Z V hV ▷ Z.1 ≫ (α_ V Z.1ᘁ Z.1).hom ≫
          V ◁ ε_ Z.1 Z.1ᘁ ≫ (ρ_ V).hom) ⊗≫ 𝟙 (U ⊗ V) := by
      monoidal
    _ = 𝟙 ((Z.1ᘁ ⊗ (U ⊗ V)) ⊗ Z.1) ⊗≫
        (dualHalfBraidingHom Z U hU ▷ (V ⊗ Z.1) ≫
          (U ⊗ Z.1ᘁ) ◁ (Z.2.β V hV).inv) ⊗≫
        U ◁ ε_ Z.1 Z.1ᘁ ▷ V ⊗≫ 𝟙 (U ⊗ V) := by
      rw [dualHalfBraidingHom_cap (hU := hV)]
      dsimp [dualHalfBraidingCap]
      monoidal
    _ = 𝟙 ((Z.1ᘁ ⊗ (U ⊗ V)) ⊗ Z.1) ⊗≫
        (Z.1ᘁ ⊗ U) ◁ (Z.2.β V hV).inv ⊗≫
        (dualHalfBraidingHom Z U hU ▷ Z.1 ≫ (α_ U Z.1ᘁ Z.1).hom ≫
          U ◁ ε_ Z.1 Z.1ᘁ ≫ (ρ_ U).hom) ▷ V ⊗≫ 𝟙 (U ⊗ V) := by
      rw [← whisker_exchange]
      monoidal
    _ = dualHalfBraidingCap Z (U ⊗ V) (ObjectProperty.prop_tensor hU hV) := by
      rw [dualHalfBraidingHom_cap (hU := hU)]
      dsimp [dualHalfBraidingCap]
      rw [halfBraiding_inv_monoidal Z.2 U V hU hV]
      monoidal

end Paper18.Category.RelativeCenter
