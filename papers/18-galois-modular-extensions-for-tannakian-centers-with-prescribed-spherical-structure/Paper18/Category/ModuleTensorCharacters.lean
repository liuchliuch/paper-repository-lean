import Paper18.Category.RelativeTensorLinear
import Paper18.Category.RelativeTensorFree

/-! # Descent of actual tensor characters to algebra modules

A tensor character which is the identity on the algebra acts on every
actual module. Its monoidality is proved on the relative tensor quotient.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u
namespace Paper18.Category.ModuleTensorCharacters
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]

lemma tensor_component (X Y : C) :
    χ.hom.app (X ⊗ Y) = χ.hom.app X ⊗ₘ χ.hom.app Y := by
  have ht := NatTrans.IsMonoidal.tensor (τ := χ.hom) X Y
  change 𝟙 (X ⊗ Y) ≫ χ.hom.app (X ⊗ Y) =
    (χ.hom.app X ⊗ₘ χ.hom.app Y) ≫ 𝟙 (X ⊗ Y) at ht
  exact (Category.id_comp _).symm.trans (ht.trans (Category.comp_id _))

variable {A : C} [MonObj A] (hχ : χ.hom.app A = 𝟙 A)

include hχ in
lemma inverse_algebra : χ.inv.app A = 𝟙 A := by
  have h := χ.hom_inv_id_app A
  change χ.hom.app A ≫ χ.inv.app A = 𝟙 A at h
  rw [hχ] at h
  exact (Category.id_comp _).symm.trans h

include hχ in
lemma action_compatible (M : Mod_ C A) :
    γ[A,M.X] ≫ χ.hom.app M.X = (A ◁ χ.hom.app M.X) ≫ γ[A,M.X] := by
  have hn := χ.hom.naturality γ[A,M.X]
  change γ[A,M.X] ≫ χ.hom.app M.X = χ.hom.app (A ⊗ M.X) ≫ γ[A,M.X] at hn
  rw [tensor_component, hχ] at hn
  exact hn.trans (congrArg (fun k => k ≫ γ[A,M.X])
    (MonoidalCategory.id_tensorHom A (χ.hom.app M.X)))

def moduleMap (M : Mod_ C A) : M ⟶ M :=
  Mod_.Hom.mk' (χ.hom.app M.X) (action_compatible χ hχ M)

def moduleIso (M : Mod_ C A) : M ≅ M where
  hom := moduleMap χ hχ M
  inv := by
    letI : NatTrans.IsMonoidal χ.symm.hom := inferInstanceAs (NatTrans.IsMonoidal χ.inv)
    exact moduleMap χ.symm (inverse_algebra χ hχ) M
  hom_inv_id := by apply Mod_.Hom.ext; exact χ.hom_inv_id_app M.X
  inv_hom_id := by apply Mod_.Hom.ext; exact χ.inv_hom_id_app M.X

def moduleCharacter : 𝟭 (Mod_ C A) ≅ 𝟭 (Mod_ C A) :=
  NatIso.ofComponents (moduleIso χ hχ) (fun {M N} f => by
    apply Mod_.Hom.ext
    exact χ.hom.naturality f.hom)

@[simp] lemma moduleCharacter_hom (M : Mod_ C A) :
    ((moduleCharacter χ hχ).hom.app M).hom = χ.hom.app M.X := rfl

@[simp] lemma moduleCharacter_inv (M : Mod_ C A) :
    ((moduleCharacter χ hχ).inv.app M).hom = χ.inv.app M.X := rfl

variable [BraidedCategory C] [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A]

lemma tensor_quotient {M N P Q : Mod_ C A} (f : M ⟶ P) (g : N ⟶ Q) :
    RelativeTensor.π M N ≫ (f ⊗ₘ g).hom =
      (f.hom ⊗ₘ g.hom) ≫ RelativeTensor.π P Q := by
  rw [MonoidalCategory.tensorHom_def]
  change RelativeTensor.π M N ≫ (f ▷ N).hom ≫ (P ◁ g).hom = _
  rw [RelativeTensor.π_whiskerRight_assoc, RelativeTensor.π_whiskerLeft]
  simp only [MonoidalCategory.tensorHom_def, Category.assoc]

instance moduleCharacter_isMonoidal : NatTrans.IsMonoidal (moduleCharacter χ hχ).hom where
  unit := by
    change 𝟙 (𝟙_ (Mod_ C A)) ≫ (moduleCharacter χ hχ).hom.app (𝟙_ (Mod_ C A)) =
      𝟙 (𝟙_ (Mod_ C A))
    rw [Category.id_comp]
    apply Mod_.Hom.ext
    exact hχ
  tensor M N := by
    change 𝟙 (M ⊗ N) ≫ (moduleCharacter χ hχ).hom.app (M ⊗ N) =
      ((moduleCharacter χ hχ).hom.app M ⊗ₘ (moduleCharacter χ hχ).hom.app N) ≫ 𝟙 (M ⊗ N)
    rw [Category.id_comp]
    apply Eq.trans ?_ (Category.comp_id _).symm
    apply Mod_.Hom.ext
    apply (cancel_epi (RelativeTensor.π M N)).mp
    rw [tensor_quotient]
    have hn := χ.hom.naturality (RelativeTensor.π M N)
    change RelativeTensor.π M N ≫ χ.hom.app (RelativeTensor.tensorObj M N).X =
      χ.hom.app (M.X ⊗ N.X) ≫ RelativeTensor.π M N at hn
    rw [tensor_component] at hn
    exact hn

lemma free_compatible (X : C) :
    (moduleCharacter χ hχ).hom.app (InternalModule.free A X) =
      InternalModule.freeMap (χ.hom.app X) := by
  apply Mod_.Hom.ext
  change χ.hom.app (A ⊗ X) = A ◁ χ.hom.app X
  rw [tensor_component, hχ]
  exact MonoidalCategory.id_tensorHom A (χ.hom.app X)

lemma involutive (h : ∀ X : C, χ.hom.app X ≫ χ.hom.app X = 𝟙 X)
    (M : Mod_ C A) :
    (moduleCharacter χ hχ).hom.app M ≫ (moduleCharacter χ hχ).hom.app M = 𝟙 M := by
  apply Mod_.Hom.ext
  exact h M.X

end Paper18.Category.ModuleTensorCharacters
