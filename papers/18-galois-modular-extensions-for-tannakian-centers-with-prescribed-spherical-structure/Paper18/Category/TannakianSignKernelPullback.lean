import Paper18.Category.SignKernel

/-! # Pulling actual tensor characters through fully faithful tensor functors -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal
universe v u v' u'
namespace Paper18.Category.TannakianSignKernel
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Full] [F.Faithful] [F.Monoidal]
  (χ : 𝟭 D ≅ 𝟭 D) [NatTrans.IsMonoidal χ.hom]

/-- Actual fully faithful preimages of the character components. -/
def pullbackCharacter : 𝟭 C ≅ 𝟭 C :=
  NatIso.ofComponents (fun X => F.preimageIso (χ.app (F.obj X))) (fun {X Y} f => by
    apply F.map_injective
    simpa using χ.hom.naturality (F.map f))

@[simp] lemma map_pullbackCharacter (X : C) :
    F.map ((pullbackCharacter F χ).hom.app X) = χ.hom.app (F.obj X) :=
  F.map_preimage _

instance pullbackCharacter_monoidal : (pullbackCharacter F χ).hom.IsMonoidal where
  unit := by
    change 𝟙 (𝟙_ C) ≫ (pullbackCharacter F χ).hom.app (𝟙_ C) = 𝟙 (𝟙_ C)
    rw [Category.id_comp]
    apply F.map_injective
    rw [map_pullbackCharacter]
    erw [F.map_id]
    apply (cancel_epi (ε F)).mp
    have hn := χ.hom.naturality (ε F)
    change ε F ≫ χ.hom.app (F.obj (𝟙_ C)) = χ.hom.app (𝟙_ D) ≫ ε F at hn
    have hu : χ.hom.app (𝟙_ D) = 𝟙 _ := by
      simpa using (NatTrans.IsMonoidal.unit (τ := χ.hom))
    rw [hu] at hn
    simpa using hn
  tensor X Y := by
    change 𝟙 (X ⊗ Y) ≫ (pullbackCharacter F χ).hom.app (X ⊗ Y) =
      ((pullbackCharacter F χ).hom.app X ⊗ₘ (pullbackCharacter F χ).hom.app Y) ≫ 𝟙 (X ⊗ Y)
    erw [Category.id_comp, Category.comp_id]
    apply F.map_injective
    rw [map_pullbackCharacter]
    apply (cancel_epi (μ F X Y)).mp
    calc
      _ = χ.hom.app (F.obj X ⊗ F.obj Y) ≫ μ F X Y := χ.hom.naturality (μ F X Y)
      _ = (χ.hom.app (F.obj X) ⊗ₘ χ.hom.app (F.obj Y)) ≫ μ F X Y := by
        have ht : χ.hom.app (F.obj X ⊗ F.obj Y) =
            χ.hom.app (F.obj X) ⊗ₘ χ.hom.app (F.obj Y) := by
          simpa using (NatTrans.IsMonoidal.tensor (τ := χ.hom) (F.obj X) (F.obj Y))
        rw [ht]
      _ = _ := by
        rw [← map_pullbackCharacter F χ X, ← map_pullbackCharacter F χ Y]
        exact Functor.LaxMonoidal.μ_natural F _ _

lemma pullbackCharacter_involutive
    (hχ : ∀ X : D, χ.hom.app X ≫ χ.hom.app X = 𝟙 X) (X : C) :
    (pullbackCharacter F χ).hom.app X ≫ (pullbackCharacter F χ).hom.app X = 𝟙 X := by
  apply F.map_injective
  rw [CategoryTheory.Functor.map_comp, map_pullbackCharacter, hχ]
  exact (F.map_id X).symm

end Paper18.Category.TannakianSignKernel
