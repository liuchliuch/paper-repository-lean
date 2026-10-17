import Paper18.Category.SphericalizationKernelHom

/-! # Actual unit copowers and their linear Hom universal property -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [HasFiniteBiproducts C]

namespace IsUnitSum

def length {X : C} (hX : IsUnitSum X) : ℕ := Classical.choose hX

def decomposition {X : C} (hX : IsUnitSum X) :
    X ≅ ⨁ fun _ : Fin hX.length => 𝟙_ C := Classical.choice (Classical.choose_spec hX)

lemma biproduct_unit (J : Type) [Fintype J] : IsUnitSum (⨁ fun _ : J => 𝟙_ C) :=
  ⟨Fintype.card J, ⟨biproduct.whiskerEquiv
    (f := fun _ : J => 𝟙_ C) (g := fun _ : Fin (Fintype.card J) => 𝟙_ C)
    (Fintype.equivFin J) (fun _ => Iso.refl _)⟩⟩

lemma unit : IsUnitSum (𝟙_ C) :=
  .of_iso (biproductUniqueIso (fun _ : Fin 1 => 𝟙_ C)).symm (biproduct_unit (Fin 1))

lemma tensor [MonoidalPreadditive C] {X Y : C} (hX : IsUnitSum X) (hY : IsUnitSum Y) :
    IsUnitSum (X ⊗ Y) := by
  let f : Fin hX.length → C := fun _ => 𝟙_ C
  let g : Fin hY.length → C := fun _ => 𝟙_ C
  let e : X ⊗ Y ≅ ⨁ fun _ : (Σ _ : Fin hX.length, Fin hY.length) => 𝟙_ C :=
    (hX.decomposition ⊗ᵢ hY.decomposition) ≪≫ rightDistributor f (⨁ g) ≪≫
      biproduct.mapIso (fun _ => leftDistributor (𝟙_ C) g ≪≫
        biproduct.mapIso (fun _ => λ_ (𝟙_ C))) ≪≫
      biproductBiproductIso (fun _ : Fin hX.length => Fin hY.length)
        (fun _ _ => 𝟙_ C)
  exact .of_iso e (biproduct_unit _)

/-- Maps out of an actual unit sum are detected by all its unit points. -/
lemma hom_ext {X Y : C} (hX : IsUnitSum X) (f g : X ⟶ Y)
    (h : ∀ a : 𝟙_ C ⟶ X, a ≫ f = a ≫ g) : f = g := by
  apply (cancel_epi hX.decomposition.inv).mp
  apply biproduct.hom_ext'
  intro a
  simpa only [Category.assoc] using
    h (biproduct.ι (fun _ : Fin hX.length => 𝟙_ C) a ≫ hX.decomposition.inv)

variable [Linear ℂ C] [HasKernels C] [Simple (𝟙_ C)]
  [FiniteDimensional ℂ (𝟙_ C ⟶ 𝟙_ C)]

/-- A linear operation on unit points is represented by an actual morphism
out of a unit copower. -/
def homFromUnitMap {X Y : C} (hX : IsUnitSum X)
    (φ : (𝟙_ C ⟶ X) →ₗ[ℂ] (𝟙_ C ⟶ Y)) : X ⟶ Y :=
  hX.decomposition.hom ≫ biproduct.desc (fun a : Fin hX.length =>
    φ (biproduct.ι (fun _ : Fin hX.length => 𝟙_ C) a ≫ hX.decomposition.inv))

lemma comp_homFromUnitMap {X Y : C} (hX : IsUnitSum X)
    (φ : (𝟙_ C ⟶ X) →ₗ[ℂ] (𝟙_ C ⟶ Y)) (g : 𝟙_ C ⟶ X) :
    g ≫ hX.homFromUnitMap φ = φ g := by
  let f : Fin hX.length → C := fun _ => 𝟙_ C
  have hn (a : 𝟙_ C ⟶ 𝟙_ C) (b : 𝟙_ C ⟶ X) : a ≫ φ b = φ (a ≫ b) := by
    obtain ⟨c, rfl⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ a
    simp
  have ht : ∑ a : Fin hX.length,
      (g ≫ hX.decomposition.hom ≫ biproduct.π f a) ≫
        (biproduct.ι f a ≫ hX.decomposition.inv) = g := by
    simp only [← Category.assoc, ← Preadditive.sum_comp]
    simp only [Category.assoc, ← Preadditive.comp_sum, biproduct.total]
    change g ≫ hX.decomposition.hom ≫ 𝟙 _ ≫ hX.decomposition.inv = g
    simp only [Category.id_comp, Iso.hom_inv_id, Category.comp_id]
  calc
    g ≫ hX.homFromUnitMap φ = ∑ a : Fin hX.length,
        (g ≫ hX.decomposition.hom ≫ biproduct.π f a) ≫
          φ (biproduct.ι f a ≫ hX.decomposition.inv) := by
      unfold homFromUnitMap
      rw [biproduct.desc_eq]
      simp only [Preadditive.comp_sum, Category.assoc]
      rfl
    _ = ∑ a : Fin hX.length, φ ((g ≫ hX.decomposition.hom ≫ biproduct.π f a) ≫
        (biproduct.ι f a ≫ hX.decomposition.inv)) :=
      Finset.sum_congr rfl (fun _ _ => hn _ _)
    _ = φ g := by rw [← map_sum, ht]

end IsUnitSum
end Paper18.Category
