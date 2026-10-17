import Paper18.Category.LinearTensorMonoidal
import Paper18.Category.LinearTensorBraided
import Paper18.Category.LinearMatMonoidalLiftBraided

/-! # Actual componentwise functors on linear tensor products -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped TensorProduct
universe v u v' u' v₁ u₁ v₂ u₂
namespace Paper18.Category.LinearTensor
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  {E : Type u₁} [Category.{v₁} E] [Preadditive E] [Linear ℂ E]
  {H : Type u₂} [Category.{v₂} H] [Preadditive H] [Linear ℂ H]
  (F : C ⥤ E) [F.Additive] [F.Linear ℂ]
  (G : D ⥤ H) [G.Additive] [G.Linear ℂ]

def mapHom (X Y : LinearTensor C D) :
    (X ⟶ Y) →ₗ[ℂ] ((⟨F.obj X.left,G.obj X.right⟩ : LinearTensor E H) ⟶
      ⟨F.obj Y.left,G.obj Y.right⟩) :=
  TensorProduct.map (F.mapLinearMap ℂ : (X.left ⟶ Y.left) →ₗ[ℂ] _)
    (G.mapLinearMap ℂ : (X.right ⟶ Y.right) →ₗ[ℂ] _)

@[simp] lemma mapHom_tmul (X Y : LinearTensor C D)
    (f : X.left ⟶ Y.left) (g : X.right ⟶ Y.right) :
    mapHom F G X Y (f ⊗ₜ[ℂ] g) = F.map f ⊗ₜ[ℂ] G.map g := rfl

lemma mapHom_comp (X Y Z : LinearTensor C D) (f : X ⟶ Y) (g : Y ⟶ Z) :
    mapHom F G X Z (f ≫ g) = mapHom F G X Y f ≫ mapHom F G Y Z g := by
  induction f using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction g using TensorProduct.induction_on with
    | zero => simp
    | tmul c d =>
      change F.map (a ≫ c) ⊗ₜ[ℂ] G.map (b ≫ d) =
        (F.map a ≫ F.map c) ⊗ₜ[ℂ] (G.map b ≫ G.map d)
      rw [F.map_comp,G.map_comp]
    | add a b ha hb => simp_all [Preadditive.comp_add]
  | add a b ha hb => simp_all [Preadditive.add_comp]

/-- The actual linear functor on pairs and tensor-product Hom spaces. -/
def map : LinearTensor C D ⥤ LinearTensor E H where
  obj X := ⟨F.obj X.left,G.obj X.right⟩
  map f := mapHom F G _ _ f
  map_id X := by simp [id_def]
  map_comp {X Y Z} f g := mapHom_comp F G X Y Z f g

instance map_additive : (map F G).Additive where
  map_add := by intros; exact (mapHom F G _ _).map_add _ _

instance map_linear : (map F G).Linear ℂ where
  map_smul := by intros; exact (mapHom F G _ _).map_smul _ _

@[simp] lemma map_tmul (X Y : LinearTensor C D)
    (f : X.left ⟶ Y.left) (g : X.right ⟶ Y.right) :
    (map F G).map (f ⊗ₜ[ℂ] g) = F.map f ⊗ₜ[ℂ] G.map g := rfl

section FullyFaithful
variable [F.Full] [F.Faithful] [G.Full] [G.Faithful]

def mapHomEquiv (X Y : LinearTensor C D) :
    (X ⟶ Y) ≃ₗ[ℂ] ((map F G).obj X ⟶ (map F G).obj Y) :=
  TensorProduct.congr
    (LinearEquiv.ofBijective (F.mapLinearMap ℂ) ⟨F.map_injective,F.map_surjective⟩)
    (LinearEquiv.ofBijective (G.mapLinearMap ℂ) ⟨G.map_injective,G.map_surjective⟩)

lemma mapHomEquiv_eq (X Y : LinearTensor C D) (f : X ⟶ Y) :
    mapHomEquiv F G X Y f = (map F G).map f := by
  induction f using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb =>
    rw [map_add, ha, hb]
    exact ((mapHom F G X Y).map_add a b).symm

instance map_full : (map F G).Full where
  map_surjective {X Y} f := ⟨(mapHomEquiv F G X Y).symm f,
    (mapHomEquiv_eq F G X Y _).symm.trans ((mapHomEquiv F G X Y).apply_symm_apply f)⟩

instance map_faithful : (map F G).Faithful where
  map_injective {X Y} f g h := (mapHomEquiv F G X Y).injective (by
    simpa only [mapHomEquiv_eq] using h)

end FullyFaithful
end Paper18.Category.LinearTensor
