import Paper18.Category.FactorizationDeligne
import Paper18.Category.LinearTensorMonoidal
import Paper18.Category.LinearMatMonoidalLiftCoherence

/-! # The strong monoidal structure of the actual linear factorization -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped TensorProduct
universe v u
namespace Paper18.Category.Drinfeld
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] [BraidedCategory C]

@[simp] lemma linearFactorization_map_pure (X Y : LinearTensor C C)
    (f : X.left ⟶ Y.left) (g : X.right ⟶ Y.right) :
    (linearFactorization C).map (f ⊗ₜ[ℂ] g) =
      (factorizationBifunctor C).map
        (show (X.left,X.right) ⟶ (Y.left,Y.right) from (f,g)) := by
  change (positive C).map f ▷ (negative C).obj X.right ≫
    (positive C).obj Y.left ◁ (negative C).map g = _
  exact (MonoidalCategory.tensorHom_def _ _).symm

set_option maxHeartbeats 1000000 in
def linearFactorizationCoreMonoidal : (linearFactorization C).CoreMonoidal where
  εIso := Functor.Monoidal.εIso (factorizationBifunctor C)
  μIso X Y := Functor.Monoidal.μIso (factorizationBifunctor C)
    (X.left,X.right) (Y.left,Y.right)
  μIso_hom_natural_left {X Y} f Z := by
    induction f using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      change (linearFactorization C).map (show X ⟶ Y from f ⊗ₜ[ℂ] g) ▷
          (factorizationBifunctor C).obj (Z.left,Z.right) ≫ _ = _ ≫
          (linearFactorization C).map
            (show X ⊗ Z ⟶ Y ⊗ Z from (f ⊗ₘ 𝟙 Z.left) ⊗ₜ[ℂ] (g ⊗ₘ 𝟙 Z.right))
      rw [linearFactorization_map_pure, linearFactorization_map_pure]
      simpa only [MonoidalCategory.tensorHom_id] using
        Functor.LaxMonoidal.μ_natural_left (factorizationBifunctor C)
          (show (X.left,X.right) ⟶ (Y.left,Y.right) from (f,g)) (Z.left,Z.right)
    | add f g hf hg =>
      rw [Functor.map_add (linearFactorization C), MonoidalPreadditive.add_whiskerRight,
        Preadditive.add_comp, LinearTensor.whiskerRight_raw]
      simp only [map_add, LinearMap.add_apply]
      rw [Functor.map_add (linearFactorization C), Preadditive.comp_add]
      exact congrArg₂ (· + ·) hf hg
  μIso_hom_natural_right {X Y} Z f := by
    induction f using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      change (factorizationBifunctor C).obj (Z.left,Z.right) ◁
          (linearFactorization C).map (show X ⟶ Y from f ⊗ₜ[ℂ] g) ≫ _ = _ ≫
          (linearFactorization C).map
            (show Z ⊗ X ⟶ Z ⊗ Y from (𝟙 Z.left ⊗ₘ f) ⊗ₜ[ℂ] (𝟙 Z.right ⊗ₘ g))
      rw [linearFactorization_map_pure, linearFactorization_map_pure]
      simpa only [MonoidalCategory.id_tensorHom] using
        Functor.LaxMonoidal.μ_natural_right (factorizationBifunctor C) (Z.left,Z.right)
          (show (X.left,X.right) ⟶ (Y.left,Y.right) from (f,g))
    | add f g hf hg =>
      rw [Functor.map_add (linearFactorization C), MonoidalPreadditive.whiskerLeft_add,
        Preadditive.add_comp, LinearTensor.whiskerLeft_raw]
      simp only [map_add, LinearMap.add_apply]
      rw [Functor.map_add (linearFactorization C), Preadditive.comp_add]
      exact congrArg₂ (· + ·) hf hg
  associativity X Y Z := by
    change _ ≫ _ ≫ (linearFactorization C).map
        (show (X ⊗ Y) ⊗ Z ⟶ X ⊗ (Y ⊗ Z) from
          (α_ X.left Y.left Z.left).hom ⊗ₜ[ℂ] (α_ X.right Y.right Z.right).hom) = _
    rw [linearFactorization_map_pure]
    exact Functor.LaxMonoidal.associativity (factorizationBifunctor C)
      (X.left,X.right) (Y.left,Y.right) (Z.left,Z.right)
  left_unitality X := by
    change _ = _ ≫ _ ≫ (linearFactorization C).map
      (show (𝟙_ (LinearTensor C C)) ⊗ X ⟶ X from
        (λ_ X.left).hom ⊗ₜ[ℂ] (λ_ X.right).hom)
    rw [linearFactorization_map_pure]
    exact Functor.LaxMonoidal.left_unitality (factorizationBifunctor C) (X.left,X.right)
  right_unitality X := by
    change _ = _ ≫ _ ≫ (linearFactorization C).map
      (show X ⊗ (𝟙_ (LinearTensor C C)) ⟶ X from
        (ρ_ X.left).hom ⊗ₜ[ℂ] (ρ_ X.right).hom)
    rw [linearFactorization_map_pure]
    exact Functor.LaxMonoidal.right_unitality (factorizationBifunctor C) (X.left,X.right)

instance linearFactorization_monoidal : (linearFactorization C).Monoidal :=
  (linearFactorizationCoreMonoidal C).toMonoidal

variable [HasFiniteBiproducts C]

instance deligneFactorization_monoidal : (deligneFactorization C).Monoidal :=
  inferInstanceAs ((linearMatLift (linearFactorization C)).Monoidal)

end Paper18.Category.Drinfeld
