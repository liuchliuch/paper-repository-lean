import Paper18.Category.LinearTensorLift
import Paper18.Category.LinearTensorMonoidal
import Paper18.Category.LinearMatMonoidalLiftCoherence
import Mathlib.CategoryTheory.Functor.Currying

/-! # Actual monoidal transport from a separately linear uncurried functor

The tensor and unit isomorphisms are the given actual uncurried ones.
Their naturality extends over the actual tensor-product Hom spaces by
pure-tensor induction. Source and target universes are independent.
-/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped TensorProduct
universe vC uC vD uD vE uE
namespace Paper18.Category.LinearTensor
variable {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {D : Type uD} [Category.{vD} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  {E : Type uE} [Category.{vE} E] [Preadditive E] [Linear ℂ E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalLinear ℂ E]
  (F : C ⥤ D ⥤ E) [F.Additive] [F.Linear ℂ]
  [∀ X : C, (F.obj X).Additive] [∀ X : C, (F.obj X).Linear ℂ]
  [(Functor.uncurry.obj F).Monoidal]

@[simp] lemma lift_map_tmul_uncurry (X Y : LinearTensor C D)
    (f : X.left ⟶ Y.left) (g : X.right ⟶ Y.right) :
    (lift F).map (f ⊗ₜ[ℂ] g) =
      (Functor.uncurry.obj F).map
        (show (X.left,X.right) ⟶ (Y.left,Y.right) from (f,g)) := rfl

set_option maxHeartbeats 1000000 in
/-- Actual uncurried strong monoidal data extend to the actual linear
tensor category, with naturality proved on every genuine tensor Hom. -/
def uncurryCoreMonoidal : (lift F).CoreMonoidal where
  εIso := Functor.Monoidal.εIso (Functor.uncurry.obj F)
  μIso X Y := Functor.Monoidal.μIso (Functor.uncurry.obj F)
    (X.left,X.right) (Y.left,Y.right)
  μIso_hom_natural_left {X Y} f Z := by
    induction f using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      change (lift F).map (show X ⟶ Y from f ⊗ₜ[ℂ] g) ▷
          (Functor.uncurry.obj F).obj (Z.left,Z.right) ≫ _ = _ ≫
          (lift F).map
            (show X ⊗ Z ⟶ Y ⊗ Z from (f ⊗ₘ 𝟙 Z.left) ⊗ₜ[ℂ] (g ⊗ₘ 𝟙 Z.right))
      rw [lift_map_tmul_uncurry, lift_map_tmul_uncurry]
      simpa only [MonoidalCategory.tensorHom_id] using
        Functor.LaxMonoidal.μ_natural_left (Functor.uncurry.obj F)
          (show (X.left,X.right) ⟶ (Y.left,Y.right) from (f,g)) (Z.left,Z.right)
    | add f g hf hg =>
      rw [Functor.map_add (lift F), MonoidalPreadditive.add_whiskerRight,
        Preadditive.add_comp, whiskerRight_raw]
      simp only [map_add, LinearMap.add_apply]
      rw [Functor.map_add (lift F), Preadditive.comp_add]
      exact congrArg₂ (· + ·) hf hg
  μIso_hom_natural_right {X Y} Z f := by
    induction f using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      change (Functor.uncurry.obj F).obj (Z.left,Z.right) ◁
          (lift F).map (show X ⟶ Y from f ⊗ₜ[ℂ] g) ≫ _ = _ ≫
          (lift F).map
            (show Z ⊗ X ⟶ Z ⊗ Y from (𝟙 Z.left ⊗ₘ f) ⊗ₜ[ℂ] (𝟙 Z.right ⊗ₘ g))
      rw [lift_map_tmul_uncurry, lift_map_tmul_uncurry]
      simpa only [MonoidalCategory.id_tensorHom] using
        Functor.LaxMonoidal.μ_natural_right (Functor.uncurry.obj F) (Z.left,Z.right)
          (show (X.left,X.right) ⟶ (Y.left,Y.right) from (f,g))
    | add f g hf hg =>
      rw [Functor.map_add (lift F), MonoidalPreadditive.whiskerLeft_add,
        Preadditive.add_comp, whiskerLeft_raw]
      simp only [map_add, LinearMap.add_apply]
      rw [Functor.map_add (lift F), Preadditive.comp_add]
      exact congrArg₂ (· + ·) hf hg
  associativity X Y Z := by
    change _ ≫ _ ≫ (lift F).map
        (show (X ⊗ Y) ⊗ Z ⟶ X ⊗ (Y ⊗ Z) from
          (α_ X.left Y.left Z.left).hom ⊗ₜ[ℂ] (α_ X.right Y.right Z.right).hom) = _
    rw [lift_map_tmul_uncurry]
    exact Functor.LaxMonoidal.associativity (Functor.uncurry.obj F)
      (X.left,X.right) (Y.left,Y.right) (Z.left,Z.right)
  left_unitality X := by
    change _ = _ ≫ _ ≫ (lift F).map
      (show (𝟙_ (LinearTensor C D)) ⊗ X ⟶ X from
        (λ_ X.left).hom ⊗ₜ[ℂ] (λ_ X.right).hom)
    rw [lift_map_tmul_uncurry]
    exact Functor.LaxMonoidal.left_unitality (Functor.uncurry.obj F) (X.left,X.right)
  right_unitality X := by
    change _ = _ ≫ _ ≫ (lift F).map
      (show X ⊗ (𝟙_ (LinearTensor C D)) ⟶ X from
        (ρ_ X.left).hom ⊗ₜ[ℂ] (ρ_ X.right).hom)
    rw [lift_map_tmul_uncurry]
    exact Functor.LaxMonoidal.right_unitality (Functor.uncurry.obj F) (X.left,X.right)

instance liftMonoidalOfUncurry : (lift F).Monoidal := (uncurryCoreMonoidal F).toMonoidal

@[simp] lemma liftMonoidalOfUncurry_ε : Functor.LaxMonoidal.ε (lift F) =
    Functor.LaxMonoidal.ε (Functor.uncurry.obj F) := rfl

@[simp] lemma liftMonoidalOfUncurry_μ (X Y : LinearTensor C D) :
    Functor.LaxMonoidal.μ (lift F) X Y =
      Functor.LaxMonoidal.μ (Functor.uncurry.obj F) (X.left,X.right) (Y.left,Y.right) := rfl

instance deligneLiftMonoidalOfUncurry [HasFiniteBiproducts E] :
    (DeligneProduct.lift F).Monoidal :=
  inferInstanceAs ((linearMatLift (lift F)).Monoidal)

end Paper18.Category.LinearTensor
