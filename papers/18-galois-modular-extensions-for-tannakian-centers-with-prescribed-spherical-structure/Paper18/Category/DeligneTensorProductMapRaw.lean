import Paper18.Category.DiagonalAlgebraGeneral
import Paper18.Category.DeligneProductMap
import Paper18.Category.BraidedFunctorReverse

/-! # The actual tensor-product comparison on linear pair objects -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.Monoidal
open scoped TensorProduct
universe v u v' u'
namespace Paper18.Category.DeligneTensorProductMap
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] [BraidedCategory C]

/-- The actual raw central tensor-product functor after forgetting its half-braiding. -/
def rawTensor : LinearTensor C C ⥤ C := Drinfeld.linearFactorization C ⋙ Center.forget C
instance rawTensor_additive : (rawTensor C).Additive := by unfold rawTensor; infer_instance
instance rawTensor_linear : (rawTensor C).Linear ℂ := by unfold rawTensor; infer_instance
instance rawTensor_monoidal : (rawTensor C).Monoidal := by unfold rawTensor; infer_instance

@[simp] lemma rawTensor_map_pure (X Y : LinearTensor C C)
    (f : X.left ⟶ Y.left) (g : X.right ⟶ Y.right) :
    (rawTensor C).map (f ⊗ₜ[ℂ] g) = f ⊗ₘ g := by
  change f ▷ X.right ≫ Y.left ◁ g = f ⊗ₘ g
  exact (tensorHom_def f g).symm

lemma rawTensor_unit : ε (rawTensor C) = (λ_ (𝟙_ C)).inv := by
  dsimp only [rawTensor, Functor.LaxMonoidal.comp_ε]
  simp only [Center.forget_ε, Category.id_comp]
  change (ε (Drinfeld.factorizationBifunctor C)).f = _
  simp only [Drinfeld.factorizationBifunctor, Functor.LaxMonoidal.comp_ε, tensor_ε,
    Center.comp_f, Center.leftUnitor_inv_f]
  change (λ_ (𝟙_ C)).inv ≫ (𝟙 _ ⊗ₘ 𝟙 _) = _
  simp

lemma rawTensor_tensor (X Y : LinearTensor C C) :
    μ (rawTensor C) X Y =
      @tensorμ C _ _ (reverseBraiding C) X.left X.right Y.left Y.right := by
  change 𝟙 _ ≫ (
    (tensorμ ((Drinfeld.positive C).obj X.left) ((Drinfeld.negative C).obj X.right)
      ((Drinfeld.positive C).obj Y.left) ((Drinfeld.negative C).obj Y.right)).f ≫ (𝟙 _ ⊗ₘ 𝟙 _)) = _
  simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id]
  erw [Category.comp_id]
  simp only [tensorμ, Center.comp_f, Center.associator_hom_f, Center.associator_inv_f,
    Center.whiskerLeft_f, Center.whiskerRight_f]
  rfl

variable {C} {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] [BraidedCategory D]
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Braided]

/-- The actual strong tensorator is the natural comparison on all raw pairs. -/
def rawComparison : LinearTensor.map F F ⋙ rawTensor D ≅ rawTensor C ⋙ F :=
  NatIso.ofComponents (fun X => μIso F X.left X.right) (fun {X Y} f => by
    induction f using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [Functor.comp_map, LinearTensor.map_tmul, rawTensor_map_pure,
        Functor.comp_map, rawTensor_map_pure]
      change (F.map a ⊗ₘ F.map b) ≫ μ F Y.left Y.right =
        μ F X.left X.right ≫ F.map (a ⊗ₘ b)
      exact μ_natural F a b
    | add a b ha hb =>
      rw [CategoryTheory.Functor.map_add, CategoryTheory.Functor.map_add,
        Preadditive.add_comp, Preadditive.comp_add]
      exact congrArg₂ (· + ·) ha hb)

instance rawComparison_monoidal : NatTrans.IsMonoidal (rawComparison F).hom where
  unit := by
    dsimp only [rawComparison, NatIso.ofComponents_hom_app, μIso_hom,
      Functor.LaxMonoidal.comp_ε]
    simp only [Category.assoc]
    change ε (rawTensor D) ≫
      (rawTensor D).map (show (𝟙_ (LinearTensor D D)) ⟶
        (LinearTensor.map F F).obj (𝟙_ (LinearTensor C C)) from ε F ⊗ₜ[ℂ] ε F) ≫
        μ F (𝟙_ C) (𝟙_ C) =
      ε F ≫ F.map (ε (rawTensor C))
    rw [rawTensor_unit, rawTensor_map_pure, rawTensor_unit, ε_tensorHom_comp_μ]
    rw [← Category.assoc, ← leftUnitor_inv_naturality, Category.assoc, Iso.inv_hom_id_assoc]
  tensor X Y := by
    dsimp only [rawComparison, NatIso.ofComponents_hom_app, μIso_hom,
      Functor.LaxMonoidal.comp_μ]
    simp only [Category.assoc]
    change μ (rawTensor D) ((LinearTensor.map F F).obj X) ((LinearTensor.map F F).obj Y) ≫
      (rawTensor D).map (show (LinearTensor.map F F).obj X ⊗ (LinearTensor.map F F).obj Y ⟶
        (LinearTensor.map F F).obj (X ⊗ Y) from μ F X.left Y.left ⊗ₜ[ℂ] μ F X.right Y.right) ≫
        μ F (X.left ⊗ Y.left) (X.right ⊗ Y.right) =
      (μ F X.left X.right ⊗ₘ μ F Y.left Y.right) ≫
        μ F (X.left ⊗ X.right) (Y.left ⊗ Y.right) ≫ F.map (μ (rawTensor C) X Y)
    rw [rawTensor_tensor, rawTensor_map_pure, rawTensor_tensor]
    let hrev := braidedFunctorReverse F
    letI : BraidedCategory C := reverseBraiding C
    letI : BraidedCategory D := reverseBraiding D
    letI : F.Braided := hrev
    simpa only [hrev, braidedFunctorReverse, LinearTensor.map] using
      tensorμ_comp_μ_tensorHom_μ_comp_μ F X.left X.right Y.left Y.right

end Paper18.Category.DeligneTensorProductMap
