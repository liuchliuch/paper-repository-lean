import Paper18.Category.GraphPicardGraphTensor

/-! # Explicit tensor and factor maps of the actual graph functor -/
noncomputable section
set_option maxHeartbeats 2000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped TensorProduct
universe v u
namespace Paper18.Category.GraphPicard
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [CategoryTheory.Limits.HasFiniteBiproducts D]
  (α : D ⥤ D) [α.Braided] [α.Additive] [α.Linear ℂ]

@[simp] lemma graphRaw_map_pure {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    (graphRaw α).map
      (show (⟨X,Y⟩ : LinearTensor D D) ⟶ ⟨X',Y'⟩ from f ⊗ₜ[ℂ] g) =
      (Drinfeld.positive D).map f ⊗ₘ (Drinfeld.negative D).map (α.map g) := by
  dsimp only [graphRaw, Functor.comp_map]
  rw [LinearTensor.map_tmul, Drinfeld.linearFactorization_map_tmul]
  rfl

/-- The actual pure graph tensorator consists of the actual central
crossing and the specified actual tensorator of the braided functor. -/
lemma graphRaw_tensor (X Y X' Y' : D) :
    Functor.LaxMonoidal.μ (graphRaw α)
        (⟨X,Y⟩ : LinearTensor D D) (⟨X',Y'⟩ : LinearTensor D D) =
      tensorμ ((Drinfeld.positive D).obj X) ((Drinfeld.negative D).obj (α.obj Y))
          ((Drinfeld.positive D).obj X') ((Drinfeld.negative D).obj (α.obj Y')) ≫
        (Functor.LaxMonoidal.μ (Drinfeld.positive D) X X' ⊗ₘ
          (Functor.LaxMonoidal.μ (Drinfeld.negative D) (α.obj Y) (α.obj Y') ≫
            (Drinfeld.negative D).map (Functor.LaxMonoidal.μ α Y Y'))) := by
  dsimp only [graphRaw, Functor.LaxMonoidal.comp_μ]
  change Functor.LaxMonoidal.μ (Drinfeld.linearFactorization D)
      (⟨X,α.obj Y⟩ : LinearTensor D D) (⟨X',α.obj Y'⟩ : LinearTensor D D) ≫
    (Drinfeld.linearFactorization D).map
      (show (⟨X ⊗ X',α.obj Y ⊗ α.obj Y'⟩ : LinearTensor D D) ⟶
        ⟨X ⊗ X',α.obj (Y ⊗ Y')⟩ from
          (𝟙 (X ⊗ X')) ⊗ₜ[ℂ] Functor.LaxMonoidal.μ α Y Y') = _
  rw [Drinfeld.linearFactorization_map_tmul, CategoryTheory.Functor.map_id]
  apply Center.Hom.ext
  dsimp only [Drinfeld.linearFactorization_monoidal, Drinfeld.linearFactorizationCoreMonoidal,
    Functor.CoreMonoidal.toMonoidal, Functor.CoreMonoidal.toLaxMonoidal,
    Drinfeld.factorizationBifunctor, Functor.LaxMonoidal.comp_μ]
  simp only [Center.comp_f, Center.tensorHom_f, Center.ofBraided_μ_f,
    Drinfeld.negative_μ_f]
  simp

end Paper18.Category.GraphPicard
