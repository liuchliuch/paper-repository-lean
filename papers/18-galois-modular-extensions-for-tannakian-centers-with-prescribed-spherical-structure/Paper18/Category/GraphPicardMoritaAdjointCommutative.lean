import Paper18.Category.GraphPicardMoritaAdjoint
import Paper18.Category.DrinfeldBasic
import Paper18.Category.DrinfeldLinear

/-! # Commutativity forced by an actual central lift

Naturality of an actual half-braiding at a map to the tensor unit is
enough for its self-crossing to disappear after the two maps are closed.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped MonObj
universe v u w v' u'
namespace Paper18.Category.GraphPicard.Morita
variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

/-- Closing both legs of an actual central self-crossing gives the same
map as closing the two uncrossed legs. -/
lemma halfBraiding_character_square (Z : Center D) (q : Z.1 ⟶ 𝟙_ D) :
    (Z.2.β Z.1).hom ≫ (q ⊗ₘ q) ≫ (λ_ (𝟙_ D)).hom =
      (q ⊗ₘ q) ≫ (λ_ (𝟙_ D)).hom := by
  calc
    _ = Z.1 ◁ q ≫ (ρ_ Z.1).hom ≫ q := by
      rw [tensorHom_def, Category.assoc, ← Z.2.naturality_assoc,
        Drinfeld.halfBraiding_unit]
      simp only [Category.assoc, leftUnitor_naturality, Iso.inv_hom_id_assoc]
    _ = (q ⊗ₘ q) ≫ (ρ_ (𝟙_ D)).hom := by
      rw [tensorHom_def']
      simp only [Category.assoc, rightUnitor_naturality]
    _ = _ := by rw [unitors_equal]

section Adjoint
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [MonoidalCategory C] [BraidedCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasFiniteBiproducts D] [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (K : C ⥤ Center D) [K.Braided] [K.Additive] [K.Linear ℂ]

/-- The underlying actual central functor. -/
abbrev centralUnderlying : C ⥤ D := K ⋙ Center.forget D

/-- The genuine braided law of the central lift, expressed through the
actual oplax tensor comparison of its underlying functor. -/
@[reassoc] lemma centralUnderlying_braiding (X Y : C) :
    (centralUnderlying K).map (β_ X Y).hom ≫ δ (centralUnderlying K) Y X =
      δ (centralUnderlying K) X Y ≫ ((K.obj X).2.β (K.obj Y).1).hom := by
  have h := congrArg Center.Hom.f (Functor.Braided.braided (F := K) X Y)
  simp only [Center.comp_f] at h
  have hmu (U V : C) : Functor.LaxMonoidal.μ (centralUnderlying K) U V =
      (Functor.LaxMonoidal.μ K U V).f := by
    change 𝟙 _ ≫ _ = _
    exact Category.id_comp _
  have h' : Functor.LaxMonoidal.μ (centralUnderlying K) X Y ≫
      (centralUnderlying K).map (β_ X Y).hom =
        ((K.obj X).2.β (K.obj Y).1).hom ≫
          Functor.LaxMonoidal.μ (centralUnderlying K) Y X := by
    rw [hmu, hmu]
    exact h
  apply (cancel_epi (Functor.LaxMonoidal.μ (centralUnderlying K) X Y)).mp
  rw [← Category.assoc, h']
  simp only [Category.assoc, Functor.Monoidal.μ_δ, Functor.Monoidal.μ_δ_assoc]
  exact Category.comp_id _

/-- The right-adjoint unit algebra is actually commutative whenever the
functor has a genuine braided central lift. This needs neither a target
braiding nor a target pivotal structure. -/
instance centralAdjointAlgebra_comm :
    IsCommMonObj (DiagonalAlgebra.semisimpleAdjointAlgebra S (centralUnderlying K)) where
  mul_comm := by
    apply adjointUnit_hom_ext S (centralUnderlying K)
    simp only [Functor.map_comp, Category.assoc]
    rw [DiagonalAlgebra.semisimpleAdjointAlgebra_mul_counit]
    let A := DiagonalAlgebra.semisimpleAdjointAlgebra S (centralUnderlying K)
    let q := DiagonalAlgebra.semisimpleAdjointAlgebraCounit S (centralUnderlying K)
    calc
      _ = δ (centralUnderlying K) A A ≫ ((K.obj A).2.β (K.obj A).1).hom ≫
          (q ⊗ₘ q) ≫ (λ_ (𝟙_ D)).hom := by
        simpa only [Category.assoc] using
          congrArg (fun f => f ≫ (q ⊗ₘ q) ≫ (λ_ (𝟙_ D)).hom)
            (centralUnderlying_braiding K A A)
      _ = _ := congrArg (fun f => δ (centralUnderlying K) A A ≫ f)
        (halfBraiding_character_square (K.obj A) q)

end Adjoint

end Paper18.Category.GraphPicard.Morita
