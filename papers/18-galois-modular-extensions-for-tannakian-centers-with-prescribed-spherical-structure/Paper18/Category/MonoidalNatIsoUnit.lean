import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # The unit equation follows from the tensor equation for an invertible comparison

For strong monoidal functors, an invertible natural transformation that
preserves tensorators automatically preserves the unit maps. The proof
uses actual left and right unitors and invertibility of the unit maps.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
open CategoryTheory.Functor.Monoidal
universe v u v' u'
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  {F H : C ⥤ D} [F.Monoidal] [H.Monoidal] (e : F ≅ H)

/-- An actual invertible natural transformation preserving the tensor maps
of strong monoidal functors automatically preserves their actual unit maps. -/
theorem monoidalNatIso_unit_of_tensor
    (ht : ∀ X Y : C, μ F X Y ≫ e.hom.app (X ⊗ Y) =
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ μ H X Y) :
    ε F ≫ e.hom.app (𝟙_ C) = ε H := by
  have h : (ε F ≫ e.hom.app (𝟙_ C)) ▷ H.obj (𝟙_ C) =
      ε H ▷ H.obj (𝟙_ C) := by
    apply (cancel_mono (μ H (𝟙_ C) (𝟙_ C) ≫ H.map (λ_ (𝟙_ C)).hom)).mp
    apply (cancel_epi ((𝟙_ D) ◁ e.hom.app (𝟙_ C))).mp
    simp only [comp_whiskerRight, assoc]
    rw [whisker_exchange_assoc (ε F) (e.hom.app (𝟙_ C))]
    rw [← tensorHom_def'_assoc, ← reassoc_of% (ht (𝟙_ C) (𝟙_ C))]
    rw [← e.hom.naturality (λ_ (𝟙_ C)).hom]
    rw [reassoc_of% (Functor.LaxMonoidal.left_unitality F (𝟙_ C)).symm,
      (Functor.LaxMonoidal.left_unitality H (𝟙_ C)).symm]
    exact (leftUnitor_naturality (e.hom.app (𝟙_ C))).symm
  have hh := congrArg (fun f => f ≫ H.obj (𝟙_ C) ◁ η H) h
  dsimp only at hh
  rw [← whisker_exchange, ← whisker_exchange] at hh
  have hh' := (cancel_epi ((𝟙_ D) ◁ η H)).mp hh
  have hh'' := congrArg (fun f => f ≫ (ρ_ (H.obj (𝟙_ C))).hom) hh'
  dsimp only at hh''
  rw [rightUnitor_naturality, rightUnitor_naturality] at hh''
  exact (cancel_epi (ρ_ (𝟙_ D)).hom).mp hh''

/-- Full actual monoidal coherence for an invertible natural comparison
can be established by checking its tensor equation. -/
def monoidalNatIso_isMonoidal_of_tensor
    (ht : ∀ X Y : C, μ F X Y ≫ e.hom.app (X ⊗ Y) =
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ μ H X Y) : NatTrans.IsMonoidal e.hom where
  unit := monoidalNatIso_unit_of_tensor e ht
  tensor := ht

end Paper18.Category
