import Paper18.Category.FixedBoundaryScalarGauge
import Paper18.Category.FixedBoundaryHomogeneousBoundary
import Paper18.Category.ModuleFunctorFiniteContraction

/-! # Actual coherence of the tensorator defect

Transporting the genuine monoidal structure along the genuine ordinary
natural isomorphism provides all defect coherences.  No scalar coordinates
are supplied.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

section General
variable (F : C ⥤ C) [F.Monoidal] (e : F ≅ 𝟭 C)

/-- The actual ordinary comparison transports the actual monoidal structure
onto identity. Its tensorator is precisely the actual defect. -/
def defectIdentityMonoidal : (𝟭 C).Monoidal := Functor.Monoidal.transport e

@[simp] theorem defectIdentityMonoidal_μ (X Y : C) :
    letI m := defectIdentityMonoidal F e
    letI := m.toLaxMonoidal
    Functor.LaxMonoidal.μ (𝟭 C) X Y = tensoratorDefect F e X Y := rfl

instance tensoratorDefect_isIso (X Y : C) : IsIso (tensoratorDefect F e X Y) := by
  dsimp only [tensoratorDefect]
  infer_instance

/-- The actual tensorator defect satisfies the actual associativity square. -/
@[reassoc] theorem tensoratorDefect_associativity (X Y Z : C) :
    (tensoratorDefect F e X Y ▷ Z) ≫ tensoratorDefect F e (X ⊗ Y) Z ≫
        (α_ X Y Z).hom =
      (α_ X Y Z).hom ≫ X ◁ tensoratorDefect F e Y Z ≫
        tensoratorDefect F e X (Y ⊗ Z) := by
  letI m := defectIdentityMonoidal F e
  letI := m.toLaxMonoidal
  exact Functor.LaxMonoidal.associativity (𝟭 C) X Y Z

/-- An actual monoidal comparison at a pair has exactly identity defect. -/
lemma tensoratorDefect_eq_id_of_tensor (X Y : C)
    (h : Functor.LaxMonoidal.μ F X Y ≫ e.hom.app (X ⊗ Y) =
      e.hom.app X ⊗ₘ e.hom.app Y) : tensoratorDefect F e X Y = 𝟙 _ := by
  rw [tensoratorDefect, h, tensorHom_comp_tensorHom]
  simp only [Iso.inv_hom_id_app]
  change (𝟙 X ⊗ₘ 𝟙 Y) = 𝟙 (X ⊗ Y)
  simp

/-- Identity defect is equivalent to the actual tensor equation. -/
lemma tensoratorDefect_eq_id_iff_tensor (X Y : C) :
    tensoratorDefect F e X Y = 𝟙 (X ⊗ Y) ↔
      Functor.LaxMonoidal.μ F X Y ≫ e.hom.app (X ⊗ Y) =
        e.hom.app X ⊗ₘ e.hom.app Y := by
  constructor
  · intro hd
    apply (cancel_epi (e.inv.app X ⊗ₘ e.inv.app Y)).mp
    change tensoratorDefect F e X Y = _
    rw [hd, tensorHom_comp_tensorHom]
    simp only [Iso.inv_hom_id_app]
    change 𝟙 (X ⊗ Y) = (𝟙 X ⊗ₘ 𝟙 Y)
    simp
  · exact tensoratorDefect_eq_id_of_tensor F e X Y

end General

section Braided
variable [BraidedCategory C] (F : C ⥤ C) [F.Braided] (e : F ≅ 𝟭 C)

/-- Braidedness of the original functor makes the defect symmetric under
the actual ambient crossing. -/
@[reassoc] theorem tensoratorDefect_braiding (X Y : C) :
    tensoratorDefect F e X Y ≫ (β_ X Y).hom =
      (β_ X Y).hom ≫ tensoratorDefect F e Y X := by
  dsimp only [tensoratorDefect]
  simp only [Category.assoc]
  have hn := e.hom.naturality (β_ X Y).hom
  dsimp only [Functor.id_map] at hn
  rw [← hn]
  rw [Functor.LaxBraided.braided_assoc]
  rw [reassoc_of% (BraidedCategory.braiding_naturality (e.inv.app X) (e.inv.app Y))]

end Braided

end Paper18.Category.FixedBoundary
