import Paper18.Category.DrinfeldEquivalenceMapBasic

/-! # Tensor coherence of transported half-braidings -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal CategoryTheory.Functor.Monoidal
universe v u v' u'
namespace Paper18.Category.DrinfeldEquivalence
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

/-- Applying an actual strong tensor functor to the actual half-braiding
hexagon gives its tensorator-normalized image hexagon. -/
lemma image_hexagon (F : C ⥤ D) [F.Monoidal] (Z : Center C) (U V : C) :
    F.obj Z.1 ◁ μ F U V ≫ μ F Z.1 (U ⊗ V) ≫
      F.map (Z.2.β (U ⊗ V)).hom ≫ δ F (U ⊗ V) Z.1 =
    (α_ (F.obj Z.1) (F.obj U) (F.obj V)).inv ≫
      (μ F Z.1 U ≫ F.map (Z.2.β U).hom ≫ δ F U Z.1) ▷ F.obj V ≫
        (α_ (F.obj U) (F.obj Z.1) (F.obj V)).hom ≫
          F.obj U ◁ (μ F Z.1 V ≫ F.map (Z.2.β V).hom ≫ δ F V Z.1) ≫
            (α_ (F.obj U) (F.obj V) (F.obj Z.1)).inv ≫ μ F U V ▷ F.obj Z.1 := by
  have h := congrArg (fun f => F.obj Z.1 ◁ μ F U V ≫ μ F Z.1 (U ⊗ V) ≫
    F.map f ≫ δ F (U ⊗ V) Z.1) (Z.2.monoidal U V)
  dsimp only at h
  simp only [F.map_comp, Functor.Monoidal.map_associator_inv F,
    Functor.Monoidal.map_associator F, Functor.Monoidal.map_whiskerLeft F,
    Functor.Monoidal.map_whiskerRight F, assoc, μ_δ_assoc,
    whiskerLeft_μ_δ_assoc, whiskerRight_μ_δ_assoc, μ_δ, comp_id] at h
  simpa only [comp_whiskerRight, whiskerLeft_comp, assoc] using h

variable (E : C ≌ D) [E.functor.Monoidal]

/-- The transported family satisfies its actual tensor hexagon on all
pairs of objects in the equivalence's actual image. -/
lemma halfIso_image_monoidal (Z : Center C) (U V : C) :
    (halfIso E Z (E.functor.obj U ⊗ E.functor.obj V)).hom =
      (α_ _ _ _).inv ≫ (halfIso E Z (E.functor.obj U)).hom ▷ E.functor.obj V ≫
        (α_ _ _ _).hom ≫ E.functor.obj U ◁ (halfIso E Z (E.functor.obj V)).hom ≫
          (α_ _ _ _).inv := by
  apply (cancel_mono (μ E.functor U V ▷ E.functor.obj Z.1)).mp
  rw [← halfIso_naturality, halfIso_image]
  simp only [assoc, halfIso_image]
  exact image_hexagon E.functor Z U V

end Paper18.Category.DrinfeldEquivalence
