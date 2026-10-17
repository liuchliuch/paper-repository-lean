import Paper18.Category.FixedBoundaryLocalCrossing
import Paper18.Category.FixedBoundaryAlgebraTranslation
import Paper18.Category.FixedBoundaryCrossedBraiding

/-! # The actual boundary module functor preserves the other crossed map

The specified alpha gives the actual comparison with algebra translation.
The original ambient braided-functor equation then proves preservation of
the translated crossing before the balancing quotient.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category
open RelativeTensor FixedBoundary
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N]
  [RightRigidCategory N] [HasCoequalizers N]
  {i : A ⥤ N} [i.Braided] (P : BoundaryAutoequivalence i) (R : A)
  [MonObj R] [IsCommMonObj R] (t : R ≅ R) [IsMonHom t.hom]

local instance imageAlgebraTranslation : IsMonHom (i.mapIso t).hom := by
  change IsMonHom (i.map t.hom)
  infer_instance

/-- The actual algebra comparison intertwines monodromy and the same
boundary algebra translation, by naturality of the specified alpha. -/
theorem BoundaryAutoequivalence.moduleFunctor_translated_monodromy
    (L : Mod_ N (i.obj R))
    (hL : (doubleBraiding (i.obj R) L.X).hom = (i.map t.hom) ▷ L.X) :
    (doubleBraiding (i.obj R) ((P.moduleFunctor R).obj L).X).hom =
      (i.map t.hom) ▷ ((P.moduleFunctor R).obj L).X := by
  apply (cancel_mono ((P.boundaryAlgebraIso R).inv ▷ P.functor.obj L.X ≫
    Functor.LaxMonoidal.μ P.functor (i.obj R) L.X)).mp
  change (doubleBraiding (i.obj R) (P.functor.obj L.X)).hom ≫
      (P.boundaryAlgebraIso R).inv ▷ P.functor.obj L.X ≫
        Functor.LaxMonoidal.μ P.functor (i.obj R) L.X =
    (i.map t.hom ▷ P.functor.obj L.X) ≫
      (P.boundaryAlgebraIso R).inv ▷ P.functor.obj L.X ≫
        Functor.LaxMonoidal.μ P.functor (i.obj R) L.X
  rw [← doubleBraiding_naturality_left_assoc,
    ← tensorator_map_doubleBraiding, hL, ← Functor.LaxMonoidal.μ_natural_left]
  rw [← comp_whiskerRight_assoc, P.inverse_algebra_endomorphism R t.hom,
    comp_whiskerRight]
  simp only [Category.assoc]

/-- The actual specified-boundary functor preserves the genuine crossing
with translated target. The two monodromy equalities concern actual
morphisms and are supplied by the proved degree/translation identity. -/
theorem BoundaryAutoequivalence.moduleFunctor_translatedBraiding
    (M L : Mod_ N (i.obj R))
    (hL : (doubleBraiding (i.obj R) L.X).hom = (i.map t.hom) ▷ L.X) :
    Functor.LaxMonoidal.μ (P.moduleFunctor R) M L ≫
        (P.moduleFunctor R).map (translatedBraidingHom (i.mapIso t) M L hL) =
      translatedBraidingHom (i.mapIso t) ((P.moduleFunctor R).obj M)
        ((P.moduleFunctor R).obj L) (P.moduleFunctor_translated_monodromy R t L hL) ≫
          ((P.moduleFunctor R).obj L ◁ (P.moduleComapComparison R t.hom).inv.app M) ≫
            Functor.LaxMonoidal.μ (P.moduleFunctor R) L ((Mod_.comap (i.map t.hom)).obj M) := by
  apply module_hom_ext
  change π ((P.moduleFunctor R).obj M) ((P.moduleFunctor R).obj L) ≫
      (Functor.LaxMonoidal.μ (P.moduleFunctor R) M L).hom ≫
        P.functor.map (translatedBraidingHom (i.mapIso t) M L hL).hom =
    π ((P.moduleFunctor R).obj M) ((P.moduleFunctor R).obj L) ≫
      (translatedBraidingHom (i.mapIso t) ((P.moduleFunctor R).obj M)
        ((P.moduleFunctor R).obj L) (P.moduleFunctor_translated_monodromy R t L hL)).hom ≫
          (((P.moduleFunctor R).obj L ◁ (P.moduleComapComparison R t.hom).inv.app M)).hom ≫
            (Functor.LaxMonoidal.μ (P.moduleFunctor R) L ((Mod_.comap (i.map t.hom)).obj M)).hom
  rw [P.π_moduleFunctor_μ_assoc, ← P.functor.map_comp,
    π_translatedBraidingHom, P.functor.map_comp,
    π_translatedBraidingHom_assoc, π_whiskerLeft_assoc]
  rw [P.moduleComapComparison_inv_hom R t.hom M]
  erw [whiskerLeft_id, Category.id_comp, P.π_moduleFunctor_μ]
  exact Functor.LaxBraided.braided_assoc M.X L.X _

end Paper18.Category
