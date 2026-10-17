import Paper18.Category.FixedBoundaryBasic

/-! # Monoidal comparison reflected by a fully faithful tensor functor

This is ordinary categorical reflection of the unit and tensor squares.
It provides the final lifting step for actual regular descent.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u v' u' v'' u''
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  {E : Type u''} [Category.{v''} E] [MonoidalCategory E]
  {F G : C ⥤ D} [F.Monoidal] [G.Monoidal]
  (K : D ⥤ E) [K.Monoidal] [K.Full] [K.Faithful]
  (e : F ⋙ K ≅ G ⋙ K) [NatTrans.IsMonoidal e.hom]

/-- The actual fully faithful preimage comparison is monoidal, as the
faithful tensor functor reflects both defining squares. -/
instance fullyFaithfulCancelRightMonoidal :
    NatTrans.IsMonoidal (Functor.fullyFaithfulCancelRight K e).hom where
  unit := by
    apply K.map_injective
    apply (cancel_epi (Functor.LaxMonoidal.ε K)).mp
    have h := NatTrans.IsMonoidal.unit (τ := e.hom)
    simp only [Functor.LaxMonoidal.comp_ε] at h
    simpa only [Functor.map_comp, Category.assoc,
      Functor.fullyFaithfulCancelRight_hom_app, K.map_preimage] using h
  tensor X Y := by
    apply K.map_injective
    apply (cancel_epi (Functor.LaxMonoidal.μ K (F.obj X) (F.obj Y))).mp
    have h := NatTrans.IsMonoidal.tensor (τ := e.hom) X Y
    simp only [Functor.LaxMonoidal.comp_μ] at h
    rw [Functor.map_comp, Functor.map_comp]
    rw [← Functor.LaxMonoidal.μ_natural_assoc]
    simpa only [Category.assoc, Functor.fullyFaithfulCancelRight_hom_app,
      K.map_preimage] using h

end Paper18.Category.FixedBoundary

namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  {E : Type u''} [Category.{v''} E] [MonoidalCategory E]
  {F G : C ⥤ D} [F.Monoidal] [G.Monoidal]
  (K : D ⥤ E) [K.Monoidal] [K.Faithful]
  (e : F ⋙ K ≅ G ⋙ K) [NatTrans.IsMonoidal e.hom]

/-- A faithful strong tensor functor reflects monoidality of an actual
natural transformation whose mapped components form a monoidal comparison. -/
theorem natTransMonoidal_of_map (τ : F ⟶ G)
    (hτ : ∀ X, K.map (τ.app X) = e.hom.app X) : NatTrans.IsMonoidal τ where
  unit := by
    apply K.map_injective
    apply (cancel_epi (Functor.LaxMonoidal.ε K)).mp
    have h := NatTrans.IsMonoidal.unit (τ := e.hom)
    simp only [Functor.LaxMonoidal.comp_ε] at h
    simpa only [Functor.map_comp, Category.assoc, hτ] using h
  tensor X Y := by
    apply K.map_injective
    apply (cancel_epi (Functor.LaxMonoidal.μ K (F.obj X) (F.obj Y))).mp
    have h := NatTrans.IsMonoidal.tensor (τ := e.hom) X Y
    simp only [Functor.LaxMonoidal.comp_μ] at h
    rw [Functor.map_comp, Functor.map_comp, ← Functor.LaxMonoidal.μ_natural_assoc]
    simpa only [Category.assoc, hτ] using h

end Paper18.Category.FixedBoundary
