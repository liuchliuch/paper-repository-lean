import Paper18.Category.LocalModulesPivotalFrobenius
import Paper18.Category.PivotalFunctor
import Paper18.Category.FunctorImage

/-! # Actual tensor transport of perfect multiplication pairings -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category.ModuleBalancing.MultiplicationPairing
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  {A : C} [MonObj A] (P : MultiplicationPairing A)
  (F : C ⥤ D) [F.Monoidal]

/-- Strong tensor functors transport the actual cup, multiplication cap,
and both actual triangle identities. -/
def map : MultiplicationPairing (F.obj A) where
  counit := F.map P.counit ≫ Functor.OplaxMonoidal.η F
  pairing := by
    letI := P.pairing
    exact mapExactPairing F A A
  evaluation := by
    letI := P.pairing
    change Functor.LaxMonoidal.μ F A A ≫
      F.map (@ExactPairing.evaluation C _ _ A A P.pairing) ≫ Functor.OplaxMonoidal.η F =
      (Functor.LaxMonoidal.μ F A A ≫ F.map μ[A]) ≫ (F.map P.counit ≫ Functor.OplaxMonoidal.η F)
    rw [P.evaluation, F.map_comp]
    simp only [assoc]

/-- The actual counit remains normalized after actual tensor transport. -/
lemma map_one_counit (hP : η[A] ≫ P.counit = 𝟙 _) :
    η[F.obj A] ≫ (P.map F).counit = 𝟙 _ := by
  change (Functor.LaxMonoidal.ε F ≫ F.map η[A]) ≫
    (F.map P.counit ≫ Functor.OplaxMonoidal.η F) = _
  simp only [assoc]
  rw [← F.map_comp_assoc, hP, CategoryTheory.Functor.map_id, id_comp, Functor.Monoidal.ε_η]

end Paper18.Category.ModuleBalancing.MultiplicationPairing

namespace Paper18.Category.DiagonalAlgebra
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] [Linear ℂ C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [Preadditive D] [Linear ℂ D]
  (F : C ⥤ D) [F.Monoidal] [F.Additive] [F.Linear ℂ] [F.Full] [F.Faithful]

/-- Actual fully faithful linear tensor embeddings preserve connectedness. -/
lemma connected_map (A : C) (hA : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) :
    Module.finrank ℂ (𝟙_ D ⟶ F.obj A) = 1 := by
  calc
    _ = Module.finrank ℂ (F.obj (𝟙_ C) ⟶ F.obj A) :=
      finrank_hom_iso (Functor.Monoidal.εIso F) (Iso.refl _)
    _ = Module.finrank ℂ (𝟙_ C ⟶ A) :=
      (fullyFaithfulHomLinearEquiv F (𝟙_ C) A).finrank_eq.symm
    _ = 1 := hA

end Paper18.Category.DiagonalAlgebra
