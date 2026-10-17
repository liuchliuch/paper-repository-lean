import Paper18.Category.TannakianDeequivariantFusion
import Paper18.Category.TannakianDescent
import Paper18.Category.NondegenerateBasic
import Paper18.Category.LocalModulesNondegenerateBasic

/-! # Actual free-module transport and unit-sum retracts -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category
namespace InternalModule
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] {A : C} [MonObj A]

/-- The strong tensorator intertwines the actual free-module actions. -/
@[reassoc]
theorem freeAction_tensorator (X : C) :
    γ[F.obj A,(free (F.obj A) (F.obj X)).X] ≫ Functor.LaxMonoidal.μ F A X =
      (F.obj A ◁ Functor.LaxMonoidal.μ F A X) ≫ Functor.LaxMonoidal.μ F A (A ⊗ X) ≫
        F.map γ[A,(free A X).X] := by
  simp only [free_smul, F.map_comp, Functor.Monoidal.map_associator_inv,
    Functor.Monoidal.map_whiskerRight, Category.assoc,
    Functor.Monoidal.μ_δ_assoc]
  change (α_ (F.obj A) (F.obj A) (F.obj X)).inv ≫
      (Functor.LaxMonoidal.μ F A A ≫ F.map μ[A]) ▷ F.obj X ≫ Functor.LaxMonoidal.μ F A X = _
  simp only [comp_whiskerRight, Category.assoc, Functor.Monoidal.whiskerLeft_μ_δ_assoc]

/-- The inverse tensorator intertwines the same free-module actions. -/
@[reassoc]
theorem freeAction_tensorator_inv (X : C) :
    Functor.LaxMonoidal.μ F A (A ⊗ X) ≫ F.map γ[A,(free A X).X] ≫ δ F A X =
      (F.obj A ◁ δ F A X) ≫ γ[F.obj A,(free (F.obj A) (F.obj X)).X] := by
  apply (cancel_epi (F.obj A ◁ Functor.LaxMonoidal.μ F A X)).mp
  rw [← freeAction_tensorator_assoc]
  simp only [Functor.Monoidal.μ_δ, Functor.Monoidal.whiskerLeft_μ_δ_assoc]
  erw [Category.comp_id]

/-- Transport an actual free-module morphism through a strong tensor functor. -/
def mapFreeHom {X Y : C} (f : free A X ⟶ free A Y) :
    free (F.obj A) (F.obj X) ⟶ free (F.obj A) (F.obj Y) :=
  Mod_.Hom.mk' (Functor.LaxMonoidal.μ F A X ≫ F.map f.hom ≫ δ F A Y) (by
    rw [← Category.assoc, freeAction_tensorator]
    simp only [Category.assoc]
    rw [← F.map_comp_assoc, f.isMod_Hom.smul_hom, F.map_comp]
    change (F.obj A ◁ Functor.LaxMonoidal.μ F A X) ≫
      Functor.LaxMonoidal.μ F A (A ⊗ X) ≫
      (F.map (A ◁ f.hom) ≫ F.map γ[A,(free A Y).X]) ≫ δ F A Y =
      (F.obj A ◁ (Functor.LaxMonoidal.μ F A X ≫ F.map f.hom ≫ δ F A Y)) ≫
        γ[F.obj A,(free (F.obj A) (F.obj Y)).X]
    rw [Functor.Monoidal.map_whiskerLeft]
    simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
    change (F.obj A ◁ Functor.LaxMonoidal.μ F A X) ≫ (F.obj A ◁ F.map f.hom) ≫
      Functor.LaxMonoidal.μ F A (A ⊗ Y) ≫ F.map γ[A,(free A Y).X] ≫ δ F A Y = _
    rw [freeAction_tensorator_inv]
    simp only [whiskerLeft_comp, Category.assoc])

/-- Strong monoidal transport of an actual isomorphism of free modules. -/
def mapFreeIso {X Y : C} (e : free A X ≅ free A Y) :
    free (F.obj A) (F.obj X) ≅ free (F.obj A) (F.obj Y) := by
  let f := mapFreeHom F e.hom
  let e' := Functor.Monoidal.μIso F A X ≪≫
    F.mapIso ((Mod_.forget (D := C) A).mapIso e) ≪≫
    (Functor.Monoidal.μIso F A Y).symm
  letI : IsIso f.hom := e'.isIso_hom
  letI := internalModule_isIso_of_underlying f
  exact asIso f

end InternalModule

section UnitSumRetract
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasKernels C] [HasFiniteBiproducts C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalPreadditive C] [Simple (𝟙_ C)]

omit [BraidedCategory C] [MonoidalPreadditive C] in
/-- A simple actual retract of a finite sum of units is isomorphic to the unit. -/
theorem iso_unit_of_simple_retract_unitSum {X Y : C} [Simple X]
    (r : Retract X Y) (hY : IsUnitSum Y) : Nonempty (X ≅ 𝟙_ C) := by
  obtain ⟨n, ⟨e⟩⟩ := hY
  have hn : ∃ j : Fin n, r.i ≫ e.hom ≫ biproduct.π _ j ≠ 0 := by
    by_contra h
    push_neg at h
    have hi : r.i ≫ e.hom = 0 := by
      apply biproduct.hom_ext
      intro j
      simpa only [zero_comp, Category.assoc] using h j
    have hi' : r.i = 0 := by
      apply (cancel_mono e.hom).mp
      simpa only [zero_comp] using hi
    apply CategoryTheory.id_nonzero X
    rw [← r.retract, hi', zero_comp]
  obtain ⟨j, hj⟩ := hn
  letI := CategoryTheory.isIso_of_hom_simple hj
  exact ⟨asIso (r.i ≫ e.hom ≫ biproduct.π _ j)⟩

end UnitSumRetract
end Paper18.Category
