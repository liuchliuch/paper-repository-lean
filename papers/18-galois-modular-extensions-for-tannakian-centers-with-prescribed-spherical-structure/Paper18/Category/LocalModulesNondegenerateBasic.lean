import Paper18.Category.LocalModulesFree
import Paper18.Category.RelativeTensorCentralFree

/-! # Detecting actual centralization against free local modules -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.BraidedCategory
open scoped MonObj
universe v u
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [HasCoequalizers C] {A : C} [MonObj A] [IsCommMonObj A]
open RelativeTensor

@[reassoc]
private theorem free_doubleBraiding_generator (M : Mod_ C A) (hM : IsLocalModule M)
    (X : C) (hX : IsLocalModule (InternalModule.free A X)) :
    freeTensorGenerator X M ≫ (localBraidingHom (InternalModule.free A X) M hM).hom ≫
      (localBraidingHom M (InternalModule.free A X) hX).hom =
      (doubleBraiding X M.X).hom ≫ freeTensorGenerator X M := by
  unfold freeTensorGenerator
  rw [assoc, π_localBraidingHom_assoc, braiding_naturality_left_assoc,
    π_localBraidingHom, braiding_naturality_right_assoc]
  simp only [doubleBraiding, Iso.trans_hom, assoc]

private theorem localBraiding_free_centralizes_iff (M : Mod_ C A) (hM : IsLocalModule M)
    (X : C) (hX : IsLocalModule (InternalModule.free A X)) :
    (localBraidingHom (InternalModule.free A X) M hM ≫
      localBraidingHom M (InternalModule.free A X) hX = 𝟙 _) ↔ Centralizes X M.X := by
  constructor
  · intro h
    apply (cancel_mono (freeTensorGenerator X M)).mp
    change (doubleBraiding X M.X).hom ≫ freeTensorGenerator X M =
      𝟙 _ ≫ freeTensorGenerator X M
    rw [← free_doubleBraiding_generator M hM X hX]
    have hh := congrArg Mod_.Hom.hom h
    simp only [Mod_.comp_hom', Mod_.id_hom'] at hh
    rw [hh, comp_id, id_comp]
  · intro h
    apply Mod_.Hom.ext
    apply (cancel_epi (freeTensorGenerator X M)).mp
    change freeTensorGenerator X M ≫
        ((localBraidingHom (InternalModule.free A X) M hM).hom ≫
          (localBraidingHom M (InternalModule.free A X) hX).hom) =
      freeTensorGenerator X M ≫ 𝟙 _
    rw [free_doubleBraiding_generator M hM X hX, h, id_comp, comp_id]

/-- Centralization against the actual free local module is precisely
centralization of the underlying ambient object against its generator. -/
theorem centralizes_localFree_iff (M : LocalModules A)
    (X : CentralizerCategory ({A} : Set C)) :
    Centralizes M ((localFreeFunctor (A := A)).obj X) ↔ Centralizes M.obj.X X.obj := by
  have hX := ((localFreeFunctor (A := A)).obj X).property
  constructor
  · intro h
    have hh := (localBraiding_free_centralizes_iff M.obj M.property X.obj hX).mp h.symm
    exact hh.symm
  · intro h
    have hh := (localBraiding_free_centralizes_iff M.obj M.property X.obj hX).mpr h.symm
    have h' : Centralizes ((localFreeFunctor (A := A)).obj X) M := hh
    exact h'.symm

/-- Transparent algebra condensation detects ambient centralization
against every actual free generator. -/
theorem centralizes_free_iff_of_transparent (hA : A ∈ mugerCenter (C := C))
    (M : Mod_ C A) (X : C) :
    letI := moduleBraidedOfTransparent hA
    Centralizes M (InternalModule.free A X) ↔ Centralizes M.X X := by
  letI := moduleBraidedOfTransparent hA
  constructor
  · intro h
    exact ((localBraiding_free_centralizes_iff M (localModule_of_transparent hA M) X
      (localModule_of_transparent hA (InternalModule.free A X))).mp h.symm).symm
  · intro h
    have hh := (localBraiding_free_centralizes_iff M (localModule_of_transparent hA M) X
      (localModule_of_transparent hA (InternalModule.free A X))).mpr h.symm
    have h' : Centralizes (InternalModule.free A X) M := hh
    exact h'.symm

/-- An actual transparent module over a transparent algebra has an actual
transparent underlying ambient object. -/
theorem underlying_transparent_of_module_transparent (hA : A ∈ mugerCenter (C := C))
    (M : Mod_ C A) :
    letI := moduleBraidedOfTransparent hA
    M ∈ mugerCenter (C := Mod_ C A) → M.X ∈ mugerCenter (C := C) := by
  letI := moduleBraidedOfTransparent hA
  intro h X _
  exact (centralizes_free_iff_of_transparent hA M X).mp
    (h (InternalModule.free A X) (Set.mem_univ _))

end Paper18.Category
