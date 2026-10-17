import Paper18.Category.RelativeTensorLeftFree
import Mathlib.CategoryTheory.Monoidal.Center

/-! # Actual central free modules

The half-braiding comparisons are constructed from the two actual
free-factor tensor isomorphisms and checked on actual free generators.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.BraidedCategory
open scoped MonObj
universe v u
namespace Paper18.Category.RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [HasCoequalizers C] {A : C} [MonObj A] [IsCommMonObj A]

/-- The actual generators of the relative tensor with a free left factor. -/
def freeTensorGenerator (X : C) (M : Mod_ C A) :
    X ⊗ M.X ⟶ (InternalModule.free A X ⊗ M).X :=
  (freeUnit X ▷ M.X) ≫ π (InternalModule.free A X) M

@[reassoc (attr := simp)]
theorem freeTensorGenerator_leftFreeHom (X : C) (M : Mod_ C A) :
    freeTensorGenerator X M ≫ (leftFreeHom X M).hom = (β_ X M.X).hom := by
  unfold freeTensorGenerator
  rw [Category.assoc, π_leftFreeHom, freeUnit_leftFreeLinearHom]

/-- The free generators form an actual underlying isomorphism. -/
instance freeTensorGenerator_isIso (X : C) (M : Mod_ C A) :
    IsIso (freeTensorGenerator X M) := by
  let z := (Mod_.forget (D := C) A).mapIso (leftFreeIso X M)
  have h : freeTensorGenerator X M = (β_ X M.X).hom ≫ z.inv := by
    apply (cancel_mono z.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact freeTensorGenerator_leftFreeHom X M
  rw [h]
  infer_instance

/-- Actual module maps from a free relative tensor are detected by its
actual ambient generators. -/
theorem freeCentral_hom_ext {X : C} {M N : Mod_ C A}
    {f g : InternalModule.free A X ⊗ M ⟶ N}
    (h : freeTensorGenerator X M ≫ f.hom = freeTensorGenerator X M ≫ g.hom) : f = g := by
  apply Mod_.Hom.ext
  exact (cancel_epi (freeTensorGenerator X M)).mp h

@[reassoc (attr := simp)]
theorem freeUnit_π_freeCentralIso (X : C) (M : Mod_ C A) :
    (freeUnit X ▷ M.X) ≫ π (InternalModule.free A X) M ≫ (freeCentralIso X M).hom.hom =
      (β_ X M.X).hom ≫ (M.X ◁ freeUnit X) ≫ π M (InternalModule.free A X) := by
  change (freeUnit X ▷ M.X) ≫ π (InternalModule.free A X) M ≫
      (leftFreeHom X M).hom ≫ (M.X ◁ freeUnit X) ≫ π M (InternalModule.free A X) = _
  rw [π_leftFreeHom_assoc, freeUnit_leftFreeLinearHom_assoc]

/-- The actual free commutation isomorphism is natural in every module. -/
@[reassoc]
theorem freeCentralIso_naturality (X : C) {M N : Mod_ C A} (f : M ⟶ N) :
    InternalModule.free A X ◁ f ≫ (freeCentralIso X N).hom =
      (freeCentralIso X M).hom ≫ f ▷ InternalModule.free A X := by
  apply freeCentral_hom_ext
  simp only [freeTensorGenerator, Mod_.comp_hom', Category.assoc]
  change (freeUnit X ▷ M.X) ≫ π (InternalModule.free A X) M ≫
      (InternalModule.free A X ◁ f).hom ≫ (freeCentralIso X N).hom.hom =
    (freeUnit X ▷ M.X) ≫ π (InternalModule.free A X) M ≫
      (freeCentralIso X M).hom.hom ≫ (f ▷ InternalModule.free A X).hom
  rw [π_whiskerLeft_assoc, ← whisker_exchange_assoc, freeUnit_π_freeCentralIso,
    freeUnit_π_freeCentralIso_assoc, π_whiskerRight]
  rw [braiding_naturality_right_assoc, whisker_exchange_assoc]

/-- The forward hexagon of the actual free half-braiding. -/
theorem freeCentralIso_hexagon_forward (X : C) (M N : Mod_ C A) :
    (α_ (InternalModule.free A X) M N).hom ≫ (freeCentralIso X (M ⊗ N)).hom ≫
        (α_ M N (InternalModule.free A X)).hom =
      (freeCentralIso X M).hom ▷ N ≫ (α_ M (InternalModule.free A X) N).hom ≫
        M ◁ (freeCentralIso X N).hom := by
  apply module_hom_ext
  letI : IsIso (freeTensorGenerator X M ▷ N.X) :=
    inferInstanceAs (IsIso ((tensorRight N.X).map (freeTensorGenerator X M)))
  apply (cancel_epi (freeTensorGenerator X M ▷ N.X)).mp
  unfold freeTensorGenerator
  simp only [comp_whiskerRight, Category.assoc]
  change ((freeUnit X ▷ M.X) ▷ N.X) ≫ (π (InternalModule.free A X) M ▷ N.X) ≫
      π (InternalModule.free A X ⊗ M) N ≫ (α_ (InternalModule.free A X) M N).hom.hom ≫
      (freeCentralIso X (M ⊗ N)).hom.hom ≫ (α_ M N (InternalModule.free A X)).hom.hom =
    ((freeUnit X ▷ M.X) ▷ N.X) ≫ (π (InternalModule.free A X) M ▷ N.X) ≫
      π (InternalModule.free A X ⊗ M) N ≫ ((freeCentralIso X M).hom ▷ N).hom ≫
      (α_ M (InternalModule.free A X) N).hom.hom ≫ (M ◁ (freeCentralIso X N).hom).hom
  rw [π_associator_assoc, associator_naturality_left_assoc, ← whisker_exchange_assoc]
  erw [freeUnit_π_freeCentralIso_assoc X (M ⊗ N)]
  erw [braiding_naturality_right_assoc, ← whisker_exchange_assoc,
    π_associator, associator_naturality_right_assoc]
  rw [π_whiskerRight_assoc, ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]
  rw [Category.assoc, freeUnit_π_freeCentralIso, comp_whiskerRight_assoc, comp_whiskerRight_assoc]
  rw [π_associator_assoc, associator_naturality_middle_assoc, π_whiskerLeft]
  rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc]
  rw [Category.assoc, freeUnit_π_freeCentralIso]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [hexagon_forward_assoc]

/-- The actual half-braiding on a free module. -/
def freeHalfBraiding (X : C) : HalfBraiding (InternalModule.free A X) where
  β := freeCentralIso X
  naturality := freeCentralIso_naturality X
  monoidal M N := by
    apply (cancel_epi (α_ (InternalModule.free A X) M N).hom).mp
    apply (cancel_mono (α_ M N (InternalModule.free A X)).hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using freeCentralIso_hexagon_forward X M N

/-- The actual free module regarded in the actual Drinfeld center. -/
def centralFreeObj (X : C) : Center (Mod_ C A) := ⟨InternalModule.free A X, freeHalfBraiding X⟩

/-- Ambient morphisms induce actual central free-module morphisms. -/
theorem freeCentralIso_map {X Y : C} (f : X ⟶ Y) (M : Mod_ C A) :
    InternalModule.freeMap f ▷ M ≫ (freeCentralIso Y M).hom =
      (freeCentralIso X M).hom ≫ M ◁ InternalModule.freeMap f := by
  apply freeCentral_hom_ext
  simp only [freeTensorGenerator, Mod_.comp_hom', Category.assoc]
  rw [π_whiskerRight_assoc, ← comp_whiskerRight_assoc, freeUnit_naturality,
    comp_whiskerRight_assoc, freeUnit_π_freeCentralIso,
    freeUnit_π_freeCentralIso_assoc, π_whiskerLeft, ← whiskerLeft_comp_assoc,
    freeUnit_naturality, whiskerLeft_comp_assoc, braiding_naturality_left_assoc]

/-- The actual free-module functor lifts to the actual Drinfeld center. -/
def centralFreeFunctor : C ⥤ Center (Mod_ C A) where
  obj := centralFreeObj
  map f := { f := InternalModule.freeMap f, comm := freeCentralIso_map f }
  map_id X := by
    apply Center.ext
    exact (InternalModule.freeFunctor (A := A)).map_id X
  map_comp f g := by
    apply Center.ext
    exact (InternalModule.freeFunctor (A := A)).map_comp f g

end Paper18.Category.RelativeTensor
