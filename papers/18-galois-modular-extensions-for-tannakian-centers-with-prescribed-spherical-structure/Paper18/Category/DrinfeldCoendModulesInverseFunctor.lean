import Paper18.Category.DrinfeldCoendModulesInverseTensor

/-! # The actual inverse functor from coend modules to central objects -/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- Module intertwiners are actual morphisms for the recovered
half-braidings. -/
lemma moduleHalfBraiding_map {M N : Mod_ D (algebra S)} (f : M ⟶ N) (T : D) :
    f.hom ▷ T ≫ ((moduleHalfBraiding S N).β T).hom =
      ((moduleHalfBraiding S M).β T).hom ≫ T ◁ f.hom := by
  let eM := (moduleRightLaxHalfBraiding S M).crossingIso T
  let eN := (moduleRightLaxHalfBraiding S N).crossingIso T
  change f.hom ▷ T ≫ eN.inv = eM.inv ≫ T ◁ f.hom
  apply (cancel_epi eM.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  have hm : T ◁ f.hom ≫ eN.hom = eM.hom ≫ f.hom ▷ T := moduleInverseCrossing_map S f T
  rw [← reassoc_of% hm, Iso.hom_inv_id, comp_id]

/-- Every actual coend module gives an actual central object, and every
actual module morphism gives an actual central morphism. -/
def fromModules : Mod_ D (algebra S) ⥤ Center D where
  obj M := ⟨M.X,moduleHalfBraiding S M⟩
  map f := ⟨f.hom,moduleHalfBraiding_map S f⟩
  map_id _ := by apply Center.Hom.ext; rfl
  map_comp _ _ := by apply Center.Hom.ext; rfl

@[simp] lemma fromModules_obj_fst (M : Mod_ D (algebra S)) :
    ((fromModules S).obj M).1 = M.X := rfl

@[simp] lemma fromModules_map_f {M N : Mod_ D (algebra S)} (f : M ⟶ N) :
    ((fromModules S).map f).f = f.hom := rfl

/-- The constructed central object's holonomy recovers the original
module's actual transposed annular operator. -/
lemma fromModules_holonomy (M : Mod_ D (algebra S)) (T : D) :
    (holonomy ((fromModules S).obj M) T).hom = moduleHolonomy S M T := by
  change ((moduleHalfBraiding S M).β T).inv ≫ (β_ T M.X).inv = _
  rw [moduleHalfBraiding_inv, moduleInverseCrossing, assoc, Iso.hom_inv_id, comp_id]

/-- Descending the recovered central structure back to the actual coend
returns exactly the original actual module action. -/
lemma fromModules_action (M : Mod_ D (algebra S)) :
    action S ((fromModules S).obj M) = γ[algebra S,M.X] := by
  apply Eq.symm
  apply action_eq_of_holonomy S M (moduleHalfBraiding S M)
  intro T
  exact (fromModules_holonomy S M T).symm

/-- Actual central intertwiners preserve the original module actions. -/
instance fromModules_full : (fromModules S).Full where
  map_surjective f := by
    refine ⟨Mod_.Hom.mk' f.f ?_, ?_⟩
    · simpa only [fromModules_action] using action_naturality S f
    · apply Center.Hom.ext
      rfl

instance fromModules_faithful : (fromModules S).Faithful where
  map_injective h := by
    apply Mod_.Hom.ext
    exact congrArg Center.Hom.f h

end Paper18.Category.DrinfeldCoendModules
