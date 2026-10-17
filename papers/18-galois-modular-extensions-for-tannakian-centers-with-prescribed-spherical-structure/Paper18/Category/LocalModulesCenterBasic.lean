import Paper18.Category.RelativeTensorCentralFreeMonoidal
import Paper18.Category.LocalModulesCoherence
import Paper18.Category.SeparableModulesSemisimple

/-! # Actual central half-braidings of local separable modules

The positive crossing with a local module is invertible on free modules.
Separability supplies actual retracts of free modules and hence its inverse
on every module. This constructs the central lift without a centrality field.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.BraidedCategory
open scoped MonObj
universe v u
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [HasCoequalizers C] {A : C} [MonObj A] [IsCommMonObj A]
open RelativeTensor

/-- On an actual free module the positive local crossing is the actual
central free half-braiding. -/
theorem localBraidingHom_free (X : C) (M : Mod_ C A) (hM : IsLocalModule M) :
    localBraidingHom (InternalModule.free A X) M hM = (freeCentralIso X M).hom := by
  apply freeCentral_hom_ext
  simp only [freeTensorGenerator, Category.assoc]
  rw [π_localBraidingHom, freeUnit_π_freeCentralIso]
  rw [braiding_naturality_left_assoc]

/-- The positive crossing against a local module is an actual isomorphism
whenever its first input is an actual retract of a free module. -/
def localBraidingIsoOfFreeRetract (M N : Mod_ C A) (hM : IsLocalModule M)
    {X : C} (R : Retract N (InternalModule.free A X)) : N ⊗ M ≅ M ⊗ N where
  hom := localBraidingHom N M hM
  inv := M ◁ R.i ≫ (freeCentralIso X M).inv ≫ R.r ▷ M
  hom_inv_id := by
    rw [← localBraiding_naturality_left_assoc R.i M hM]
    rw [localBraidingHom_free X M hM, Iso.hom_inv_id_assoc]
    rw [← comp_whiskerRight, R.retract, id_whiskerRight]
  inv_hom_id := by
    rw [Category.assoc, Category.assoc, localBraiding_naturality_left R.r M hM,
      localBraidingHom_free X M hM, Iso.inv_hom_id_assoc]
    rw [← whiskerLeft_comp, R.retract, whiskerLeft_id]

namespace SeparableAlgebra
variable (S : SeparableAlgebra A)

/-- Separability makes the actual crossing against a local module
invertible on every actual module. -/
def localCrossingIso (M N : Mod_ C A) (hM : IsLocalModule M) : N ⊗ M ≅ M ⊗ N :=
  localBraidingIsoOfFreeRetract M N hM (S.freeRetract N)

/-- The central half-braiding of a local module uses the inverse of the
positive crossing against that module. -/
def localHalfBraiding (M : Mod_ C A) (hM : IsLocalModule M) : HalfBraiding M where
  β N := (S.localCrossingIso M N hM).symm
  naturality {N P} f := by
    apply (cancel_epi (S.localCrossingIso M N hM).hom).mp
    apply (cancel_mono (S.localCrossingIso M P hM).hom).mp
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
    exact (localBraiding_naturality_left f M hM).symm
  monoidal N P := by
    apply (cancel_epi (S.localCrossingIso M (N ⊗ P) hM).hom).mp
    simp only [Iso.symm_hom, Iso.hom_inv_id]
    have hh : (α_ N P M).inv ≫ (S.localCrossingIso M (N ⊗ P) hM).hom ≫
        (α_ M N P).inv =
      N ◁ (S.localCrossingIso M P hM).hom ≫ (α_ N M P).inv ≫
        (S.localCrossingIso M N hM).hom ▷ P :=
      localBraiding_hexagon_reverse N P M hM
    symm
    calc
      _ = (α_ N P M).hom ≫ ((α_ N P M).inv ≫
          (S.localCrossingIso M (N ⊗ P) hM).hom ≫ (α_ M N P).inv) ≫
          (S.localCrossingIso M N hM).inv ▷ P ≫ (α_ N M P).hom ≫
          N ◁ (S.localCrossingIso M P hM).inv ≫ (α_ N P M).inv := by simp
      _ = _ := by rw [hh]; simp [← comp_whiskerRight_assoc, ← whiskerLeft_comp_assoc]

end SeparableAlgebra
end Paper18.Category
