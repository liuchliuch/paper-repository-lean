import Paper18.Category.SphericalizationMonoidal
import Paper18.Category.EquivariantMonoidal
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# The canonical order-two action underlying braided sphericalization

The nontrivial element acts by canonical double dualization. Its multiplication
comparison is the inverse of the canonical monoidal four-dual map, and its
associativity is derived from double-dual compatibility of that map.
-/
noncomputable section
universe v u
namespace Paper18.Category
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
attribute [local instance 2000] RightRigidCategory.rightDual

abbrev SphericalizationGroup := Multiplicative (ZMod 2)

@[simp] lemma sphericalizationGroup_generator_mul :
    Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2) = 1 := by decide

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]

/-- The underlying two translating functors. -/
def sphericalizationRho (g : SphericalizationGroup) : C ⥤ C :=
  if g = 1 then 𝟭 C else doubleDualFunctor C

lemma sphericalizationGroup_mul (g h : SphericalizationGroup) (hg : g ≠ 1) (hh : h ≠ 1) :
    g * h = 1 := by
  fin_cases g <;> fin_cases h <;> simp_all [SphericalizationGroup]

/-- The actual order-two action multiplication comparison. -/
def sphericalizationMulIso (g h : SphericalizationGroup) :
    sphericalizationRho C h ⋙ sphericalizationRho C g ≅ sphericalizationRho C (g * h) := by
  by_cases hg : g = 1
  · subst g
    simpa only [sphericalizationRho, if_pos rfl, one_mul] using
      (Functor.rightUnitor (sphericalizationRho C h))
  · by_cases hh : h = 1
    · subst h
      simpa only [sphericalizationRho, if_pos rfl, mul_one, if_neg hg] using
        (Functor.leftUnitor (doubleDualFunctor C))
    · simpa only [sphericalizationRho, if_neg hg, if_neg hh,
        sphericalizationGroup_mul g h hg hh, if_pos rfl] using
        (braidedFourDualNatIso (C := C)).symm

lemma braidedFourDualIso_doubleDual_inv (X : C) :
    (braidedFourDualIso ((doubleDualFunctor C).obj X)).inv =
      (doubleDualFunctor C).map (braidedFourDualIso X).inv := by
  have hi : braidedFourDualIso ((doubleDualFunctor C).obj X) =
      (doubleDualFunctor C).mapIso (braidedFourDualIso X) :=
    Iso.ext (braidedFourDualIso_doubleDual X)
  exact congrArg Iso.inv hi

@[simp] lemma braidedFourDualNatIso_inv_app (X : C) :
    (braidedFourDualNatIso (C := C)).inv.app X = (braidedFourDualIso X).inv := rfl

/-- The actual canonical weak group action, obtained entirely from rigidity
and the braiding. -/
def sphericalizationAction : WeakAction SphericalizationGroup C where
  ρ := sphericalizationRho C
  unitIso := eqToIso (by simp [sphericalizationRho])
  mulIso := sphericalizationMulIso C
  assoc g h k X := by
    fin_cases g <;> fin_cases h <;> fin_cases k <;>
      simp [sphericalizationRho, sphericalizationMulIso, SphericalizationGroup,
        braidedFourDualIso_doubleDual_inv]
  one_mul g X := by
    fin_cases g <;> simp [sphericalizationRho, sphericalizationMulIso, SphericalizationGroup]
  mul_one g X := by
    fin_cases g <;> simp [sphericalizationRho, sphericalizationMulIso, SphericalizationGroup]

instance sphericalizationRho_monoidal (g : SphericalizationGroup) :
    (sphericalizationRho C g).Monoidal := by
  dsimp only [sphericalizationRho]
  split_ifs <;> infer_instance

instance sphericalizationAction_rho_monoidal (g : SphericalizationGroup) :
    ((sphericalizationAction C).ρ g).Monoidal := sphericalizationRho_monoidal C g

instance sphericalizationAction_isMonoidal : (sphericalizationAction C).IsMonoidal where
  unit_monoidal := by
    constructor
    · simp [sphericalizationAction, sphericalizationRho, sphericalizationAction_rho_monoidal,
        sphericalizationRho_monoidal]
    · intro X Y
      simp [sphericalizationAction, sphericalizationRho, sphericalizationAction_rho_monoidal,
        sphericalizationRho_monoidal]
  mul_monoidal g h := by
    fin_cases g <;> fin_cases h <;>
      simp [sphericalizationAction, sphericalizationMulIso, sphericalizationRho,
        SphericalizationGroup]
    all_goals infer_instance

section Linear
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

instance canonicalDoubleDual_additive : (doubleDualFunctor C).Additive where
  map_add := by
    intros
    simp [doubleDualFunctor, dualMap, rightAdjointMate, Preadditive.comp_add, Preadditive.add_comp]

instance canonicalDoubleDual_linear : (doubleDualFunctor C).Linear ℂ where
  map_smul f c := by simp [doubleDualFunctor, dualMap, rightAdjointMate]

instance sphericalizationAction_rho_additive (g : SphericalizationGroup) :
    ((sphericalizationAction C).ρ g).Additive := by
  dsimp only [sphericalizationAction, sphericalizationRho]
  split_ifs <;> infer_instance

instance sphericalizationAction_rho_linear (g : SphericalizationGroup) :
    ((sphericalizationAction C).ρ g).Linear ℂ := by
  dsimp only [sphericalizationAction, sphericalizationRho]
  split_ifs <;> infer_instance

end Linear

end Paper18.Category
