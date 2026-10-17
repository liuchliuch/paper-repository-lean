import Paper18.Category.RadfordBraidedCoherence
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Canonical double dualization as an actual braided tensor equivalence

The ordinary Drinfeld natural isomorphism proves ordinary equivalence
only. The tensor structure remains the canonical rigidity-derived one.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.GraphPicard
variable (D : Type u) [Category.{v} D] [MonoidalCategory D]
  [RightRigidCategory D] [BraidedCategory D]

instance doubleDualIsEquivalence : (doubleDualFunctor D).IsEquivalence :=
  Functor.isEquivalence_of_iso (drinfeldNatIso (C := D))

def doubleDualEquivalence : D ≌ D := (doubleDualFunctor D).asEquivalence

instance doubleDualEquivalence_functorMonoidal : (doubleDualEquivalence D).functor.Monoidal :=
  inferInstanceAs (doubleDualFunctor D).Monoidal

instance doubleDualEquivalence_functorBraided : (doubleDualEquivalence D).functor.Braided :=
  inferInstanceAs (doubleDualFunctor D).Braided

instance doubleDualEquivalence_inverseMonoidal : (doubleDualEquivalence D).inverse.Monoidal :=
  (doubleDualEquivalence D).inverseMonoidal

instance doubleDualEquivalence_isMonoidal : (doubleDualEquivalence D).IsMonoidal := by
  infer_instance

instance doubleDualEquivalence_inverseBraided : (doubleDualEquivalence D).inverse.Braided where
  braided X Y := by
    let e := doubleDualEquivalence D
    letI : NatTrans.IsMonoidal e.counitIso.symm.hom :=
      inferInstanceAs (NatTrans.IsMonoidal e.counitIso.inv)
    letI : (e.inverse ⋙ e.functor).LaxBraided := Functor.LaxBraided.ofNatIso e.counitIso.symm
    have h := Functor.LaxBraided.braided (F := e.inverse ⋙ e.functor) X Y
    apply e.functor.map_injective
    apply (cancel_epi (Functor.LaxMonoidal.μ e.functor (e.inverse.obj X) (e.inverse.obj Y))).mp
    simp only [Functor.map_comp]
    rw [Functor.LaxBraided.braided_assoc]
    simpa only [Functor.comp_map, Functor.comp_obj, Functor.LaxMonoidal.comp_μ,
      Category.assoc] using h

end Paper18.Category.GraphPicard
