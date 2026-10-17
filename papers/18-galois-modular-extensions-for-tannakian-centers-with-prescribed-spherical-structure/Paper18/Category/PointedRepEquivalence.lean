import Paper18.Category.PointedRepEquivalenceEssential
import Paper18.Category.PointedRepEquivalenceMonoidal
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # The actual Tannakian identification of the Appendix B transparent center

The forward functor takes the total finite direct sum of homogeneous fibers,
with the nonidentity element of C₂ acting by the first-coordinate parity.
Its inverse is supplied by the proved positive/negative eigenspace realization.
The tensor comparison is the actual distributivity isomorphism of finite
biproducts, and preserves the specified Appendix B braiding.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal
namespace Paper18.Category.AppendixBPointed
open RepresentationZ2

/-- The transparent center is actually equivalent to complex representations
of C₂, through its homogeneous total-vector representation. -/
def repZ2Equivalence : BCenter ≌ FDRep ℂ H := centerRepFunctor.asEquivalence

@[simp] lemma repZ2Equivalence_functor : repZ2Equivalence.functor = centerRepFunctor := rfl

instance repZ2Equivalence_functor_additive : repZ2Equivalence.functor.Additive :=
  centerRepFunctor_additive

instance repZ2Equivalence_functor_linear : repZ2Equivalence.functor.Linear ℂ :=
  centerRepFunctor_linear

instance repZ2Equivalence_functor_braided : repZ2Equivalence.functor.Braided :=
  centerRepFunctor_braided

/-- The inverse tensor structure is obtained from the actual equivalence
adjunction and the already proved forward tensor comparison. -/
instance repZ2Equivalence_inverse_monoidal : repZ2Equivalence.inverse.Monoidal :=
  repZ2Equivalence.inverseMonoidal

instance repZ2Equivalence_isMonoidal : repZ2Equivalence.IsMonoidal := inferInstance

instance repZ2Equivalence_unit_monoidal :
    NatTrans.IsMonoidal repZ2Equivalence.unitIso.hom :=
  inferInstanceAs (NatTrans.IsMonoidal repZ2Equivalence.unit)

instance repZ2Equivalence_counit_monoidal :
    NatTrans.IsMonoidal repZ2Equivalence.counitIso.hom :=
  inferInstanceAs (NatTrans.IsMonoidal repZ2Equivalence.counit)

instance repZ2Equivalence_inverse_linear : repZ2Equivalence.inverse.Linear ℂ :=
  Equivalence.inverseLinear ℂ repZ2Equivalence

instance repZ2Equivalence_inverse_additive : repZ2Equivalence.inverse.Additive :=
  Equivalence.inverse_additive repZ2Equivalence

/-- Both directions preserve the specified braiding, with the equivalence
unit and counit compatible with their actual tensor structures. -/
instance repZ2Equivalence_inverse_braided : repZ2Equivalence.inverse.Braided where
  toMonoidal := repZ2Equivalence_inverse_monoidal
  braided X Y := by
    letI : NatTrans.IsMonoidal repZ2Equivalence.counitIso.symm.hom :=
      inferInstanceAs (NatTrans.IsMonoidal repZ2Equivalence.counitIso.inv)
    letI : (repZ2Equivalence.inverse ⋙ repZ2Equivalence.functor).LaxBraided :=
      Functor.LaxBraided.ofNatIso repZ2Equivalence.counitIso.symm
    have h := Functor.LaxBraided.braided
      (F := repZ2Equivalence.inverse ⋙ repZ2Equivalence.functor) X Y
    apply repZ2Equivalence.functor.map_injective
    apply (cancel_epi (μ repZ2Equivalence.functor
      (repZ2Equivalence.inverse.obj X) (repZ2Equivalence.inverse.obj Y))).1
    simp only [Functor.map_comp]
    rw [Functor.LaxBraided.braided_assoc]
    simpa only [Functor.comp_map, Functor.comp_obj, Functor.LaxMonoidal.comp_μ,
      Category.assoc] using h

end Paper18.Category.AppendixBPointed
