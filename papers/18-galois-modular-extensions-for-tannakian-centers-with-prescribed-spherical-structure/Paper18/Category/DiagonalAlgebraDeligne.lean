import Paper18.Category.DiagonalAlgebraCenter
import Paper18.Category.Factorization
import Paper18.Category.FactorizationDeligneBraided
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # The canonical algebra in the actual reverse-second Deligne product

The algebra is transported through the actual factorization equivalence.
The reverse-second braiding is always explicit: no global product braiding
is changed. Commutativity and connectedness are derived from the actual
center algebra and the actual fully faithful linear tensor equivalence.
-/
noncomputable section
set_option maxHeartbeats 1000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Limits
open scoped MonObj
universe v u w v' u'
namespace Paper18.Category.DiagonalAlgebra

section Equivalence
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  (E : C ≌ D) [E.functor.Braided]

/-- The actual inverse tensor equivalence preserves the specified braidings. -/
def inverseBraided :
    letI : E.inverse.Monoidal := E.inverseMonoidal
    E.inverse.Braided := by
  letI : E.inverse.Monoidal := E.inverseMonoidal
  refine { braided := ?_ }
  intro X Y
  letI : E.IsMonoidal := inferInstance
  letI : NatTrans.IsMonoidal E.counitIso.symm.hom :=
    inferInstanceAs (NatTrans.IsMonoidal E.counitIso.inv)
  letI : (E.inverse ⋙ E.functor).LaxBraided :=
    Functor.LaxBraided.ofNatIso E.counitIso.symm
  have h := Functor.LaxBraided.braided (F := E.inverse ⋙ E.functor) X Y
  apply E.functor.map_injective
  apply (cancel_epi (Functor.LaxMonoidal.μ E.functor (E.inverse.obj X) (E.inverse.obj Y))).1
  simp only [Functor.map_comp]
  rw [Functor.LaxBraided.braided_assoc]
  simpa only [Functor.comp_map, Functor.comp_obj, Functor.LaxMonoidal.comp_μ,
    Category.assoc] using h
end Equivalence

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)
  (hC : IsNondegenerate (C := C))

instance factorization_functor_monoidal :
    (Drinfeld.factorizationEquivalence S J hC).functor.Monoidal :=
  inferInstanceAs ((Drinfeld.deligneFactorization C).Monoidal)

instance factorization_functor_additive :
    (Drinfeld.factorizationEquivalence S J hC).functor.Additive :=
  inferInstanceAs ((Drinfeld.deligneFactorization C).Additive)

instance factorization_functor_linear :
    (Drinfeld.factorizationEquivalence S J hC).functor.Linear ℂ :=
  inferInstanceAs ((Drinfeld.deligneFactorization C).Linear ℂ)

instance factorization_inverse_monoidal :
    (Drinfeld.factorizationEquivalence S J hC).inverse.Monoidal :=
  (Drinfeld.factorizationEquivalence S J hC).inverseMonoidal

instance factorization_inverse_additive :
    (Drinfeld.factorizationEquivalence S J hC).inverse.Additive :=
  Equivalence.inverse_additive (Drinfeld.factorizationEquivalence S J hC)

instance factorization_inverse_linear :
    (Drinfeld.factorizationEquivalence S J hC).inverse.Linear ℂ :=
  Equivalence.inverseLinear ℂ (Drinfeld.factorizationEquivalence S J hC)

/-- The actual diagonal algebra object, obtained from the actual right-adjoint
unit algebra through the actual factorization equivalence. -/
def diagonalAlgebra : DeligneProduct C C :=
  (Drinfeld.factorizationEquivalence S J hC).inverse.obj (centerAlgebra S J)

instance diagonalAlgebraMonObj : MonObj (diagonalAlgebra S J hC) :=
  Functor.monObjObj (F := (Drinfeld.factorizationEquivalence S J hC).inverse)
    (centerAlgebra S J)

/-- Commutativity holds for the actual reverse-second braiding used by
factorization. The product's default braiding is not replaced globally. -/
def diagonalAlgebra_commutative :
    letI : BraidedCategory (DeligneProduct C C) := Drinfeld.deligneReverseSecondBraiding C
    IsCommMonObj (diagonalAlgebra S J hC) := by
  letI : BraidedCategory (DeligneProduct C C) := Drinfeld.deligneReverseSecondBraiding C
  let E := Drinfeld.factorizationEquivalence S J hC
  letI : E.functor.Braided := Drinfeld.deligneFactorizationBraided C
  letI : E.inverse.Braided := inverseBraided E
  exact Functor.isCommMonObj_obj (F := E.inverse)

/-- The actual diagonal algebra is connected. -/
theorem diagonalAlgebra_connected :
    Module.finrank ℂ (𝟙_ (DeligneProduct C C) ⟶ diagonalAlgebra S J hC) = 1 := by
  let E := Drinfeld.factorizationEquivalence S J hC
  let e := fullyFaithfulHomLinearEquiv E.functor
    (𝟙_ (DeligneProduct C C)) (diagonalAlgebra S J hC)
  calc
    _ = Module.finrank ℂ (E.functor.obj (𝟙_ (DeligneProduct C C)) ⟶
        E.functor.obj (diagonalAlgebra S J hC)) := e.finrank_eq
    _ = Module.finrank ℂ (𝟙_ (Center C) ⟶ centerAlgebra S J) :=
      finrank_hom_iso (Functor.Monoidal.εIso E.functor).symm
        (E.counitIso.app (centerAlgebra S J))
    _ = 1 := centerAlgebra_connected S J

end Paper18.Category.DiagonalAlgebra
