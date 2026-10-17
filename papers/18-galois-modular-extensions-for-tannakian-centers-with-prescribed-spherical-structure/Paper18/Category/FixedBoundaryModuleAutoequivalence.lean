import Paper18.Category.FixedBoundaryAlgebra
import Paper18.Category.FixedBoundaryModuleEquivalence
import Paper18.Category.FixedBoundaryRestriction

/-! # Actual de-equivariantized fixed-boundary autoequivalences -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N]
  [HasKernels N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  {i : A ⥤ N} [i.Monoidal] (P : BoundaryAutoequivalence i)

/-- The actual module functor determined by `(F,α)` is an autoequivalence
for every separable boundary algebra. Essential surjectivity was proved
from actual free-module retracts and source kernels. -/
def BoundaryAutoequivalence.moduleEquivalence (R : A) [MonObj R]
    (S : SeparableAlgebra (i.obj R)) : Mod_ N (i.obj R) ≌ Mod_ N (i.obj R) := by
  let e := P.boundaryAlgebraIso R
  letI : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  exact (InternalModule.moduleEquivalence P.functor S).trans
    (InternalModule.algebraRestrictionEquivalence e.symm)

@[simp] theorem BoundaryAutoequivalence.moduleEquivalence_functor
    (R : A) [MonObj R] (S : SeparableAlgebra (i.obj R)) :
    (P.moduleEquivalence R S).functor = P.moduleFunctor R := rfl

/-- Specialization to the actual regular algebra of a specified
Tannakian boundary center, with separability transported through `i`. -/
def BoundaryAutoequivalence.regularModuleEquivalence
    {G : Type} [Group G] [Fintype G] (T : TannakianCenter A G) :
    Mod_ N (i.obj T.regularAlgebra) ≌ Mod_ N (i.obj T.regularAlgebra) :=
  P.moduleEquivalence T.regularAlgebra (T.regularAlgebraSeparable.map i)

end Paper18.Category
