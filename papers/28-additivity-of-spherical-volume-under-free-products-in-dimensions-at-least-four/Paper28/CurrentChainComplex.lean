import Paper28.CompactCurrentAlgebraInput
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! The native chain complex and native homology of the disclosed actual
compact integral-current groups. No independent homology surrogate is used. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open CategoryTheory
universe u v
variable {X : Type u} {metric : MetricSpace X}

def compactCurrentChainComplex (I : CompactIntegralCurrentAlgebraInput.{u,v} X metric) :
    ChainComplex AddCommGrpCat.{v} ℕ :=
  ChainComplex.of I.Current (fun k => AddCommGrpCat.ofHom (I.boundary k)) (by
    intro k
    ext C
    exact I.boundary_squared_zero k C)

@[simp] theorem compactCurrentChainComplex_d
    (I : CompactIntegralCurrentAlgebraInput.{u,v} X metric) (k : ℕ) :
    (compactCurrentChainComplex I).d (k+1) k = AddCommGrpCat.ofHom (I.boundary k) :=
  ChainComplex.of_d _ _ _ k

abbrev CompactCurrentHomology (I : CompactIntegralCurrentAlgebraInput.{u,v} X metric) (k : ℕ) :=
  (compactCurrentChainComplex I).homology k

end Paper28
