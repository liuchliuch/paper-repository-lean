import Paper28.ConcreteHomologyClasses
import Paper28.CompactCurrentAlgebraInput
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Genuine positive-degree current homology and its mass infimum. The
short complex consists of the actual compact integral-current groups and
their actual boundary maps. No abstract volume surrogate is introduced.
-/
set_option autoImplicit false
noncomputable section
namespace Paper28
open CategoryTheory Set
variable {X : Type} {metricX : MetricSpace X}
  (I : CompactIntegralCurrentAlgebraInput.{0,0} X metricX)

def positiveCurrentShortComplex (k : ℕ) : ShortComplex AddCommGrpCat :=
  ShortComplex.mk (AddCommGrpCat.ofHom (I.boundary (k+1))) (AddCommGrpCat.ofHom (I.boundary k))
    (by ext C; exact I.boundary_squared_zero k C)

abbrev PositiveCurrentHomology (k : ℕ) := (positiveCurrentShortComplex I k).homology
abbrev PositiveCurrentCycles (k : ℕ) := (I.boundary k).ker

def positiveCurrentClass (k : ℕ) (C : PositiveCurrentCycles I k) : PositiveCurrentHomology I k :=
  concreteHomologyClass (positiveCurrentShortComplex I k) C.val C.property

theorem concreteHomologyClass_add {S : ShortComplex AddCommGrpCat} (x y : S.X₂)
    (hx : S.g x = 0) (hy : S.g y = 0) :
    concreteHomologyClass S (x+y) (by rw [map_add,hx,hy,add_zero]) =
      concreteHomologyClass S x hx+concreteHomologyClass S y hy := by
  unfold concreteHomologyClass
  have he : (⟨x+y,by change S.g (x+y) = 0; rw [map_add,hx,hy,add_zero]⟩ : S.g.hom.ker) = ⟨x,hx⟩+⟨y,hy⟩ := rfl
  rw [he,QuotientAddGroup.mk_add,map_add]

theorem concreteHomologyClass_neg {S : ShortComplex AddCommGrpCat} (x : S.X₂) (hx : S.g x = 0) :
    concreteHomologyClass S (-x) (by rw [map_neg,hx,neg_zero]) = -concreteHomologyClass S x hx := by
  unfold concreteHomologyClass
  have he : (⟨-x,by change S.g (-x) = 0; rw [map_neg,hx,neg_zero]⟩ : S.g.hom.ker) = -⟨x,hx⟩ := rfl
  rw [he,QuotientAddGroup.mk_neg,map_neg]

def positiveCurrentClassHom (k : ℕ) : PositiveCurrentCycles I k →+ PositiveCurrentHomology I k where
  toFun := positiveCurrentClass I k
  map_zero' := by
    unfold positiveCurrentClass concreteHomologyClass
    change (positiveCurrentShortComplex I k).abHomologyIso.inv (QuotientAddGroup.mk 0) = 0
    rw [QuotientAddGroup.mk_zero,map_zero]
  map_add' C D := concreteHomologyClass_add (S := positiveCurrentShortComplex I k) C.val D.val C.property D.property

theorem positiveCurrentClass_eq_iff_boundary (k : ℕ) (C D : PositiveCurrentCycles I k) :
    positiveCurrentClass I k C = positiveCurrentClass I k D ↔
      ∃ W : I.Current (k+2), C.val-D.val = I.boundary (k+1) W := by
  have he : positiveCurrentClass I k (C-D) = positiveCurrentClass I k C-positiveCurrentClass I k D := by
    change (positiveCurrentClassHom I k) (C-D) = (positiveCurrentClassHom I k) C-(positiveCurrentClassHom I k) D
    exact map_sub (positiveCurrentClassHom I k) C D
  rw [← sub_eq_zero,← he]
  exact (concreteHomologyClass_eq_zero_iff (positiveCurrentShortComplex I k) (C-D).val (C-D).property).trans
    ⟨fun ⟨W,hW⟩ => ⟨W,hW.symm⟩,fun ⟨W,hW⟩ => ⟨W,hW.symm⟩⟩

def currentClassMasses (k : ℕ) (h : PositiveCurrentHomology I k) : Set ℝ :=
  {m | ∃ C : PositiveCurrentCycles I k, positiveCurrentClass I k C = h ∧ I.mass C.val = m}

def sphericalClassVolume (k : ℕ) (h : PositiveCurrentHomology I k) : ℝ := sInf (currentClassMasses I k h)

theorem currentClassMasses_bddBelow (k : ℕ) (h : PositiveCurrentHomology I k) :
    BddBelow (currentClassMasses I k h) :=
  ⟨0,by rintro m ⟨C,_,rfl⟩; exact I.mass_nonneg C.val⟩

end Paper28
