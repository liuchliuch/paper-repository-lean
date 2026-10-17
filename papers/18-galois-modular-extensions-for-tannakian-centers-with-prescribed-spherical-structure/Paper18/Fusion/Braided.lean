import Paper18.Fusion.Pivotal
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Braided fusion data, Müger centers and centralizers

Monodromy pairing and Hopf-link matrix on simple objects; Müger center and
centralizer of a full fusion subcategory (a set of simples closed under
duality and tensor).
-/

noncomputable section

open Classical

universe u

open scoped BigOperators

namespace Paper18

/-- Braided fusion data on a fusion basis. -/
structure BraidedData {ι : Type u} [Fintype ι] (B : FusionBasis ι) where
  /-- Hopf-link matrix `S_{X,Y} = tr(c_{Y,X} c_{X,Y})`. -/
  S : ι → ι → ℂ
  /-- Monodromy scalar of the double braiding. -/
  monodromy : ι → ι → ℂ
  /-- Monodromy is symmetric. -/
  monodromy_symm : ∀ x y, monodromy x y = monodromy y x
  /-- Monodromy with the unit is trivial. -/
  monodromy_unit_left : ∀ x, monodromy B.one x = 1
  monodromy_unit_right : ∀ x, monodromy x B.one = 1
  /-- The S-matrix is invertible on `ι → ℂ`. -/
  S_invertible : Function.Bijective
    (fun (v : ι → ℂ) => fun y => ∑ x, S x y * v x)

namespace BraidedData

variable {ι : Type u} [Fintype ι] {B : FusionBasis ι} (C : BraidedData B)

/-- Simple `x` is *transparent* when it monodromies trivially with every simple. -/
def IsTransparent (x : ι) : Prop := ∀ y : ι, C.monodromy x y = 1

/-- Müger center: the set of transparent simple objects. -/
def mugerCenter : Set ι := {x | C.IsTransparent x}

/-- A set of simple objects is a *full fusion subcategory* when it contains the
unit, is closed under duality, and is closed under tensor constituents. -/
def IsFullSubcategory (s : Set ι) : Prop :=
  B.one ∈ s ∧ (∀ x ∈ s, B.dual x ∈ s) ∧
    (∀ x y, x ∈ s → y ∈ s → ∀ z, 0 < B.N x y z → z ∈ s)

/-- Centralizer of a full subcategory `s`: simples monodromying trivially with
every element of `s`. -/
def centralizer (s : Set ι) : Set ι :=
  {x | ∀ y ∈ s, C.monodromy x y = 1}

lemma mugerCenter_eq_centralizer_univ :
    C.mugerCenter = C.centralizer (Set.univ : Set ι) := by
  ext x
  simp [mugerCenter, centralizer, IsTransparent]

lemma centralizer_mono_of_mono_dual
    (h : ∀ x y : ι, C.monodromy (B.dual x) y = C.monodromy x y)
    (s : Set ι) {x : ι} (hx : x ∈ C.centralizer s) :
    B.dual x ∈ C.centralizer s := by
  intro y hy
  rw [h]
  exact hx y hy

lemma centralizer_empty : C.centralizer (∅ : Set ι) = Set.univ := by
  ext x
  simp [centralizer]

lemma centralizer_univ : C.centralizer (Set.univ : Set ι) = C.mugerCenter :=
  C.mugerCenter_eq_centralizer_univ.symm

lemma isTransparent_iff_mem_muger {x : ι} :
    C.IsTransparent x ↔ x ∈ C.mugerCenter := Iff.rfl

/-- *Nondegeneracy*: the only transparent simple is the unit. -/
def Nondegenerate : Prop := ∀ x : ι, C.IsTransparent x → x = B.one

lemma nondegenerate_iff_muger_eq (h : C.Nondegenerate) :
    C.mugerCenter = ({B.one} : Set ι) := by
  ext x
  constructor
  · intro hx
    exact h x hx
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    intro y
    exact C.monodromy_unit_left y

lemma isTransparent_unit : C.IsTransparent B.one := by
  intro y
  exact C.monodromy_unit_left y

lemma mem_muger_unit : B.one ∈ C.mugerCenter := C.isTransparent_unit

/-- Hypothesis `Z_2(𝒜) = ⟨f⟩ ≅ Rep(ℤ/2)`: transparent simples are exactly
the unit and the prescribed order-two object `f`. -/
structure MugerIsOrderTwo (f : ι) where
  /-- `f` is transparent. -/
  f_transparent : C.IsTransparent f
  /-- `f` is invertible. -/
  f_invertible : B.fpdim f = 1
  /-- `f` is self-dual. -/
  f_self_dual : B.dual f = f
  /-- `f` is not the unit. -/
  f_ne_one : f ≠ B.one
  /-- Trivial self-braiding (Tannakian). -/
  self_monodromy : C.monodromy f f = 1
  /-- Exactly the two transparent simples. -/
  muger_eq : ∀ x : ι, C.IsTransparent x ↔ x = B.one ∨ x = f

lemma muger_of_orderTwo {f : ι} (T : C.MugerIsOrderTwo f)
    {x : ι} (hx : C.IsTransparent x) : x = B.one ∨ x = f :=
  T.muger_eq x |>.mp hx

lemma muger_of_orderTwo' {f : ι} (T : C.MugerIsOrderTwo f) :
    C.mugerCenter = ({B.one, f} : Set ι) := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, mugerCenter, Set.mem_setOf_eq]
  exact T.muger_eq x

/-- Dimension of a centralizer, Müger formula
`FPdim(s') = FPdim(C) · FPdim(s) / FPdim(s)` specialized in the paper. -/
def centralizerFPdim (total centralizerSub sub : ℝ) : ℝ :=
  total * centralizerSub / sub

lemma centralizerFPdim_indexTwo (FPdimK FPdimE : ℝ)
    (hK : FPdimK ≠ 0) :
    centralizerFPdim FPdimK (FPdimE / 2) (FPdimK / 2) = FPdimE := by
  simp only [centralizerFPdim]
  field_simp [hK]

end BraidedData

end Paper18
