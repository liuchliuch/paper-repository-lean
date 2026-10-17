import K44K35Free.Cap
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fin.VecNotation

/-! Concrete homogeneous geometry for the quartic construction. -/
namespace K44K35Free.Geometry

noncomputable section

open scoped BigOperators
open Polynomial Module

abbrev V (F : Type*) := Fin 6 → F
abbrev Param (F : Type*) := Fin 3 → F
abbrev Quartic (F : Type*) := Fin 4 → F

/-- The four free lower coefficients of a monic quartic. -/
def quarticPolynomial {F : Type*} [Field F] (c : Quartic F) : F[X] :=
  X ^ 4 + ∑ i : Fin 4, Polynomial.C (c i) * X ^ (i : ℕ)

/-- The affine parameters label the actual points of the paper's set. -/
def point {F : Type*} [Field F] (α : F) (c : Quartic F) (p : Param F) : V F :=
  ![1, p 0, p 1, p 2, (p 0)^2,
    (p 1)^2 - α * (p 2)^2 + (quarticPolynomial c).eval (p 0)]

/-- A projective plane is a three-dimensional vector subspace. -/
abbrev Plane (F : Type*) [Field F] :=
  { U : Submodule F (V F) // finrank F U = 3 }

instance planeFinite {F : Type*} [Field F] [Finite F] : Finite (Plane F) := by
  apply Finite.of_injective (fun E : Plane F => (E.val : Set (V F)))
  intro E G h
  apply Subtype.ext
  exact SetLike.coe_injective h

noncomputable def planeSection {F : Type*} [Field F] [Fintype F]
    (α : F) (c : Quartic F) (E : Plane F) : Finset (Param F) := by
  classical
  exact Finset.univ.filter (fun p => point α c p ∈ E.val)

@[simp] theorem mem_section {F : Type*} [Field F] [Fintype F]
    (α : F) (c : Quartic F) (E : Plane F) (p : Param F) :
    p ∈ planeSection α c E ↔ point α c p ∈ E.val := by
  classical
  simp [planeSection]

structure GraphData (F : Type*) where
  A : Fin 3 → F
  B : Fin 3 → F
  C : Fin 3 → F
  deriving DecidableEq, Fintype

/-- Affine coefficients, in homogeneous variables `(w,x,u)`. -/
def linEval {F : Type*} [Field F] (a t : Fin 3 → F) : F :=
  a 0 * t 0 + a 1 * t 1 + a 2 * t 2

def graphMap {F : Type*} [Field F] (g : GraphData F) : (Fin 3 → F) →ₗ[F] V F where
  toFun t := ![t 0, t 1, linEval g.A t, linEval g.B t, t 2, linEval g.C t]
  map_add' s t := by
    ext i
    fin_cases i <;> simp [linEval, mul_add] <;> ring
  map_smul' a t := by
    ext i
    fin_cases i <;> simp [linEval] <;> ring

@[simp] theorem graphMap_injective {F : Type*} [Field F] (g : GraphData F) :
    Function.Injective (graphMap g) := by
  intro s t h
  funext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1
  · exact congrFun h 4

noncomputable def graphPlane {F : Type*} [Field F] (g : GraphData F) : Plane F :=
  ⟨LinearMap.range (graphMap g), by
    simpa using LinearMap.finrank_range_of_inj (graphMap_injective g)⟩

def qPolynomial {F : Type*} [Field F] (a : Fin 3 → F) : F[X] :=
  Polynomial.C (a 0) + Polynomial.C (a 1) * X + Polynomial.C (a 2) * X ^ 2

def sectionPolynomial {F : Type*} [Field F] (α : F) (c : Quartic F)
    (g : GraphData F) : F[X] :=
  quarticPolynomial c + qPolynomial g.A ^ 2 - Polynomial.C α * qPolynomial g.B ^ 2 -
    qPolynomial g.C

/-- The solid with fixed affine x coordinate. -/
def fiberSubspace {F : Type*} [Field F] (d : F) : Submodule F (V F) where
  carrier := {v | v 1 = d * v 0 ∧ v 4 = d ^ 2 * v 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change (a 1 + b 1 = d * (a 0 + b 0)) ∧
      (a 4 + b 4 = d ^ 2 * (a 0 + b 0))
    constructor
    · rw [ha.1, hb.1]; ring
    · rw [ha.2, hb.2]; ring
  smul_mem' := by
    intro a v hv
    change (a * v 1 = d * (a * v 0)) ∧ (a * v 4 = d ^ 2 * (a * v 0))
    constructor
    · rw [hv.1]; ring
    · rw [hv.2]; ring

def IdentityExceptional {F : Type*} [Field F] (α : F) (c : Quartic F)
    (E : Plane F) : Prop :=
  ∃ g : GraphData F, graphPlane g = E ∧ sectionPolynomial α c g = 0

def FiberExceptional {F : Type*} [Field F] (E : Plane F) : Prop :=
  ∃ d : F, E.val ≤ fiberSubspace d

def Exceptional {F : Type*} [Field F] (α : F) (c : Quartic F)
    (E : Plane F) : Prop :=
  IdentityExceptional α c E ∨ FiberExceptional E

@[simp] theorem mem_graphPlane {F : Type*} [Field F] (g : GraphData F) (v : V F) :
    v ∈ (graphPlane g).val ↔
      v 2 = linEval g.A ![v 0, v 1, v 4] ∧
      v 3 = linEval g.B ![v 0, v 1, v 4] ∧
      v 5 = linEval g.C ![v 0, v 1, v 4] := by
  change (∃ t, graphMap g t = v) ↔ _
  constructor
  · rintro ⟨t, rfl⟩
    simp [graphMap, linEval]
  · rintro ⟨ha, hb, hc⟩
    refine ⟨![v 0, v 1, v 4], ?_⟩
    ext i
    fin_cases i <;> simp [graphMap, linEval] at * <;> symm <;> assumption

theorem graphPlane_injective {F : Type*} [Field F] :
    Function.Injective (graphPlane (F := F)) := by
  intro g h heq
  have coords (t : Fin 3 → F) :
      linEval g.A t = linEval h.A t ∧ linEval g.B t = linEval h.B t ∧
        linEval g.C t = linEval h.C t := by
    have hm : graphMap g t ∈ (graphPlane h).val := by
      rw [← heq]
      exact LinearMap.mem_range_self _ _
    simpa [graphMap, linEval] using (mem_graphPlane h (graphMap g t)).mp hm
  have ha : g.A = h.A := by
    ext i
    have hx := (coords (Pi.single i 1)).1
    fin_cases i <;> simpa [linEval, Pi.single_apply] using hx
  have hb : g.B = h.B := by
    ext i
    have hx := (coords (Pi.single i 1)).2.1
    fin_cases i <;> simpa [linEval, Pi.single_apply] using hx
  have hc : g.C = h.C := by
    ext i
    have hx := (coords (Pi.single i 1)).2.2
    fin_cases i <;> simpa [linEval, Pi.single_apply] using hx
  cases g
  cases h
  simp_all

@[simp] theorem qPolynomial_eval {F : Type*} [Field F] (a : Fin 3 → F) (t : F) :
    (qPolynomial a).eval t = a 0 + a 1 * t + a 2 * t ^ 2 := by
  simp [qPolynomial]

@[simp] theorem point_mem_graphPlane_iff {F : Type*} [Field F]
    (α : F) (c : Quartic F) (g : GraphData F) (p : Param F) :
    point α c p ∈ (graphPlane g).val ↔
      p 1 = (qPolynomial g.A).eval (p 0) ∧
      p 2 = (qPolynomial g.B).eval (p 0) ∧
      (sectionPolynomial α c g).eval (p 0) = 0 := by
  rw [mem_graphPlane]
  change (p 1 = g.A 0 * 1 + g.A 1 * p 0 + g.A 2 * (p 0)^2 ∧
    p 2 = g.B 0 * 1 + g.B 1 * p 0 + g.B 2 * (p 0)^2 ∧
    (p 1)^2 - α * (p 2)^2 + (quarticPolynomial c).eval (p 0) =
      g.C 0 * 1 + g.C 1 * p 0 + g.C 2 * (p 0)^2) ↔ _
  simp only [mul_one, qPolynomial_eval]
  constructor
  · rintro ⟨ha, hb, hc⟩
    refine ⟨ha, hb, ?_⟩
    simp only [sectionPolynomial, eval_sub, eval_add, eval_pow, eval_mul, eval_C,
      qPolynomial_eval]
    rw [← ha, ← hb]
    linear_combination hc
  · rintro ⟨ha, hb, hc⟩
    refine ⟨ha, hb, ?_⟩
    simp only [sectionPolynomial, eval_sub, eval_add, eval_pow, eval_mul, eval_C,
      qPolynomial_eval] at hc
    rw [← ha, ← hb] at hc
    linear_combination hc

@[simp] theorem point_injective {F : Type*} [Field F] (α : F) (c : Quartic F) :
    Function.Injective (point α c) := by
  intro p q h
  ext i
  fin_cases i
  · exact congrFun h 1
  · exact congrFun h 2
  · exact congrFun h 3

@[simp] theorem point_ne_zero {F : Type*} [Field F] (α : F) (c : Quartic F)
    (p : Param F) : point α c p ≠ 0 := by
  intro h
  have := congrFun h 0
  simpa [point] using this

end
end K44K35Free.Geometry
