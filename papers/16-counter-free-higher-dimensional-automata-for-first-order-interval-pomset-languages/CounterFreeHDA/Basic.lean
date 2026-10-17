/-
Copyright (c) 2026. Counter-Free Higher-Dimensional Automata formalisation.
Basic types: statuses, conclists, cube faces, width bounds.
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Lattice
import Mathlib.Tactic

/-!
# Basic combinatorial types for interval-pomset languages

We fix a finite alphabet `Lab` and a width bound `k`.  A *conclist* is a finite
linearly ordered set labelled by `Lab`.  Faces of a standard cube of type `U`
are indexed by `Θ_U = {0,⋆,1}^U`.

Note: we cannot use `Σ` as a binder (Lean sum-type notation); the alphabet is `Lab`.
-/

namespace CounterFreeHDA

universe u v

/-- Event status on a cube face: not started / active / terminated.
We use `Fin 3` so the linear order `0 < ⋆ < 1` is the standard one. -/
abbrev Status : Type := Fin 3

namespace Status

/-- Not started. -/
abbrev zero : Status := 0
/-- Active. -/
abbrev star : Status := 1
/-- Terminated. -/
abbrev one : Status := 2

theorem zero_lt_star : zero < star := by
  show (0 : Fin 3) < 1
  simp [zero, star]

theorem zero_lt_one : zero < one := by
  show (0 : Fin 3) < 2
  simp [zero, one]

theorem star_lt_one : star < one := by
  show (1 : Fin 3) < 2
  simp [star, one]

theorem zero_le_star : zero ≤ star := Nat.le_of_lt zero_lt_star
theorem zero_le_one : zero ≤ one := Nat.le_of_lt zero_lt_one
theorem star_le_one : star ≤ one := Nat.le_of_lt star_lt_one

/-- Numeric code of a status. -/
def code (s : Status) : ℕ := s.val

end Status

/-- An interface is a finite label list (a conclist). -/
abbrev Conclist (Lab : Type u) := List Lab

/-- Width / dimension of a conclist. -/
def Conclist.dim {Lab : Type u} (U : Conclist Lab) : ℕ := U.length

/-- Faces of the standard cube of type `U` are status lists. -/
abbrev Face {Lab : Type u} (_U : Conclist Lab) := List Status

/-- A face is well-typed when it has the same length as its conclist. -/
def Face.WellTyped {Lab : Type u} {U : Conclist Lab} (θ : Face U) : Prop :=
  θ.length = U.length

/-- The all-active face `⋆^U`. -/
def Face.allActive {Lab : Type u} (U : Conclist Lab) : Face U :=
  List.replicate U.length Status.star

theorem Face.allActive_wellTyped {Lab : Type u} (U : Conclist Lab) :
    (Face.allActive U).WellTyped := by
  simp [Face.allActive, Face.WellTyped]

/-- Elementary change of a face: one coordinate from `0` to `⋆` or from `⋆` to `1`. -/
inductive ElementaryChange {Lab : Type u} {U : Conclist Lab} : Face U → Face U → Prop where
  | start (θ : Face U) (i : ℕ) (h0 : θ[i]? = some Status.zero) :
      ElementaryChange θ (θ.set i Status.star)
  | terminate (θ : Face U) (i : ℕ) (h1 : θ[i]? = some Status.star) :
      ElementaryChange θ (θ.set i Status.one)

/-- `Θ_U` as a type: all well-typed faces. -/
def Theta (Lab : Type u) (U : Conclist Lab) : Type _ :=
  { θ : Face U // θ.WellTyped }

/-- Conclists of length at most `k` over an alphabet. -/
def ConclistsUpTo (Lab : Type u) (k : ℕ) : Type _ :=
  { U : List Lab // U.length ≤ k }

theorem ConclistsUpTo.length_le {Lab : Type u} {k : ℕ} (U : ConclistsUpTo Lab k) :
    U.1.length ≤ k := U.2

/-- A face of type `U` as a function on positions. -/
def Face.toFun {Lab : Type u} {U : Conclist Lab} (θ : Face U) :
    ℕ → Status :=
  fun i => θ[i]?.getD Status.zero

end CounterFreeHDA
