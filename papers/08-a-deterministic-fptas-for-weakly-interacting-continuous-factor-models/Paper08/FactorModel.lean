import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic
import Paper08.Basic

/-!
# Continuous factor models

We follow Section 1 of the paper.  A model is a finite variable set `Fin n`
together with a labelled family of factors.  Each factor `e` has a nonempty
scope of size at most `r` and a positive local function on the unit cube of
its scope, with `1 ≤ Ψ_e ≤ e^q` and Euclidean Lipschitz constant at most `K`.
-/

noncomputable section

open scoped Real BigOperators

namespace Paper08

/-! ## Euclidean cubes and local functions -/

/-- The unit cube `[0,1]^k ⊆ ℝ^k` with the Euclidean structure. -/
def euclCube (k : ℕ) : Set (EuclideanSpace ℝ (Fin k)) :=
  {x | ∀ i : Fin k, 0 ≤ x i ∧ x i ≤ 1}

lemma euclCube_nonempty {k : ℕ} : (euclCube k).Nonempty :=
  ⟨0, fun _ => ⟨by norm_num, by norm_num⟩⟩

/-- Euclidean norm of a point of `ℝ^k`. -/
abbrev euclNorm {k : ℕ} (x : Fin k → ℝ) : ℝ :=
  ‖WithLp.toLp 2 x‖

/-- The Euclidean distance on `ℝ^k`. -/
abbrev euclDist {k : ℕ} (x y : Fin k → ℝ) : ℝ :=
  euclNorm (fun i => x i - y i)

/-- A local function on the unit cube of `ℝ^k`. -/
structure LocalFunc (k : ℕ) where
  toFun : (Fin k → ℝ) → ℝ

namespace LocalFunc

variable {k : ℕ} (f : LocalFunc k)

/-- Uniform sup-norm bound `‖f‖_∞ ≤ A` on the cube. -/
def BoundBy (A : ℝ) : Prop :=
  ∀ x : Fin k → ℝ, (∀ i, 0 ≤ x i ∧ x i ≤ 1) → |f.toFun x| ≤ A

/-- Euclidean Lipschitz bound `Lip₂(f) ≤ K` on the cube. -/
def LipLe (K : ℝ) : Prop :=
  ∀ x y : Fin k → ℝ, (∀ i, 0 ≤ x i ∧ x i ≤ 1) → (∀ i, 0 ≤ y i ∧ y i ≤ 1) →
    |f.toFun x - f.toFun y| ≤ K * euclDist x y

end LocalFunc

/-! ## Factor instances -/

/-- A labelled factor: a scope (nonempty, size ≤ `r`) and a local function. -/
structure Factor (n r : ℕ) where
  scope : Finset (Fin n)
  nonempty : scope.Nonempty
  card_le : scope.card ≤ r
  psi : LocalFunc scope.card

/-- `1 ≤ Ψ_e ≤ exp q` on the cube. -/
def Factor.RangeOk {n r} (e : Factor n r) (q : ℝ) : Prop :=
  e.psi.BoundBy (Real.exp q) ∧
  ∀ x : Fin e.scope.card → ℝ, (∀ i, 0 ≤ x i ∧ x i ≤ 1) → 1 ≤ e.psi.toFun x

/-- `Lip₂(Ψ_e) ≤ K`. -/
def Factor.LipOk {n r} (e : Factor n r) (K : ℝ) : Prop :=
  e.psi.LipLe K

/-- Log-factor `ℓ_e = log Ψ_e`. -/
def Factor.ell {n r} (e : Factor n r) : LocalFunc e.scope.card where
  toFun := fun x => Real.log (e.psi.toFun x)

/-- Bounded occurrence: every variable lies in at most `c` factors. -/
def BoundedOccurrence {n r} (E : Finset (Factor n r)) (c : ℕ) : Prop :=
  ∀ v : Fin n, (E.filter (fun e => v ∈ e.scope)).card ≤ c

/-- The primal graph: two distinct variables are adjacent when they share a scope. -/
def PrimalAdjacent {n r} (E : Finset (Factor n r)) (u v : Fin n) : Prop :=
  u ≠ v ∧ ∃ e ∈ E, u ∈ e.scope ∧ v ∈ e.scope

/-- The logarithmic local function has range `[0,q]`. -/
theorem Factor.ell_range {n r : ℕ} (e : Factor n r) {q : ℝ}
    (hq : e.RangeOk q) (x : Fin e.scope.card → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    0 ≤ e.ell.toFun x ∧ e.ell.toFun x ≤ q := by
  have hlow := hq.2 x hx
  have hupp : e.psi.toFun x ≤ Real.exp q :=
    (le_abs_self _).trans (hq.1 x hx)
  refine ⟨Real.log_nonneg hlow, ?_⟩
  have hl := Real.log_le_log (by linarith : 0 < e.psi.toFun x) hupp
  simpa only [Real.log_exp] using hl

/-- Passing to a logarithm preserves the Euclidean Lipschitz bound because
all factor values are at least one. -/
theorem Factor.ell_lip {n r : ℕ} (e : Factor n r) {q K : ℝ}
    (hq : e.RangeOk q) (hK : e.LipOk K) : e.ell.LipLe K := by
  intro x y hx hy
  exact (Paper08.log_abs_sub_le_abs_sub (hq.2 x hx) (hq.2 y hy)).trans (hK x y hx hy)

/-- Arity can be tightened after deriving the scope bound from primal degree. -/
def Factor.withArity {n r : ℕ} (e : Factor n r) (r' : ℕ)
    (hcard : e.scope.card ≤ r') : Factor n r' where
  scope := e.scope
  nonempty := e.nonempty
  card_le := hcard
  psi := e.psi

/-! ## Labelled occurrences

A family retains repeated occurrences even when two factors have identical
scopes and functions. All incidence counts below count labels in `Fin m`.
-/

/-- A labelled family of `m` factor occurrences. -/
abbrev FactorFamily (n r m : ℕ) := Fin m → Factor n r

/-- Bounded occurrence for a labelled family, counting every occurrence. -/
def FamilyBoundedOccurrence {n r m : ℕ} (E : FactorFamily n r m) (c : ℕ) : Prop :=
  ∀ v : Fin n, (Finset.univ.filter (fun e : Fin m => v ∈ (E e).scope)).card ≤ c

/-- The neighbours of a variable in the primal graph of a labelled family. -/
def primalNeighbors {n r m : ℕ} (E : FactorFamily n r m) (v : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter (fun u => u ≠ v ∧ ∃ e : Fin m, u ∈ (E e).scope ∧ v ∈ (E e).scope)

/-- The maximum primal degree is at most `η`. -/
def FamilyPrimalDegreeLe {n r m : ℕ} (E : FactorFamily n r m) (η : ℕ) : Prop :=
  ∀ v : Fin n, (primalNeighbors E v).card ≤ η

/-- A scope of a graph of maximum degree `η` has size at most `η + 1`. -/
theorem scope_card_le_primalDegree_add_one {n r m η : ℕ}
    (E : FactorFamily n r m) (hη : FamilyPrimalDegreeLe E η) (e : Fin m) :
    (E e).scope.card ≤ η + 1 := by
  obtain ⟨v, hv⟩ := (E e).nonempty
  have hsub : (E e).scope.erase v ⊆ primalNeighbors E v := by
    intro u hu
    rcases Finset.mem_erase.mp hu with ⟨hne, hu⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, e, hu, hv⟩
  have hc := (Finset.card_le_card hsub).trans (hη v)
  have heq := Finset.card_erase_add_one hv
  omega

/-- Every factor is nonempty, so bounded occurrence bounds the number of
labelled factors by `c * n`. This is the input-size reduction used in §4. -/
theorem family_card_le_occurrence_mul_variables {n r m c : ℕ}
    (E : FactorFamily n r m) (hc : FamilyBoundedOccurrence E c) : m ≤ c * n := by
  have hlower : m ≤ ∑ e : Fin m, (E e).scope.card := by
    calc
      m = ∑ _e : Fin m, 1 := by simp
      _ ≤ ∑ e : Fin m, (E e).scope.card := by
        apply Finset.sum_le_sum
        intro e _
        exact Finset.one_le_card.mpr (E e).nonempty
  have heq : (∑ e : Fin m, (E e).scope.card) =
      ∑ v : Fin n, (Finset.univ.filter (fun e : Fin m => v ∈ (E e).scope)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    conv_lhs => arg 2; ext e; rw [← Finset.univ_inter (E e).scope, ← Finset.sum_ite_mem]
    rw [Finset.sum_comm]
  calc
    m ≤ ∑ e : Fin m, (E e).scope.card := hlower
    _ = ∑ v : Fin n, (Finset.univ.filter (fun e : Fin m => v ∈ (E e).scope)).card := heq
    _ ≤ ∑ _v : Fin n, c := Finset.sum_le_sum (fun v _ => hc v)
    _ = c * n := by simp [Nat.mul_comm]

/-! ## Moments and coefficients (Section 2)

The integral definitions are supplied in `Paper08.Moments`.
-/

end Paper08
