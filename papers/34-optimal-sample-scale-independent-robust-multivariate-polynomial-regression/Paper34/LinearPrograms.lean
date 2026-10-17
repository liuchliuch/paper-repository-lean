import Paper34.Model
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases

/-! Actual dense-monomial LP encodings for Section 6. The exact finite
variable/row counts below cover the combinatorial portion of Proposition
6.2. They do not prove the missing coercivity or asymptotic work bounds. -/
open BigOperators
namespace Paper34
noncomputable section

abbrev Exponent (n d : ℕ) := Fin n → Fin (d+1)

def exponentEquiv (n d : ℕ) :
    {f : Fin n →₀ ℕ // ∀ k, f k ≤ d} ≃ Exponent n d where
  toFun f k := ⟨f.1 k, Nat.lt_succ_iff.mpr (f.2 k)⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun k => (f k : ℕ)), by
    intro k
    simpa using Nat.le_of_lt_succ (f k).isLt⟩
  left_inv f := by apply Subtype.ext; ext k; rfl
  right_inv f := by funext k; apply Fin.ext; rfl

theorem card_exponent (n d : ℕ) : Fintype.card (Exponent n d) = (d+1)^n := by
  simp [Exponent]

/-- The exact dimension of the source coordinate-degree polynomial space. -/
theorem finrank_polynomialSpace (n d : ℕ) :
    Module.finrank ℝ (PolynomialSpace n d) = (d+1)^n := by
  let b := (MvPolynomial.basisRestrictSupport ℝ
    {f : Fin n →₀ ℕ | ∀ k, f k ≤ d}).reindex (exponentEquiv n d)
  change Module.finrank ℝ (MvPolynomial.restrictSupport ℝ
    {f : Fin n →₀ ℕ | ∀ k, f k ≤ d}) = _
  exact (Module.finrank_eq_card_basis b).trans (card_exponent n d)

/-- The actual polynomial encoded by dense monomial coefficients. -/
def densePolynomial {n d : ℕ} (c : Exponent n d → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ a, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun k => (a k : ℕ))) (c a)

/-- Every dense coefficient vector encodes a polynomial in the source space. -/
theorem densePolynomial_mem {n d : ℕ} (c : Exponent n d → ℝ) :
    densePolynomial c ∈ MvPolynomial.restrictDegree (Fin n) ℝ d := by
  classical
  unfold densePolynomial
  apply Submodule.sum_mem
  intro a _
  rw [MvPolynomial.mem_restrictDegree]
  intro s hs k
  have heq := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hs)
  subst s
  change (a k : ℕ) ≤ d
  exact Nat.le_of_lt_succ (a k).isLt

def denseEval {n d : ℕ} (c : Exponent n d → ℝ) (x : Point n) : ℝ :=
  ∑ a, c a * ∏ k, x k ^ (a k : ℕ)

theorem eval_densePolynomial {n d : ℕ} (c : Exponent n d → ℝ) (x : Point n) :
    MvPolynomial.eval x (densePolynomial c) = denseEval c x := by
  simp [densePolynomial, denseEval, MvPolynomial.eval_monomial]

abbrev InitializerVariable (n d M : ℕ) := Sum (Exponent n d) (Fin M)
abbrev InitializerRow (M : ℕ) := Fin M × Bool
abbrev RefinementVariable (n d : ℕ) := Option (Exponent n d)
abbrev RefinementRow (n m : ℕ) := CellIndex n m × Bool

def initCoefficients {n d M : ℕ} (v : InitializerVariable n d M → ℝ) :
    Exponent n d → ℝ := fun a => v (Sum.inl a)

def initSlacks {n d M : ℕ} (v : InitializerVariable n d M → ℝ) (i : Fin M) : ℝ :=
  v (Sum.inr i)

/-- Each observation supplies its two affine residual inequalities. -/
def initializerConstraint {n d M : ℕ} (X : Fin M → Point n) (Y : Fin M → ℝ)
    (v : InitializerVariable n d M → ℝ) (row : InitializerRow M) : Prop :=
  if row.2 then denseEval (initCoefficients v) (X row.1) - Y row.1 ≤ initSlacks v row.1
  else -(initSlacks v row.1) ≤ denseEval (initCoefficients v) (X row.1) - Y row.1

theorem initializer_constraints_iff {n d M : ℕ} (X : Fin M → Point n) (Y : Fin M → ℝ)
    (v : InitializerVariable n d M → ℝ) :
    (∀ row, initializerConstraint X Y v row) ↔
      ∀ i, |MvPolynomial.eval (X i) (densePolynomial (initCoefficients v)) - Y i| ≤
        initSlacks v i := by
  simp only [eval_densePolynomial]
  constructor
  · intro h i
    exact abs_le.mpr ⟨by simpa [initializerConstraint] using h (i, false),
      by simpa [initializerConstraint] using h (i, true)⟩
  · intro h row
    rcases row with ⟨i, b⟩
    cases b with
    | false => simpa [initializerConstraint] using (abs_le.mp (h i)).1
    | true => simpa [initializerConstraint] using (abs_le.mp (h i)).2

/-- A refinement has a single scalar lambda and a dense coefficient block. -/
def refinementConstraint {n d m : ℕ} (a : CellIndex n m → Point n)
    (y : CellIndex n m → ℝ) (v : RefinementVariable n d → ℝ)
    (row : RefinementRow n m) : Prop :=
  if row.2 then denseEval (fun e => v (some e)) (a row.1) - y row.1 ≤ v none
  else -(v none) ≤ denseEval (fun e => v (some e)) (a row.1) - y row.1

theorem refinement_constraints_iff {n d m : ℕ} (a : CellIndex n m → Point n)
    (y : CellIndex n m → ℝ) (v : RefinementVariable n d → ℝ) :
    (∀ row, refinementConstraint a y v row) ↔
      ∀ j, |MvPolynomial.eval (a j) (densePolynomial (fun e => v (some e))) - y j| ≤
        v none := by
  simp only [eval_densePolynomial]
  constructor
  · intro h j
    exact abs_le.mpr ⟨by simpa [refinementConstraint] using h (j, false),
      by simpa [refinementConstraint] using h (j, true)⟩
  · intro h row
    rcases row with ⟨j, b⟩
    cases b with
    | false => simpa [refinementConstraint] using (abs_le.mp (h j)).1
    | true => simpa [refinementConstraint] using (abs_le.mp (h j)).2

/-- Exact variable and residual-row counts for the two concrete encodings. -/
theorem lp_description_counts (n d m M : ℕ) :
    Fintype.card (InitializerVariable n d M) = (d+1)^n + M ∧
    Fintype.card (InitializerRow M) = 2*M ∧
    Fintype.card (RefinementVariable n d) = (d+1)^n + 1 ∧
    Fintype.card (RefinementRow n m) = 2*m^n := by
  simp [InitializerVariable, InitializerRow, RefinementVariable, RefinementRow,
    CellIndex, Nat.mul_comm]

end
end Paper34
