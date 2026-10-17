import Paper32.Geometry
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.FinCases

/-!
The algebraic and polyhedral function-class assertions of Lemma 3.1.
Semialgebraic means a finite Boolean combination of polynomial inequalities in
real affine space.  Polyhedra are finite intersections of closed affine
halfspaces.  Neither definition refers to the particular objective.
-/

open Set

namespace Paper32

/-- A real affine form on the paper's two-dimensional space. -/
structure AffineForm where
  x : ℝ
  y : ℝ
  c : ℝ

def AffineForm.eval (a : AffineForm) (z : Point) : ℝ := a.x * z.1 + a.y * z.2 + a.c

theorem AffineForm.continuous (a : AffineForm) : Continuous a.eval := by
  unfold eval
  fun_prop

/-- Coefficient forms satisfy the usual affine-combination identity. -/
theorem AffineForm.affineCombination (a : AffineForm) (z w : Point) (t : ℝ) :
    a.eval (t • z + (1 - t) • w) = t * a.eval z + (1 - t) * a.eval w := by
  simp [eval]
  ring

def AffineForm.sub (a b : AffineForm) : AffineForm := ⟨a.x - b.x, a.y - b.y, a.c - b.c⟩
def AffineForm.neg (a : AffineForm) : AffineForm := ⟨-a.x, -a.y, -a.c⟩
def AffineForm.addConst (a : AffineForm) (c : ℝ) : AffineForm := ⟨a.x, a.y, a.c + c⟩

@[simp] theorem AffineForm.eval_sub (a b : AffineForm) (z : Point) :
    (a.sub b).eval z = a.eval z - b.eval z := by simp [sub, eval]; ring
@[simp] theorem AffineForm.eval_neg (a : AffineForm) (z : Point) :
    a.neg.eval z = -a.eval z := by simp [neg, eval]; ring
@[simp] theorem AffineForm.eval_addConst (a : AffineForm) (c : ℝ) (z : Point) :
    (a.addConst c).eval z = a.eval z + c := by simp [addConst, eval]; ring

/-- A (closed convex) polyhedron is a finite intersection of affine halfspaces. -/
def IsPolyhedron (s : Set Point) : Prop :=
  ∃ (n : ℕ) (a : Fin n → AffineForm), s = {z | ∀ i, 0 ≤ (a i).eval z}

/-- A finite polyhedral cover on which the function has affine formulas.
Boundary faces may be shared, with the same function value on every shared face. -/
def FinitePiecewiseAffine (f : Point → ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (cell : ι → Set Point) (a : ι → AffineForm),
    (∀ i, IsPolyhedron (cell i)) ∧ (∀ z, ∃ i, z ∈ cell i) ∧
      ∀ i z, z ∈ cell i → f z = (a i).eval z

def ContinuousPiecewiseAffine (f : Point → ℝ) : Prop :=
  Continuous f ∧ FinitePiecewiseAffine f

/-- Standard quantifier-free real polynomial formulas. -/
inductive PolynomialFormula (n : ℕ) where
  | nonneg (p : MvPolynomial (Fin n) ℝ)
  | truth
  | compl (p : PolynomialFormula n)
  | conj (p q : PolynomialFormula n)
  | disj (p q : PolynomialFormula n)

def PolynomialFormula.Holds {n : ℕ} : PolynomialFormula n → (Fin n → ℝ) → Prop
  | .nonneg p, q => 0 ≤ MvPolynomial.eval q p
  | .truth, _ => True
  | .compl p, q => ¬ p.Holds q
  | .conj p r, q => p.Holds q ∧ r.Holds q
  | .disj p r, q => p.Holds q ∨ r.Holds q

/-- Finite Boolean combinations of polynomial weak inequalities.
Strict inequalities and polynomial equations are included using complement
and pairs of weak inequalities, respectively. -/
def IsSemialgebraic {n : ℕ} (s : Set (Fin n → ℝ)) : Prop :=
  ∃ p : PolynomialFormula n, s = {q | p.Holds q}

def SemialgebraicFunction (f : Point → ℝ) : Prop :=
  IsSemialgebraic {q : Fin 3 → ℝ | q 2 = f (q 0, q 1)}

private def PolynomialFormula.all {n : ℕ} : List (PolynomialFormula n) → PolynomialFormula n
  | [] => .truth
  | p :: ps => .conj p (all ps)

private def PolynomialFormula.any {n : ℕ} : List (PolynomialFormula n) → PolynomialFormula n
  | [] => .compl .truth
  | p :: ps => .disj p (any ps)

@[simp] private theorem holds_all {n : ℕ} (ps : List (PolynomialFormula n)) (q) :
    (PolynomialFormula.all ps).Holds q ↔ ∀ p ∈ ps, p.Holds q := by
  induction ps with
  | nil => simp [PolynomialFormula.all, PolynomialFormula.Holds]
  | cons p ps ih => simp [PolynomialFormula.all, PolynomialFormula.Holds, ih]

@[simp] private theorem holds_any {n : ℕ} (ps : List (PolynomialFormula n)) (q) :
    (PolynomialFormula.any ps).Holds q ↔ ∃ p ∈ ps, p.Holds q := by
  induction ps with
  | nil => simp [PolynomialFormula.any, PolynomialFormula.Holds]
  | cons p ps ih => simp [PolynomialFormula.any, PolynomialFormula.Holds, ih]

private noncomputable def allIndexed {n : ℕ} {ι : Type} [Fintype ι]
    (p : ι → PolynomialFormula n) : PolynomialFormula n := by
  classical
  exact PolynomialFormula.all (Finset.univ.toList.map p)

private noncomputable def anyIndexed {n : ℕ} {ι : Type} [Fintype ι]
    (p : ι → PolynomialFormula n) : PolynomialFormula n := by
  classical
  exact PolynomialFormula.any (Finset.univ.toList.map p)

@[simp] private theorem holds_allIndexed {n : ℕ} {ι : Type} [Fintype ι]
    (p : ι → PolynomialFormula n) (q) : (allIndexed p).Holds q ↔ ∀ i, (p i).Holds q := by
  classical
  simp [allIndexed]

@[simp] private theorem holds_anyIndexed {n : ℕ} {ι : Type} [Fintype ι]
    (p : ι → PolynomialFormula n) (q) : (anyIndexed p).Holds q ↔ ∃ i, (p i).Holds q := by
  classical
  simp [anyIndexed]

/-- The polynomial representing a two-variable affine form in graph space. -/
noncomputable def AffineForm.polynomial (a : AffineForm) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.C a.x * MvPolynomial.X 0 +
    MvPolynomial.C a.y * MvPolynomial.X 1 + MvPolynomial.C a.c

@[simp] theorem AffineForm.eval_polynomial (a : AffineForm) (q : Fin 3 → ℝ) :
    MvPolynomial.eval q a.polynomial = a.eval (q 0, q 1) := by
  simp [polynomial, eval]

/-- Each choice records signs of x,y, the active minimum branch, and the
active maximum branch, hence there are sixteen regions. -/
abbrev AffineRegion := Bool × Bool × Bool × Bool

private def signed (b : Bool) : ℝ := if b then 1 else -1
private def signedX (b : Bool) : AffineForm := ⟨signed b, 0, 0⟩
private def signedY (b : Bool) : AffineForm := ⟨0, signed b, 0⟩
private def branchA (sx sy : Bool) : AffineForm := ⟨signed sx, 2 * signed sy, 0⟩
private def branchB (sx sy : Bool) : AffineForm := ⟨7 * signed sx, -signed sy, 0⟩
private def branchL (sx sy : Bool) : AffineForm := ⟨signed sx, signed sy, 0⟩
private def coreAffine (r : AffineRegion) : AffineForm :=
  if r.2.2.1 then branchA r.1 r.2.1 else branchB r.1 r.2.1

def regionAffine (r : AffineRegion) : AffineForm :=
  if r.2.2.2 then (coreAffine r).addConst 8 else branchL r.1 r.2.1

private def regionConstraint (r : AffineRegion) (i : Fin 4) : AffineForm :=
  if i = 0 then signedX r.1 else
  if i = 1 then signedY r.2.1 else
  if i = 2 then
    if r.2.2.1 then (branchB r.1 r.2.1).sub (branchA r.1 r.2.1)
    else (branchA r.1 r.2.1).sub (branchB r.1 r.2.1)
  else
    if r.2.2.2 then ((coreAffine r).addConst 8).sub (branchL r.1 r.2.1)
    else (branchL r.1 r.2.1).sub ((coreAffine r).addConst 8)

def regionCell (r : AffineRegion) : Set Point :=
  {z | ∀ i, 0 ≤ (regionConstraint r i).eval z}

theorem regionCell_polyhedron (r : AffineRegion) : IsPolyhedron (regionCell r) :=
  ⟨4, regionConstraint r, rfl⟩

private theorem mem_regionCell (r : AffineRegion) (z : Point) :
    z ∈ regionCell r ↔
      0 ≤ (signedX r.1).eval z ∧ 0 ≤ (signedY r.2.1).eval z ∧
      (if r.2.2.1 then (branchA r.1 r.2.1).eval z ≤ (branchB r.1 r.2.1).eval z
        else (branchB r.1 r.2.1).eval z ≤ (branchA r.1 r.2.1).eval z) ∧
      (if r.2.2.2 then (branchL r.1 r.2.1).eval z ≤ (coreAffine r).eval z + 8
        else (coreAffine r).eval z + 8 ≤ (branchL r.1 r.2.1).eval z) := by
  rcases r with ⟨sx, sy, b, c⟩
  cases b <;> cases c <;>
    simp [regionCell, regionConstraint, Fin.forall_fin_succ, sub_nonneg]

private theorem abs_eq_signed {b : Bool} {x : ℝ} (h : 0 ≤ signed b * x) :
    |x| = signed b * x := by
  cases b <;> simp only [signed, Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul] at *
  · exact abs_of_nonpos (by linarith)
  · exact abs_of_nonneg h

private theorem branch_values {r : AffineRegion} {z : Point} (hz : z ∈ regionCell r) :
    (branchA r.1 r.2.1).eval z = |z.1| + 2 * |z.2| ∧
    (branchB r.1 r.2.1).eval z = 7 * |z.1| - |z.2| ∧
    (branchL r.1 r.2.1).eval z = l1 z := by
  have hs := (mem_regionCell r z).mp hz
  have hx : |z.1| = signed r.1 * z.1 := abs_eq_signed (by simpa [signedX, AffineForm.eval] using hs.1)
  have hy : |z.2| = signed r.2.1 * z.2 := abs_eq_signed (by simpa [signedY, AffineForm.eval] using hs.2.1)
  simp only [branchA, branchB, branchL, AffineForm.eval, l1, hx, hy]
  constructor
  · ring
  constructor <;> ring

private theorem core_value {r : AffineRegion} {z : Point} (hz : z ∈ regionCell r) :
    (coreAffine r).eval z = g z := by
  have hs := (mem_regionCell r z).mp hz
  have hb := branch_values hz
  by_cases h : r.2.2.1 = true
  · simp only [coreAffine, h, ↓reduceIte]
    rw [hb.1]
    exact (min_eq_left (by simpa [h, hb.1, hb.2.1] using hs.2.2.1)).symm
  · simp only [coreAffine, h, Bool.false_eq_true, ↓reduceIte]
    rw [hb.2.1]
    exact (min_eq_right (by simpa [h, hb.1, hb.2.1] using hs.2.2.1)).symm

theorem F_eq_regionAffine {r : AffineRegion} {z : Point} (hz : z ∈ regionCell r) :
    F z = (regionAffine r).eval z := by
  have hs := (mem_regionCell r z).mp hz
  have hb := branch_values hz
  have hc := core_value hz
  by_cases h : r.2.2.2 = true
  · simp only [regionAffine, h, ↓reduceIte, AffineForm.eval_addConst, hc]
    exact max_eq_left (by simpa [h, hb.2.2, hc] using hs.2.2.2)
  · simp only [regionAffine, h, Bool.false_eq_true, ↓reduceIte, hb.2.2]
    exact max_eq_right (by simpa [h, hb.2.2, hc] using hs.2.2.2)

theorem regionCells_cover (z : Point) : ∃ r : AffineRegion, z ∈ regionCell r := by
  classical
  let sx : Bool := decide (0 ≤ z.1)
  let sy : Bool := decide (0 ≤ z.2)
  have hx : (signedX sx).eval z = |z.1| := by
    by_cases h : 0 ≤ z.1
    · simp [sx, h, signedX, signed, AffineForm.eval, abs_of_nonneg h]
    · simp [sx, h, signedX, signed, AffineForm.eval, abs_of_neg (lt_of_not_ge h)]
  have hy : (signedY sy).eval z = |z.2| := by
    by_cases h : 0 ≤ z.2
    · simp [sy, h, signedY, signed, AffineForm.eval, abs_of_nonneg h]
    · simp [sy, h, signedY, signed, AffineForm.eval, abs_of_neg (lt_of_not_ge h)]
  let b : Bool := decide ((branchA sx sy).eval z ≤ (branchB sx sy).eval z)
  let c : Bool := decide ((branchL sx sy).eval z ≤
    (coreAffine (sx, sy, b, false)).eval z + 8)
  refine ⟨(sx, sy, b, c), (mem_regionCell _ _).mpr ⟨?_, ?_, ?_, ?_⟩⟩
  · simpa only [hx] using abs_nonneg z.1
  · simpa only [hy] using abs_nonneg z.2
  · dsimp [b]
    split <;> simp_all
    all_goals linarith
  · have heq : coreAffine (sx, sy, b, c) = coreAffine (sx, sy, b, false) := rfl
    rw [heq]
    dsimp [c]
    split <;> simp_all
    all_goals linarith

theorem finitePiecewiseAffine_F : FinitePiecewiseAffine F :=
  ⟨AffineRegion, inferInstance, regionCell, regionAffine,
    regionCell_polyhedron, regionCells_cover, fun _ _ hz => F_eq_regionAffine hz⟩

theorem continuousPiecewiseAffine_F : ContinuousPiecewiseAffine F :=
  ⟨continuous_F, finitePiecewiseAffine_F⟩

private noncomputable def graphDifference (a : AffineForm) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.X 2 - a.polynomial

private noncomputable def regionGraphFormula (r : AffineRegion) : PolynomialFormula 3 :=
  .conj (allIndexed (fun i : Fin 4 => .nonneg (regionConstraint r i).polynomial))
    (.conj (.nonneg (graphDifference (regionAffine r)))
      (.nonneg (-graphDifference (regionAffine r))))

private theorem holds_regionGraphFormula (r : AffineRegion) (q : Fin 3 → ℝ) :
    (regionGraphFormula r).Holds q ↔
      (q 0, q 1) ∈ regionCell r ∧ q 2 = (regionAffine r).eval (q 0, q 1) := by
  simp only [regionGraphFormula, PolynomialFormula.Holds, holds_allIndexed]
  simp only [AffineForm.eval_polynomial, graphDifference, MvPolynomial.eval_sub,
    MvPolynomial.eval_X, MvPolynomial.eval_neg, AffineForm.eval_polynomial]
  change (∀ i, 0 ≤ (regionConstraint r i).eval (q 0, q 1)) ∧
      (0 ≤ q 2 - (regionAffine r).eval (q 0, q 1) ∧
        0 ≤ -(q 2 - (regionAffine r).eval (q 0, q 1))) ↔ _
  constructor
  · rintro ⟨hc, h₁, h₂⟩
    exact ⟨hc, by linarith⟩
  · rintro ⟨hc, he⟩
    exact ⟨hc, by rw [he]; simp, by rw [he]; simp⟩

/-- The complete graph of F is given by a finite Boolean combination of
actual three-variable real polynomial inequalities. -/
theorem semialgebraic_F : SemialgebraicFunction F := by
  refine ⟨anyIndexed regionGraphFormula, ?_⟩
  ext q
  simp only [Set.mem_setOf_eq, holds_anyIndexed, holds_regionGraphFormula]
  constructor
  · intro h
    rcases regionCells_cover (q 0, q 1) with ⟨r, hr⟩
    exact ⟨r, hr, h.trans (F_eq_regionAffine hr)⟩
  · rintro ⟨r, hr, h⟩
    exact h.trans (F_eq_regionAffine hr).symm

end Paper32
