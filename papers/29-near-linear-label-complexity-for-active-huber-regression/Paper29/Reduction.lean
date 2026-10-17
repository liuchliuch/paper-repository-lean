import Paper29.Localization
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Removing zero rows and lifting finite-dimensional coordinates

The retained row type is the actual subtype of nonzero rows of the input.
The objective decomposition and coordinate lifting below are identities proved
from matrix multiplication, rather than assumptions on an abstract reduction.
-/
noncomputable section
open scoped BigOperators

namespace Paper29.Reduction

/-- The actual rows which depend on the decision variable. -/
def RetainedRows {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :=
  {i : Fin n // A i ≠ 0}

/-- The actual rows which contribute only an additive constant. -/
def ZeroRows {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :=
  {i : Fin n // A i = 0}

instance retainedFinite {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    Finite (RetainedRows A) := inferInstanceAs (Finite {i : Fin n // A i ≠ 0})

instance zeroFinite {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    Finite (ZeroRows A) := inferInstanceAs (Finite {i : Fin n // A i = 0})

noncomputable instance retainedFintype {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    Fintype (RetainedRows A) := by
  classical
  exact Subtype.fintype _

noncomputable instance zeroFintype {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    Fintype (ZeroRows A) := by
  classical
  exact Subtype.fintype _

/-- The restricted design contains precisely the nonzero original rows. -/
def retainedDesign {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    Matrix (RetainedRows A) (Fin d) ℝ := fun i j => A i.val j

def retainedObjective {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (b : Fin n → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i : RetainedRows A, huber (((retainedDesign A).mulVec x) i - b i.val)

def zeroRowCost {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (b : Fin n → ℝ) : ℝ := ∑ i : ZeroRows A, huber (-b i.val)

@[simp] theorem retained_prediction {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (x : Fin d → ℝ) (i : RetainedRows A) :
    ((retainedDesign A).mulVec x) i = (A.mulVec x) i.val := rfl

/-- Every removed row has prediction zero for every decision vector. -/
theorem zero_row_prediction {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (x : Fin d → ℝ) (i : ZeroRows A) : (A.mulVec x) i.val = 0 := by
  change dotProduct (A i.val) x = 0
  rw [i.property]
  simp [dotProduct]

theorem zeroRowCost_nonneg {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (b : Fin n → ℝ) : 0 ≤ zeroRowCost A b :=
  Finset.sum_nonneg (fun i _ => huber_nonneg (-b i.val))

theorem retainedObjective_nonneg {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (b : Fin n → ℝ) (x : Fin d → ℝ) : 0 ≤ retainedObjective A b x :=
  Finset.sum_nonneg (fun _ _ => huber_nonneg _)

/-- The exact zero-row decomposition used after equation (3.46). -/
theorem objective_eq_constant_add_retained {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) (x : Fin d → ℝ) :
    objective A b x = zeroRowCost A b + retainedObjective A b x := by
  classical
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i : Fin n => A i = 0)
    (fun i => huber ((A.mulVec x) i - b i))
  calc
    objective A b x = (∑ i : ZeroRows A, huber ((A.mulVec x) i.val - b i.val)) +
        ∑ i : RetainedRows A, huber ((A.mulVec x) i.val - b i.val) := hsplit.symm
    _ = zeroRowCost A b + retainedObjective A b x := by
      congr 1
      · unfold zeroRowCost
        apply Finset.sum_congr rfl
        intro i hi
        rw [zero_row_prediction, zero_sub]

/-- Removing zero rows preserves exactly which decision vectors minimize. -/
theorem minimizer_iff_retained {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) (x : Fin d → ℝ) :
    (∀ y, objective A b x ≤ objective A b y) ↔
      ∀ y, retainedObjective A b x ≤ retainedObjective A b y := by
  simp only [objective_eq_constant_add_retained, add_le_add_iff_left]

/-- The rows selected for the reduced design really are nonzero. -/
theorem retained_row_nonzero {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (i : RetainedRows A) : retainedDesign A i ≠ 0 := i.property

/-- The retained problem never has more rows than the original one. -/
theorem retained_card_le {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    Fintype.card (RetainedRows A) ≤ n := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
    (fun i : RetainedRows A => i.val) Subtype.val_injective

/-- Actual coordinate lifting for an arbitrary matrix of decision coordinates. -/
def coordinateDesign {n d r : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin d) (Fin r) ℝ) : Matrix (RetainedRows A) (Fin r) ℝ :=
  retainedDesign A * U

def coordinateObjective {n d r : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin d) (Fin r) ℝ) (b : Fin n → ℝ) (y : Fin r → ℝ) : ℝ :=
  ∑ i : RetainedRows A, huber (((coordinateDesign A U).mulVec y) i - b i.val)

/-- The coordinate design predicts exactly the retained original predictions
at the actual lift `U * y`. No factorization hypothesis is required. -/
theorem coordinate_predictions {n d r : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin d) (Fin r) ℝ) (y : Fin r → ℝ) :
    (coordinateDesign A U).mulVec y = (retainedDesign A).mulVec (U.mulVec y) := by
  exact (Matrix.mulVec_mulVec y (retainedDesign A) U).symm

/-- The reduced objective at coordinates is exactly the retained objective
at the lifted decision vector. -/
theorem coordinate_objective_eq {n d r : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin d) (Fin r) ℝ) (b : Fin n → ℝ) (y : Fin r → ℝ) :
    coordinateObjective A U b y = retainedObjective A b (U.mulVec y) := by
  unfold coordinateObjective retainedObjective
  rw [coordinate_predictions]

/-- Source objective decomposition at every lifted point. -/
theorem lifted_objective_eq {n d r : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin d) (Fin r) ℝ) (b : Fin n → ℝ) (y : Fin r → ℝ) :
    objective A b (U.mulVec y) = zeroRowCost A b + coordinateObjective A U b y := by
  rw [objective_eq_constant_add_retained, coordinate_objective_eq]

/-- A nonnegative zero-row constant preserves every relative loss factor at
least one. This also applies to the squared factor for the Huber norm objective. -/
theorem relative_guarantee_add_constant {C F G κ : ℝ}
    (hC : 0 ≤ C) (hκ : 1 ≤ κ) (hFG : F ≤ κ * G) :
    C + F ≤ κ * (C + G) := by
  have hm := mul_nonneg hC (sub_nonneg.mpr hκ)
  nlinarith

/-- An approximation on retained rows lifts with the same relative factor. -/
theorem retained_relative_guarantee {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ)
    (xhat xstar : Fin d → ℝ) {κ : ℝ} (hκ : 1 ≤ κ)
    (hret : retainedObjective A b xhat ≤ κ * retainedObjective A b xstar) :
    objective A b xhat ≤ κ * objective A b xstar := by
  rw [objective_eq_constant_add_retained, objective_eq_constant_add_retained]
  exact relative_guarantee_add_constant (zeroRowCost_nonneg A b) hκ hret

/-- The source Huber norm guarantee survives removal of the zero rows. -/
theorem retained_sqrt_relative_guarantee {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ)
    (xhat xstar : Fin d → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hret : retainedObjective A b xhat ≤ (1 + ε) ^ 2 * retainedObjective A b xstar) :
    Real.sqrt (objective A b xhat) ≤ (1 + ε) * Real.sqrt (objective A b xstar) := by
  have hκ : 1 ≤ (1 + ε) ^ 2 := by nlinarith
  have hrel := retained_relative_guarantee A b xhat xstar hκ hret
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  have hnonneg : 0 ≤ objective A b xhat :=
    Finset.sum_nonneg (fun _ _ => huber_nonneg _)
  have hnonneg' : 0 ≤ objective A b xstar :=
    Finset.sum_nonneg (fun _ _ => huber_nonneg _)
  rwa [Real.sq_sqrt hnonneg, mul_pow, Real.sq_sqrt hnonneg']

/-- With an identically zero design, every point has the same objective.
Thus the fixed output zero requires no information about the labels. -/
theorem zero_design_optimizer {n d : ℕ} (b : Fin n → ℝ) :
    ∀ x : Fin d → ℝ, objective (0 : Matrix (Fin n) (Fin d) ℝ) b 0 ≤
      objective (0 : Matrix (Fin n) (Fin d) ℝ) b x := by
  intro x
  simp [objective]

/-- Rank zero forces every entry of the design to vanish. -/
theorem design_zero_of_rank_zero {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (hrank : A.rank = 0) : A = 0 := by
  have hrange : LinearMap.range A.mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp hrank
  have hx : ∀ x : Fin d → ℝ, A.mulVec x = 0 := by
    intro x
    have hm : A.mulVec x ∈ LinearMap.range A.mulVecLin := ⟨x, rfl⟩
    rw [hrange] at hm
    exact hm
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [hx, Matrix.zero_mulVec]

/-- The rank-zero branch has the fixed optimizer zero for every label vector. -/
theorem rank_zero_optimizer {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (hrank : A.rank = 0) (b : Fin n → ℝ) :
    ∀ x : Fin d → ℝ, objective A b 0 ≤ objective A b x := by
  rw [design_zero_of_rank_zero A hrank]
  exact zero_design_optimizer b

/-- Deleting zero rows preserves equality of prediction vectors exactly. -/
theorem retained_predictions_eq_iff {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (x y : Fin d → ℝ) :
    (retainedDesign A).mulVec x = (retainedDesign A).mulVec y ↔
      A.mulVec x = A.mulVec y := by
  constructor
  · intro h
    funext i
    by_cases hi : A i = 0
    · rw [zero_row_prediction A x ⟨i, hi⟩, zero_row_prediction A y ⟨i, hi⟩]
    · exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact congrFun h i.val

/-- Exact algebraic coordinates of dimension `rank A` exist. This construction
uses a basis of the actual image and a linear section of the actual matrix map;
prediction equivalence is proved, not supplied as a factorization assumption.
Orthonormality of the lifting columns is not asserted by this algebraic lemma. -/
theorem exists_rank_coordinates {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    ∃ U : Matrix (Fin d) (Fin A.rank) ℝ,
      Function.Injective (A * U).mulVec ∧
        ∀ x : Fin d → ℝ, ∃ y : Fin A.rank → ℝ, (A * U).mulVec y = A.mulVec x := by
  classical
  let f := A.mulVecLin
  let B := Module.finBasis ℝ (LinearMap.range f)
  obtain ⟨g, hg⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  let L : (Fin A.rank → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
    g.comp B.equivFun.symm.toLinearMap
  let U : Matrix (Fin d) (Fin A.rank) ℝ := LinearMap.toMatrix' L
  have hmap : ∀ y : Fin A.rank → ℝ,
      (A * U).mulVec y = (B.equivFun.symm y).val := by
    intro y
    rw [← Matrix.mulVec_mulVec]
    change A.mulVec ((LinearMap.toMatrix' L).mulVec y) = _
    rw [LinearMap.toMatrix'_mulVec]
    exact congrArg Subtype.val (LinearMap.congr_fun hg (B.equivFun.symm y))
  refine ⟨U, ?_, ?_⟩
  · intro y z hyz
    apply B.equivFun.symm.injective
    apply Subtype.ext
    rw [← hmap y, ← hmap z]
    exact hyz
  · intro x
    let q : LinearMap.range f := ⟨A.mulVec x, x, rfl⟩
    refine ⟨B.equivFun q, ?_⟩
    rw [hmap, B.equivFun.symm_apply_apply]

/-- Full-column-rank coordinates remain injective after zero rows are deleted. -/
theorem coordinate_injective_of_full_injective {n d r : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (U : Matrix (Fin d) (Fin r) ℝ)
    (hinj : Function.Injective (A * U).mulVec) :
    Function.Injective (coordinateDesign A U).mulVec := by
  intro y z hyz
  apply hinj
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  apply (retained_predictions_eq_iff A _ _).mp
  simpa only [coordinate_predictions] using hyz

/-- A coordinate map spanning all predictions cannot create a zero retained row. -/
theorem coordinate_row_nonzero {n d r : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (U : Matrix (Fin d) (Fin r) ℝ)
    (hcover : ∀ x : Fin d → ℝ, ∃ y : Fin r → ℝ, (A * U).mulVec y = A.mulVec x)
    (i : RetainedRows A) : coordinateDesign A U i ≠ 0 := by
  intro hzero
  apply i.property
  funext j
  obtain ⟨y, hy⟩ := hcover (Pi.single j 1)
  have hrow : (A * U) i.val = 0 := hzero
  have hpred : ((A * U).mulVec y) i.val = 0 := by
    change dotProduct ((A * U) i.val) y = 0
    rw [hrow]
    simp [dotProduct]
  have he := congrFun hy i.val
  rw [Matrix.mulVec_single_one] at he
  exact he.symm.trans hpred

/-- The actual retained coordinate design has exactly `rank A` independent
columns and has no zero row. The remaining geometric refinement is to choose
an orthonormal basis of the kernel's orthogonal complement. -/
theorem exists_full_rank_retained_coordinates {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) :
    ∃ U : Matrix (Fin d) (Fin A.rank) ℝ,
      (coordinateDesign A U).rank = A.rank ∧
      (∀ i : RetainedRows A, coordinateDesign A U i ≠ 0) ∧
      ∀ x : Fin d → ℝ, ∃ y : Fin A.rank → ℝ, (A * U).mulVec y = A.mulVec x := by
  obtain ⟨U, hinj, hcover⟩ := exists_rank_coordinates A
  refine ⟨U, ?_, coordinate_row_nonzero A U hcover, hcover⟩
  have hi := coordinate_injective_of_full_injective A U hinj
  change Module.finrank ℝ (LinearMap.range (coordinateDesign A U).mulVecLin) = A.rank
  rw [LinearMap.finrank_range_of_inj hi]
  simp

/-- Prediction coverage gives exact coverage of all retained objective values. -/
theorem coordinate_objective_covers {n d r : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (U : Matrix (Fin d) (Fin r) ℝ)
    (b : Fin n → ℝ)
    (hcover : ∀ x : Fin d → ℝ, ∃ y : Fin r → ℝ, (A * U).mulVec y = A.mulVec x)
    (x : Fin d → ℝ) :
    ∃ y : Fin r → ℝ, coordinateObjective A U b y = retainedObjective A b x := by
  obtain ⟨y, hy⟩ := hcover x
  refine ⟨y, ?_⟩
  rw [coordinate_objective_eq]
  have hp : A.mulVec (U.mulVec y) = A.mulVec x := by
    rw [Matrix.mulVec_mulVec]
    exact hy
  unfold retainedObjective
  simp only [retained_prediction, hp]

/-- A minimizer in prediction-spanning coordinates is a minimizer for the
original arbitrary design, including its zero-row constant. -/
theorem coordinate_minimizer_lifts {n d r : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (U : Matrix (Fin d) (Fin r) ℝ)
    (b : Fin n → ℝ)
    (hcover : ∀ x : Fin d → ℝ, ∃ y : Fin r → ℝ, (A * U).mulVec y = A.mulVec x)
    (ystar : Fin r → ℝ)
    (hmin : ∀ y, coordinateObjective A U b ystar ≤ coordinateObjective A U b y) :
    ∀ x : Fin d → ℝ, objective A b (U.mulVec ystar) ≤ objective A b x := by
  intro x
  obtain ⟨y, hy⟩ := coordinate_objective_covers A U b hcover x
  rw [lifted_objective_eq, objective_eq_constant_add_retained]
  apply add_le_add_left
  rw [← hy]
  exact hmin y

/-- An approximation in prediction-spanning coordinates lifts to every
original comparator with exactly the same relative factor. -/
theorem coordinate_relative_guarantee {n d r : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (U : Matrix (Fin d) (Fin r) ℝ)
    (b : Fin n → ℝ)
    (hcover : ∀ x : Fin d → ℝ, ∃ y : Fin r → ℝ, (A * U).mulVec y = A.mulVec x)
    (yhat : Fin r → ℝ) {κ : ℝ} (hκ : 1 ≤ κ)
    (happrox : ∀ y, coordinateObjective A U b yhat ≤ κ * coordinateObjective A U b y) :
    ∀ x : Fin d → ℝ, objective A b (U.mulVec yhat) ≤ κ * objective A b x := by
  intro x
  obtain ⟨y, hy⟩ := coordinate_objective_covers A U b hcover x
  apply retained_relative_guarantee A b (U.mulVec yhat) x hκ
  rw [← coordinate_objective_eq, ← hy]
  exact happrox y

end Paper29.Reduction
