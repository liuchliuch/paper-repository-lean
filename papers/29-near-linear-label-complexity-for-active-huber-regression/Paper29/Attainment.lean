import Paper29.Localization
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact

/-!
# Attainment and the deterministic minimum Euclidean norm selection (Appendix A.3)

Zero-weight observations are replaced by zero rows and zero labels with unit
weight. The objective then factors through the finite-dimensional row image.
Bounded sublevels on this image give attainment even when the original matrix
has a kernel. Projection onto the closed convex argmin gives the unique
minimum Euclidean norm minimizer.
-/
noncomputable section
open scoped BigOperators

namespace Paper29.Attainment

/-- Weighted affine Huber regression, including zero weights. -/
def affineHuber {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w b : Fin n → ℝ) (x : Fin d → ℝ) : ℝ :=
  weightedHuber w (fun i => (A.mulVec x) i - b i)

/-- The response-space objective before restriction to the row image. -/
def responseHuber {ι : Type*} [Fintype ι] (w b y : ι → ℝ) : ℝ :=
  weightedHuber w (fun i => y i - b i)

theorem continuous_responseHuber {ι : Type*} [Fintype ι] (w b : ι → ℝ) :
    Continuous (responseHuber w b) := by
  unfold responseHuber weightedHuber
  apply continuous_finset_sum
  intro i hi
  exact continuous_const.mul (Paper29.continuous_huber.comp
    ((continuous_apply i).sub continuous_const))

theorem responseHuber_nonneg {ι : Type*} [Fintype ι] (w b y : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) : 0 ≤ responseHuber w b y :=
  weightedHuber_nonneg _ _ hw

/-- The source coercivity estimate, coordinate by coordinate. No injectivity
or coercivity hypothesis is needed. -/
theorem response_coordinate_bound {ι : Type*} [Fintype ι] (w b y : ι → ℝ)
    (hw : ∀ i, 0 < w i) {B : ℝ} (hy : responseHuber w b y ≤ B) (i : ι) :
    |y i| ≤ B / w i + |b i| + 1 / 2 := by
  have hterm : w i * huber (y i - b i) ≤ responseHuber w b y := by
    apply Finset.single_le_sum (fun j _ => mul_nonneg (hw j).le (huber_nonneg _))
    exact Finset.mem_univ i
  have hlower := mul_le_mul_of_nonneg_left (abs_sub_half_le_huber (y i - b i))
    (hw i).le
  have hres : |y i - b i| ≤ B / w i + 1 / 2 := by
    have hh : |y i - b i| - 1 / 2 ≤ B / w i :=
      (le_div_iff₀ (hw i)).2 (by nlinarith)
    linarith
  have habs : |y i| ≤ |y i - b i| + |b i| := by
    simpa only [sub_add_cancel] using abs_add_le (y i - b i) (b i)
  linarith

/-- Every sublevel of the response objective with positive weights is bounded,
including the empty row space. -/
theorem response_sublevel_isBounded {ι : Type*} [Fintype ι] (w b : ι → ℝ)
    (hw : ∀ i, 0 < w i) {B : ℝ} (hB : 0 ≤ B) :
    Bornology.IsBounded {y : ι → ℝ | responseHuber w b y ≤ B} := by
  classical
  let R : ℝ := ∑ i, (B / w i + |b i| + 1 / 2)
  have hterm0 (i : ι) : 0 ≤ B / w i + |b i| + 1 / 2 := by
    have hwi : 0 ≤ w i := (hw i).le
    positivity
  have hR : 0 ≤ R := Finset.sum_nonneg fun i _ => hterm0 i
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨R, ?_⟩
  intro y hy
  apply (pi_norm_le_iff_of_nonneg hR).2
  intro i
  rw [Real.norm_eq_abs]
  exact (response_coordinate_bound w b y hw hy i).trans
    (Finset.single_le_sum (fun j _ => hterm0 j) (Finset.mem_univ i))

/-- A positive-weight Huber objective attains its infimum on every linear row
image. Finite dimensionality supplies properness of the image subtype. -/
theorem response_attains_on_submodule {ι : Type*} [Fintype ι] (w b : ι → ℝ)
    (hw : ∀ i, 0 < w i) (V : Submodule ℝ (ι → ℝ)) :
    ∃ y : V, ∀ z : V, responseHuber w b y ≤ responseHuber w b z := by
  let F : V → ℝ := fun y => responseHuber w b y
  have hc : Continuous F := (continuous_responseHuber w b).comp continuous_subtype_val
  apply hc.exists_forall_le_of_isBounded (0 : V)
  have hB : 0 ≤ responseHuber w b (0 : ι → ℝ) :=
    responseHuber_nonneg w b 0 (fun i => (hw i).le)
  have hb := response_sublevel_isBounded w b hw hB
  have : Bornology.IsBounded ((Subtype.val : V → (ι → ℝ)) '' {y : V | F y ≤ F 0}) :=
    hb.subset (by rintro _ ⟨y, hy, rfl⟩; exact hy)
  apply isBounded_iff_forall_norm_le.mpr
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp this
  exact ⟨R, fun y hy => hR y ⟨y, hy, rfl⟩⟩

/-- Arbitrary nonnegative-weight affine Huber regression attains its infimum.
The zero weights, zero matrix, empty sample and rank-deficient cases are all
included in this statement. -/
theorem affineHuber_attains {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w b : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∃ x : Fin d → ℝ, ∀ y : Fin d → ℝ, affineHuber A w b x ≤ affineHuber A w b y := by
  classical
  let v : Fin n → ℝ := fun i => if w i = 0 then 1 else w i
  let C : Matrix (Fin n) (Fin d) ℝ := fun i j => if w i = 0 then 0 else A i j
  let c : Fin n → ℝ := fun i => if w i = 0 then 0 else b i
  have hv : ∀ i, 0 < v i := by
    intro i
    dsimp [v]
    split_ifs with hi
    · norm_num
    · exact lt_of_le_of_ne (hw i) (Ne.symm hi)
  have heq (x : Fin d → ℝ) : responseHuber v c (C.mulVec x) = affineHuber A w b x := by
    unfold responseHuber affineHuber weightedHuber
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hwi : w i = 0
    · simp [v, C, c, hwi, Matrix.mulVec, dotProduct]
    · simp [v, C, c, hwi, Matrix.mulVec, dotProduct]
  let L := C.mulVecLin
  obtain ⟨z, hz⟩ := response_attains_on_submodule v c hv (LinearMap.range L)
  obtain ⟨x, hx⟩ := z.property
  refine ⟨x, ?_⟩
  intro y
  rw [← heq x, ← heq y]
  have h := hz ⟨L y, ⟨y, rfl⟩⟩
  simpa only [← hx] using h

theorem continuous_affineHuber {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w b : Fin n → ℝ) : Continuous (affineHuber A w b) :=
  (continuous_responseHuber w b).comp A.mulVecLin.continuous_of_finiteDimensional

/-- The same actual matrix objective on Euclidean coordinates. -/
def euclideanHuber {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w b : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  affineHuber A w b (WithLp.ofLp x)

theorem continuous_euclideanHuber {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w b : Fin n → ℝ) : Continuous (euclideanHuber A w b) :=
  (continuous_affineHuber A w b).comp (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ))

theorem convex_euclideanHuber {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w b : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ConvexOn ℝ Set.univ (euclideanHuber A w b) := by
  have h := (Localization.convex_shifted A w (fun i => -b i) hw).comp_linearMap
    (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap
  simpa [euclideanHuber, affineHuber, Localization.shifted, sub_eq_add_neg] using h

/-- The closed convex set of global minimizers of the actual sampled loss. -/
def minimizers {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (w b : Fin n → ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ y, euclideanHuber A w b x ≤ euclideanHuber A w b y}

theorem minimizers_nonempty {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w b : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) : (minimizers A w b).Nonempty := by
  obtain ⟨x, hx⟩ := affineHuber_attains A w b hw
  refine ⟨WithLp.toLp 2 x, ?_⟩
  intro y
  exact hx (WithLp.ofLp y)

theorem minimizers_isClosed {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w b : Fin n → ℝ) : IsClosed (minimizers A w b) := by
  have heq : minimizers A w b = ⋂ y, {x | euclideanHuber A w b x ≤ euclideanHuber A w b y} := by
    ext x
    simp [minimizers]
  rw [heq]
  apply isClosed_iInter
  intro y
  exact isClosed_le (continuous_euclideanHuber A w b) continuous_const

theorem minimizers_convex {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w b : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) : Convex ℝ (minimizers A w b) := by
  obtain ⟨m, hm⟩ := minimizers_nonempty A w b hw
  have heq : minimizers A w b = {x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin d))) |
      euclideanHuber A w b x ≤ euclideanHuber A w b m} := by
    ext x
    constructor
    · intro hx
      exact ⟨Set.mem_univ _, hx m⟩
    · rintro ⟨_, hx⟩ y
      exact hx.trans (hm y)
  rw [heq]
  exact (convex_euclideanHuber A w b hw).convex_le _

/-- The Hilbert projection of zero onto the argmin is the unique global
minimizer of smallest Euclidean norm. There is no rank or coercivity hypothesis. -/
theorem exists_unique_minimum_norm {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w b : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∃! x : EuclideanSpace ℝ (Fin d),
      x ∈ minimizers A w b ∧ ∀ y ∈ minimizers A w b, ‖x‖ ≤ ‖y‖ := by
  let K := minimizers A w b
  have hne : K.Nonempty := minimizers_nonempty A w b hw
  have hc : IsClosed K := minimizers_isClosed A w b
  have hv : Convex ℝ K := minimizers_convex A w b hw
  obtain ⟨v, hvmem, hvnorm⟩ := exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hv 0
  simp only [zero_sub, norm_neg] at hvnorm
  have hb : BddBelow (Set.range (fun y : K => ‖(y : EuclideanSpace ℝ (Fin d))‖)) := by
    refine ⟨0, ?_⟩
    rintro r ⟨y, rfl⟩
    exact norm_nonneg _
  have hn (y) (hy : y ∈ K) : ‖v‖ ≤ ‖y‖ := by
    rw [hvnorm]
    exact ciInf_le hb ⟨y, hy⟩
  refine ⟨v, ⟨hvmem, hn⟩, ?_⟩
  intro u hu
  have heqnorm : ‖u‖ = ‖v‖ := le_antisymm (hu.2 v hvmem) (hn u hu.1)
  have hmid : (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • u ∈ K :=
    hv hvmem hu.1 (by norm_num) (by norm_num) (by norm_num)
  have hm := hn _ hmid
  rw [← smul_add, norm_smul] at hm
  norm_num at hm
  have hsq := mul_self_le_mul_self (norm_nonneg v) hm
  have hp := parallelogram_law_with_norm ℝ v u
  rw [heqnorm] at hp
  have hzero_sq : ‖v - u‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖v - u‖]
  have hzero : ‖v - u‖ = 0 := sq_eq_zero_iff.mp hzero_sq
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm

/-- The deterministic minimum-norm rule used by both batches. -/
def minimumNormSelection {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w b : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) : EuclideanSpace ℝ (Fin d) :=
  (exists_unique_minimum_norm A w b hw).choose

theorem minimumNormSelection_spec {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w b : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    minimumNormSelection A w b hw ∈ minimizers A w b ∧
      ∀ y ∈ minimizers A w b, ‖minimumNormSelection A w b hw‖ ≤ ‖y‖ :=
  (exists_unique_minimum_norm A w b hw).choose_spec.1

/-- The selection rule in the coordinate form used by the zero-optimum branch. -/
theorem minimumNormSelection_sum_sq_le {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (w b : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ minimizers A w b) :
    (∑ j, (minimumNormSelection A w b hw j) ^ 2) ≤ ∑ j, (y j) ^ 2 := by
  have hn := (minimumNormSelection_spec A w b hw).2 y hy
  have hs := mul_self_le_mul_self (norm_nonneg _) hn
  simpa only [← sq, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs] using hs

/-- Changing labels of zero-weight rows cannot change the observed objective. -/
theorem affineHuber_eq_of_observed_labels_eq {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (w b c : Fin n → ℝ)
    (hbc : ∀ i, w i ≠ 0 → b i = c i) (x : Fin d → ℝ) :
    affineHuber A w b x = affineHuber A w c x := by
  unfold affineHuber weightedHuber
  apply Finset.sum_congr rfl
  intro i hi
  change w i * huber ((A.mulVec x) i - b i) = w i * huber ((A.mulVec x) i - c i)
  by_cases hw : w i = 0
  · simp [hw]
  · rw [hbc i hw]

/-- The unique selection depends only on the design, the sampled weights,
and the observed labels. In particular any other batch is absent from its
arguments and zero-weight labels cannot influence the result. -/
theorem minimumNormSelection_observed_labels_only {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (w b c : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hbc : ∀ i, w i ≠ 0 → b i = c i) :
    minimumNormSelection A w b hw = minimumNormSelection A w c hw := by
  have hfun : euclideanHuber A w b = euclideanHuber A w c :=
    funext fun x => affineHuber_eq_of_observed_labels_eq A w b c hbc (WithLp.ofLp x)
  have hset : minimizers A w b = minimizers A w c := by
    simp only [minimizers, hfun]
  have hs := minimumNormSelection_spec A w b hw
  have hs' : minimumNormSelection A w b hw ∈ minimizers A w c ∧
      ∀ y ∈ minimizers A w c, ‖minimumNormSelection A w b hw‖ ≤ ‖y‖ := by
    simpa only [hset] using hs
  exact (exists_unique_minimum_norm A w c hw).choose_spec.2 _ hs'

end Paper29.Attainment
