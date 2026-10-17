import Paper15.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Matrix.Mul
import Mathlib.Logic.Function.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Monoid

/-!
# Lemma 4: ternary optimizing reduction

This module formalizes the compactness and linear-programming ingredients of
Lemma 4 of *An exact classical threshold in the binary triangle network*:

* a kernel direction for more than three support points under three linear
  equality constraints (normalization and the two vanishing-moment conditions);
* the resulting extreme-point bound `support ≤ 3` for the feasible polytope;
* continuity of `detMoments` in the three source laws;
* existence of a constrained global maximizer of `M₂` among deterministic
  ternary models (`lemma4_ternary_reduction`).
-/

noncomputable section

namespace Paper15

open Finset Real BigOperators Matrix Function Topology

/-! ## Probability vectors on `Fin n` -/

/-- Probability vectors on `Fin n`. -/
structure ProbVec (n : ℕ) where
  v : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ v i
  sum_eq : ∑ i, v i = 1

namespace ProbVec

variable {n : ℕ}

instance : CoeFun (ProbVec n) (fun _ => Fin n → ℝ) := ⟨fun s => s.v⟩

@[simp] lemma coe_apply (s : ProbVec n) (i : Fin n) : s i = s.v i := rfl

lemma apply_nonneg (s : ProbVec n) (i : Fin n) : 0 ≤ s i := s.nonneg i

lemma sum_apply (s : ProbVec n) : ∑ i, s i = 1 := s.sum_eq

lemma toVec_mem_stdSimplex (s : ProbVec n) : s.v ∈ stdSimplex ℝ (Fin n) :=
  ⟨s.nonneg, s.sum_eq⟩

/-- A probability vector from membership in the standard simplex. -/
def ofStdSimplex {x : Fin n → ℝ} (hx : x ∈ stdSimplex ℝ (Fin n)) : ProbVec n where
  v := x
  nonneg := hx.1
  sum_eq := hx.2

end ProbVec

/-! ## LP kernel lemma (pure linear algebra)

Three equality constraints (normalization plus two linear conditions) admit a
nonzero kernel direction as soon as a support carries more than three points.
-/

/-- If a support has more than three points, the columns of a `3 × n` matrix on
that support are linearly dependent over `ℝ`: there is a nonzero vector
supported on `s` in the kernel of `A`. -/
theorem exists_kernel_vec
    {n : ℕ} (A : Matrix (Fin 3) (Fin n) ℝ) (s : Finset (Fin n))
    (hs : 3 < s.card) :
    ∃ d : Fin n → ℝ, d ≠ 0 ∧ (∀ i, i ∉ s → d i = 0) ∧ A *ᵥ d = 0 := by
  classical
  let v : s → (Fin 3 → ℝ) := fun i r => A r i.val
  have hlt : 3 < Fintype.card s := by
    rwa [Fintype.card_coe]
  have hrank : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by simp
  have hdep : ¬ LinearIndependent ℝ v := by
    intro hli
    have hle : Fintype.card s ≤ Module.finrank ℝ (Fin 3 → ℝ) :=
      hli.fintype_card_le_finrank
    rw [hrank] at hle
    omega
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
  set d : Fin n → ℝ := Subtype.val.extend g 0 with hd
  refine ⟨d, ?_, ?_, ?_⟩
  · have hdi : d i.val = g i := by
      rw [hd]
      exact Subtype.val_injective.extend_apply g 0 i
    intro hzero
    apply hi
    rw [← hdi, hzero]
    simp
  · intro k hk
    rw [hd]
    have hnr : ¬∃ a : s, (a : Fin n) = k := by
      rintro ⟨a, ha⟩
      exact hk (ha ▸ a.prop)
    exact extend_apply' (f := (Subtype.val : s → Fin n)) g (0 : Fin n → ℝ) k hnr
  · ext r
    simp only [mulVec, dotProduct]
    have hrestrict : (∑ k : Fin n, A r k * d k) = ∑ k : s, g k * A r k.val := by
      rw [hd]
      conv_lhs =>
        rw [← sum_add_sum_compl (s : Finset (Fin n))]
      have hcompl : (∑ k ∈ (s : Finset (Fin n))ᶜ,
          A r k * Subtype.val.extend g (0 : Fin n → ℝ) k) = 0 := by
        refine sum_eq_zero ?_
        intro k hk
        have hkns : k ∉ s := by simpa using hk
        have hnr : ¬∃ a : s, (a : Fin n) = k := by
          rintro ⟨a, ha⟩
          exact hkns (ha ▸ a.prop)
        rw [extend_apply' (f := (Subtype.val : s → Fin n)) g (0 : Fin n → ℝ) k hnr,
          Pi.zero_apply]
        ring
      rw [hcompl, add_zero]
      have hsEq : (∑ k ∈ (s : Finset (Fin n)),
          A r k * Subtype.val.extend g (0 : Fin n → ℝ) k)
          = ∑ k : s, g k * A r k.val := by
        rw [← sum_attach]
        refine sum_congr rfl ?_
        intro k _
        rw [Subtype.val_injective.extend_apply g (0 : Fin n → ℝ) k]
        ring
      rw [hsEq]
    rw [hrestrict]
    have key : ∑ k : s, g k * A r k.val = (∑ k : s, g k • v k) r := by
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, v]
    rw [key]
    exact congrFun hg r

/-- If a support has more than three points, there is a nonzero direction
supported on `s` which is annihilated by a `2 × n` constraint matrix *and*
has zero coordinate sum (the three equality rows of the LP). -/
theorem exists_kernel_vec_sum_zero
    {n : ℕ} (A : Matrix (Fin 2) (Fin n) ℝ) (s : Finset (Fin n))
    (hs : 3 < s.card) :
    ∃ d : Fin n → ℝ, d ≠ 0 ∧ (∀ i, i ∉ s → d i = 0) ∧
      A *ᵥ d = 0 ∧ ∑ i, d i = 0 := by
  classical
  -- Embed the two rows of `A` and the all-ones row into a `3 × n` matrix.
  let A3 : Matrix (Fin 3) (Fin n) ℝ := fun r i =>
    if r = 0 then A 0 i else if r = 1 then A 1 i else 1
  obtain ⟨d, hd0, hsup, hker⟩ := exists_kernel_vec A3 s hs
  refine ⟨d, hd0, hsup, ?_, ?_⟩
  · have key0 : (A3 *ᵥ d) 0 = (A *ᵥ d) 0 := by
      simp only [mulVec, dotProduct, A3]
      refine Finset.sum_congr rfl ?_
      intro i _
      simp only [if_true]
    have key1 : (A3 *ᵥ d) 1 = (A *ᵥ d) 1 := by
      simp only [mulVec, dotProduct, A3]
      refine Finset.sum_congr rfl ?_
      intro i _
      have h10 : (1 : Fin 3) ≠ 0 := by decide
      simp only [if_neg h10, if_true]
    ext r
    rcases r with ⟨r, hr⟩
    interval_cases r
    · have := congrFun hker 0
      rw [key0] at this
      simpa using this
    · have := congrFun hker 1
      rw [key1] at this
      simpa using this
  · have key2 : (A3 *ᵥ d) 2 = ∑ i, d i := by
      simp only [mulVec, dotProduct, A3]
      refine Finset.sum_congr rfl ?_
      intro i _
      have h20 : (2 : Fin 3) ≠ 0 := by decide
      have h21 : (2 : Fin 3) ≠ 1 := by decide
      simp only [if_neg h20, if_neg h21, one_mul]
    have h := congrFun hker 2
    rw [key2] at h
    exact h

/-! ## Extreme points of the probability polytope with 3 equalities

Feasible set: `{x | x ≥ 0, A x = b, ∑ x = 1}` for `A : Matrix (Fin 2) (Fin n) ℝ`.
A feasible point is *extreme* when it is not the midpoint of two distinct
feasible points.  Extreme points have support of size at most three.
-/

/-- Feasibility of `x` for the polytope `{x | x ≥ 0, A x = b, ∑ x = 1}`. -/
def LPFeasible {n : ℕ} (A : Matrix (Fin 2) (Fin n) ℝ) (b : Fin 2 → ℝ)
    (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ A *ᵥ x = b ∧ ∑ i, x i = 1

/-- Extremality: `x` is not the midpoint of two distinct feasible points. -/
def IsLPExtreme {n : ℕ} (A : Matrix (Fin 2) (Fin n) ℝ) (b : Fin 2 → ℝ)
    (x : Fin n → ℝ) : Prop :=
  LPFeasible A b x ∧
    ∀ y z, LPFeasible A b y → LPFeasible A b z →
      x = (y + z) / 2 → y = z

/-- Direction feasibility: `x + ε • d` keeps the two linear equalities. -/
lemma LPFeasible.dir_eq {n : ℕ} {A : Matrix (Fin 2) (Fin n) ℝ} {b : Fin 2 → ℝ}
    {x d : Fin n → ℝ} (hx : LPFeasible A b x)
    (hd : A *ᵥ d = 0) (hdsum : ∑ i, d i = 0) (ε : ℝ) :
    A *ᵥ (x + ε • d) = b ∧ ∑ i, (x + ε • d) i = 1 := by
  constructor
  · have h1 : A *ᵥ (x + ε • d) = A *ᵥ x + ε • (A *ᵥ d) := by
      rw [mulVec_add]
      have : A *ᵥ (ε • d) = ε • (A *ᵥ d) := by
        rw [mulVec_smul]
      rw [this]
    rw [h1, hd, smul_zero, add_zero, hx.2.1]
  · have h2 : ∑ i, (x + ε • d) i = ∑ i, x i + ε * ∑ i, d i := by
      have hsum : ∑ i, (x + ε • d) i = ∑ i, (x i + ε * d i) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hsum, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [h2, hx.2.2, hdsum, mul_zero, add_zero]

/-- An extreme point of the polytope `{x ≥ 0 | A x = b, ∑ x = 1}` has support of
size at most three.  This is the kernel argument of Lemma 4: a support of size
greater than three admits a nonzero direction in the kernel of the three
constraint rows, and both small positive and negative perturbations remain
feasible, contradicting extremality. -/
theorem isLPExtreme_support_le
    {n : ℕ} (A : Matrix (Fin 2) (Fin n) ℝ) (b : Fin 2 → ℝ) {x : Fin n → ℝ}
    (h : IsLPExtreme A b x) :
    {i | 0 < x i}.toFinset.card ≤ 3 := by
  classical
  by_contra hcard
  push_neg at hcard
  let s : Finset (Fin n) := {i | 0 < x i}.toFinset
  have hmem : ∀ i, i ∈ s ↔ 0 < x i := by
    intro i
    simp only [s, Set.mem_toFinset, Set.mem_setOf_eq]
  have hs : 3 < s.card := by simpa only [s] using hcard
  obtain ⟨d, hd0, hsup, hker, hsum⟩ := exists_kernel_vec_sum_zero A s hs
  have hds : ∀ i, d i ≠ 0 → i ∈ s := by
    intro i hi
    by_contra hnot
    exact hi (hsup i hnot)
  have hex : ∃ i, d i ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hd0
    ext i
    exact hnone i
  obtain ⟨i0, hi0⟩ := hex
  have hi0s : i0 ∈ s := hds i0 hi0
  let ratios : Finset (Fin n) := s.filter (fun i => d i ≠ 0)
  have hrat : ∀ i ∈ ratios, 0 < x i / |d i| := by
    intro i hi
    simp only [ratios, Finset.mem_filter] at hi
    exact div_pos ((hmem i).mp hi.1) (abs_pos.mpr hi.2)
  obtain ⟨iStar, hiStar, hmin⟩ :=
    Finset.exists_min_image ratios (fun i => x i / |d i|)
      ⟨i0, by simp only [ratios, Finset.mem_filter]; exact ⟨hi0s, hi0⟩⟩
  have hiStarpos : 0 < x iStar / |d iStar| := hrat iStar hiStar
  set ε : ℝ := (x iStar / |d iStar|) / 2 with hε
  have hεpos : 0 < ε := half_pos hiStarpos
  have hstep : ∀ i, ε * |d i| ≤ x i := by
    intro i
    by_cases hdi : d i = 0
    · rw [hdi, abs_zero, mul_zero]
      exact h.1.1 i
    · have hi : i ∈ ratios := by
        simp only [ratios, Finset.mem_filter]
        exact ⟨hds i hdi, hdi⟩
      have hmi : x iStar / |d iStar| ≤ x i / |d i| := hmin i hi
      have hεeq : ε * |d i| = (x iStar / |d iStar|) * |d i| / 2 := by
        rw [hε]
        calc (x iStar / |d iStar| / 2) * |d i|
            = (x iStar / |d iStar|) * |d i| / 2 := by ring
          _ = (x iStar / |d iStar|) * |d i| / 2 := rfl
      rw [hεeq]
      have hcalc : (x iStar / |d iStar|) * |d i| / 2 ≤ x i / 2 := by
        rw [div_le_div_iff_of_pos_right two_pos]
        have hmul := mul_le_mul_of_nonneg_right hmi (abs_nonneg (d i))
        have hright : (x i / |d i|) * |d i| = x i :=
          div_mul_cancel₀ _ (abs_ne_zero.mpr hdi)
        rw [hright] at hmul
        exact hmul
      exact hcalc.trans (half_le_self (h.1.1 i))
  have hnonneg_add : ∀ i, 0 ≤ x i + ε * d i := by
    intro i
    have hst := hstep i
    by_cases hdi : d i = 0
    · rw [hdi, mul_zero, add_zero]
      exact h.1.1 i
    · by_cases hpos : 0 ≤ d i
      · nlinarith [h.1.1 i, hεpos, hpos]
      · have hneg : d i < 0 := lt_of_not_ge hpos
        have habs : |d i| = - d i := abs_of_neg hneg
        have hcalc : x i + ε * d i = x i - ε * |d i| := by
          rw [habs]
          ring
        rw [hcalc]
        linarith
  have hnonneg_sub : ∀ i, 0 ≤ x i - ε * d i := by
    intro i
    have hst := hstep i
    by_cases hdi : d i = 0
    · rw [hdi, mul_zero, sub_zero]
      exact h.1.1 i
    · by_cases hpos : 0 ≤ d i
      · have habs : |d i| = d i := abs_of_nonneg hpos
        have hcalc : x i - ε * d i = x i - ε * |d i| := by
          rw [habs]
        rw [hcalc]
        linarith
      · have hneg : d i < 0 := lt_of_not_ge hpos
        have habs : |d i| = - d i := abs_of_neg hneg
        have hcalc : x i - ε * d i = x i + ε * |d i| := by
          rw [habs]
          ring
        rw [hcalc]
        nlinarith [h.1.1 i, hεpos, hneg]
  -- Two feasible points.
  set y : Fin n → ℝ := x + ε • d with hy0
  set z : Fin n → ℝ := x - ε • d with hz0
  have hy : LPFeasible A b y := by
    refine ⟨hnonneg_add, ?_, ?_⟩
    · rw [hy0]
      exact (LPFeasible.dir_eq h.1 hker hsum ε).1
    · rw [hy0]
      exact (LPFeasible.dir_eq h.1 hker hsum ε).2
  have hz : LPFeasible A b z := by
    refine ⟨hnonneg_sub, ?_, ?_⟩
    · have hdir := LPFeasible.dir_eq h.1 hker hsum (-ε)
      have key : x + (-ε) • d = x - ε • d := by
        rw [neg_smul]
        abel
      rw [hz0, ← key]
      exact hdir.1
    · have hdir := LPFeasible.dir_eq h.1 hker hsum (-ε)
      have key : x + (-ε) • d = x - ε • d := by
        rw [neg_smul]
        abel
      rw [hz0, ← key]
      exact hdir.2
  have hmid : x = (y + z) / 2 := by
    have key : y + z = (2 : ℝ) • x := by
      rw [hy0, hz0]
      ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [key]
    ext i
    have hdiv : (((2 : ℝ) • x) / 2 : Fin n → ℝ) i = (2 * x i) / 2 := by
      rw [Pi.div_apply, Pi.smul_apply, smul_eq_mul]
      simp
    rw [hdiv]
    ring
  have hyz : y = z := h.2 y z hy hz hmid
  have hcancel : (ε • d : Fin n → ℝ) = 0 := by
    have hdiff : y - z = (2 : ℝ) • (ε • d) := by
      rw [hy0, hz0]
      ext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hyz, sub_self] at hdiff
    have := hdiff.symm
    rw [smul_eq_zero] at this
    exact this.resolve_left (by norm_num)
  apply hd0
  have hεne : ε ≠ 0 := hεpos.ne'
  rw [smul_eq_zero] at hcancel
  exact hcancel.resolve_left hεne


/-! ## Continuity of finite moment maps

For a fixed deterministic response table the aggregate moments are polynomials
in the three source laws, hence continuous.
-/

/-- The triple of one-body expectations `(eA, eB, eC)` as a function of the
three source laws. -/
def detEA (T : DetTriangle) (qx qy qz : Fin 3 → ℝ) : ℝ :=
  ∑ x, ∑ y, ∑ z, qx x * qy y * qz z * T.A y z

/-- One-body expectation of `B`. -/
def detEB (T : DetTriangle) (qx qy qz : Fin 3 → ℝ) : ℝ :=
  ∑ x, ∑ y, ∑ z, qx x * qy y * qz z * T.B z x

/-- One-body expectation of `C`. -/
def detEC (T : DetTriangle) (qx qy qz : Fin 3 → ℝ) : ℝ :=
  ∑ x, ∑ y, ∑ z, qx x * qy y * qz z * T.C x y

/-- Pair expectation of `AB`. -/
def detEAB (T : DetTriangle) (qx qy qz : Fin 3 → ℝ) : ℝ :=
  ∑ x, ∑ y, ∑ z, qx x * qy y * qz z * (T.A y z * T.B z x)

/-- Pair expectation of `BC`. -/
def detEBC (T : DetTriangle) (qx qy qz : Fin 3 → ℝ) : ℝ :=
  ∑ x, ∑ y, ∑ z, qx x * qy y * qz z * (T.B z x * T.C x y)

/-- Pair expectation of `CA`. -/
def detECA (T : DetTriangle) (qx qy qz : Fin 3 → ℝ) : ℝ :=
  ∑ x, ∑ y, ∑ z, qx x * qy y * qz z * (T.C x y * T.A y z)

/-- Three-body expectation of `ABC`. -/
def detEABC (T : DetTriangle) (qx qy qz : Fin 3 → ℝ) : ℝ :=
  ∑ x, ∑ y, ∑ z, qx x * qy y * qz z * (T.A y z * T.B z x * T.C x y)

lemma detMoments_eq (T : DetTriangle) (qx qy qz : Fin 3 → ℝ) :
    detMoments T qx qy qz =
      { M1 := (detEA T qx qy qz + detEB T qx qy qz + detEC T qx qy qz) / 3
        M2 := (detEAB T qx qy qz + detEBC T qx qy qz + detECA T qx qy qz) / 3
        M3 := detEABC T qx qy qz } := by
  rfl

lemma continuous_detEA (T : DetTriangle) :
    Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      detEA T p.1 p.2.1 p.2.2 := by
  have h : (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      detEA T p.1 p.2.1 p.2.2)
      = fun p =>
        ∑ x, ∑ y, ∑ z, p.1 x * p.2.1 y * p.2.2 z * T.A y z := rfl
  rw [h]
  refine continuous_finset_sum _ ?_
  intro x _
  refine continuous_finset_sum _ ?_
  intro y _
  refine continuous_finset_sum _ ?_
  intro z _
  fun_prop

lemma continuous_detEB (T : DetTriangle) :
    Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      detEB T p.1 p.2.1 p.2.2 := by
  have h : (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      detEB T p.1 p.2.1 p.2.2)
      = fun p =>
        ∑ x, ∑ y, ∑ z, p.1 x * p.2.1 y * p.2.2 z * T.B z x := rfl
  rw [h]
  refine continuous_finset_sum _ ?_
  intro x _
  refine continuous_finset_sum _ ?_
  intro y _
  refine continuous_finset_sum _ ?_
  intro z _
  fun_prop

lemma continuous_detEC (T : DetTriangle) :
    Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      detEC T p.1 p.2.1 p.2.2 := by
  have h : (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      detEC T p.1 p.2.1 p.2.2)
      = fun p =>
        ∑ x, ∑ y, ∑ z, p.1 x * p.2.1 y * p.2.2 z * T.C x y := rfl
  rw [h]
  refine continuous_finset_sum _ ?_
  intro x _
  refine continuous_finset_sum _ ?_
  intro y _
  refine continuous_finset_sum _ ?_
  intro z _
  fun_prop

lemma continuous_detEAB (T : DetTriangle) :
    Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      detEAB T p.1 p.2.1 p.2.2 := by
  have h : (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      detEAB T p.1 p.2.1 p.2.2)
      = fun p =>
        ∑ x, ∑ y, ∑ z, p.1 x * p.2.1 y * p.2.2 z * (T.A y z * T.B z x) := rfl
  rw [h]
  refine continuous_finset_sum _ ?_
  intro x _
  refine continuous_finset_sum _ ?_
  intro y _
  refine continuous_finset_sum _ ?_
  intro z _
  fun_prop

lemma continuous_detEBC (T : DetTriangle) :
    Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      detEBC T p.1 p.2.1 p.2.2 := by
  have h : (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      detEBC T p.1 p.2.1 p.2.2)
      = fun p =>
        ∑ x, ∑ y, ∑ z, p.1 x * p.2.1 y * p.2.2 z * (T.B z x * T.C x y) := rfl
  rw [h]
  refine continuous_finset_sum _ ?_
  intro x _
  refine continuous_finset_sum _ ?_
  intro y _
  refine continuous_finset_sum _ ?_
  intro z _
  fun_prop

lemma continuous_detECA (T : DetTriangle) :
    Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      detECA T p.1 p.2.1 p.2.2 := by
  have h : (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      detECA T p.1 p.2.1 p.2.2)
      = fun p =>
        ∑ x, ∑ y, ∑ z, p.1 x * p.2.1 y * p.2.2 z * (T.C x y * T.A y z) := rfl
  rw [h]
  refine continuous_finset_sum _ ?_
  intro x _
  refine continuous_finset_sum _ ?_
  intro y _
  refine continuous_finset_sum _ ?_
  intro z _
  fun_prop

lemma continuous_detEABC (T : DetTriangle) :
    Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      detEABC T p.1 p.2.1 p.2.2 := by
  have h : (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      detEABC T p.1 p.2.1 p.2.2)
      = fun p =>
        ∑ x, ∑ y, ∑ z, p.1 x * p.2.1 y * p.2.2 z * (T.A y z * T.B z x * T.C x y) := rfl
  rw [h]
  refine continuous_finset_sum _ ?_
  intro x _
  refine continuous_finset_sum _ ?_
  intro y _
  refine continuous_finset_sum _ ?_
  intro z _
  fun_prop

/-- `M1` of `detMoments` is continuous in the three source laws. -/
lemma continuous_detM1 (T : DetTriangle) :
    Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      (detMoments T p.1 p.2.1 p.2.2).M1 := by
  have h : (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      (detMoments T p.1 p.2.1 p.2.2).M1)
      = fun p =>
        (detEA T p.1 p.2.1 p.2.2 + detEB T p.1 p.2.1 p.2.2
          + detEC T p.1 p.2.1 p.2.2) / 3 := by
    ext p
    simp only [detMoments_eq]
  rw [h]
  exact ((continuous_detEA T).add (continuous_detEB T)).add
    (continuous_detEC T) |>.div_const 3

/-- `M2` of `detMoments` is continuous in the three source laws. -/
lemma continuous_detM2 (T : DetTriangle) :
    Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      (detMoments T p.1 p.2.1 p.2.2).M2 := by
  have h : (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      (detMoments T p.1 p.2.1 p.2.2).M2)
      = fun p =>
        (detEAB T p.1 p.2.1 p.2.2 + detEBC T p.1 p.2.1 p.2.2
          + detECA T p.1 p.2.1 p.2.2) / 3 := by
    ext p
    simp only [detMoments_eq]
  rw [h]
  exact ((continuous_detEAB T).add (continuous_detEBC T)).add
    (continuous_detECA T) |>.div_const 3

/-- `M3` of `detMoments` is continuous in the three source laws. -/
lemma continuous_detM3 (T : DetTriangle) :
    Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      (detMoments T p.1 p.2.1 p.2.2).M3 := by
  have h : (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      (detMoments T p.1 p.2.1 p.2.2).M3)
      = fun p => detEABC T p.1 p.2.1 p.2.2 := by
    ext p
    simp only [detMoments_eq]
  rw [h]
  exact continuous_detEABC T

/-! ## Finiteness of deterministic response tables

Each response takes values in `{±1}`, so a table is determined by a bit matrix.
-/

namespace RespTable

lemma ext' {T₁ T₂ : RespTable} (h : ∀ j k, T₁ j k = T₂ j k) : T₁ = T₂ := by
  cases T₁ with
  | mk f₁ legal₁ =>
    cases T₂ with
    | mk f₂ legal₂ =>
      have hf : f₁ = f₂ := by
        funext j k
        exact h j k
      subst hf
      rfl

/-- Encode a table as a bit matrix (`true` encodes `+1`). -/
def toBits (T : RespTable) : Fin 3 → Fin 3 → Bool :=
  fun j k => decide (T j k = 1)

/-- Decode a bit matrix as a table. -/
def ofBits (b : Fin 3 → Fin 3 → Bool) : RespTable where
  f j k := if b j k then (1 : ℝ) else -1
  legal j k := by
    by_cases h : b j k
    · rw [if_pos h]
      exact legalSign.one
    · rw [if_neg h]
      exact legalSign.neg_one

lemma ofBits_toBits (T : RespTable) : ofBits (toBits T) = T := by
  apply ext'
  intro j k
  show (if toBits T j k then (1:ℝ) else -1) = T j k
  rcases T.legal j k with h | h
  · have hb : toBits T j k = true := by
      simp only [toBits]
      exact decide_eq_true h
    rw [hb]
    exact h.symm
  · have hb : toBits T j k = false := by
      simp only [toBits]
      exact decide_eq_false (by
        intro he
        rw [h] at he
        exact absurd he (by norm_num))
    rw [hb]
    exact h.symm

lemma toBits_ofBits (b : Fin 3 → Fin 3 → Bool) :
    toBits (ofBits b) = b := by
  funext j k
  show decide (ofBits b j k = 1) = b j k
  cases hb : b j k
  · have h1 : ofBits b j k = (-1 : ℝ) := by
      simp [ofBits, hb]
    show decide (ofBits b j k = 1) = false
    rw [h1]
    exact decide_eq_false (by
      intro he
      exact absurd he (by norm_num))
  · have h1 : ofBits b j k = (1 : ℝ) := by
      simp [ofBits, hb]
    show decide (ofBits b j k = 1) = true
    rw [h1]
    exact decide_eq_true rfl

/-- Equivalence between response tables and bit matrices. -/
def equivBits : RespTable ≃ (Fin 3 → Fin 3 → Bool) where
  toFun := toBits
  invFun := ofBits
  left_inv := ofBits_toBits
  right_inv := toBits_ofBits

end RespTable

instance fintypeRespTable : Fintype RespTable :=
  Fintype.ofEquiv (Fin 3 → Fin 3 → Bool) (RespTable.equivBits).symm

instance fintypeDetTriangle : Fintype DetTriangle :=
  Fintype.ofEquiv (RespTable × RespTable × RespTable)
    { toFun := fun p => ⟨p.1, p.2.1, p.2.2⟩
      invFun := fun T => (T.A, T.B, T.C)
      left_inv := by
        intro p
        rcases p with ⟨a, b, c⟩
        rfl
      right_inv := by
        intro T
        rcases T with ⟨a, b, c⟩
        rfl }

/-! ## Compactness of finite moment images and Lemma 4 -/

/-- Product of three ternary source simplexes. -/
def ternarySources : Set ((Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ)) :=
  (stdSimplex ℝ (Fin 3)) ×ˢ (stdSimplex ℝ (Fin 3)) ×ˢ (stdSimplex ℝ (Fin 3))

lemma isCompact_ternarySources : IsCompact ternarySources :=
  (isCompact_stdSimplex _).prod
    ((isCompact_stdSimplex _).prod (isCompact_stdSimplex _))

/-- Constrained feasible set of source laws for a fixed table. -/
def feasibleSet (T : DetTriangle) : Set ((Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ)) :=
  {p | p.1 ∈ stdSimplex ℝ (Fin 3) ∧ p.2.1 ∈ stdSimplex ℝ (Fin 3) ∧
    p.2.2 ∈ stdSimplex ℝ (Fin 3) ∧
    (detMoments T p.1 p.2.1 p.2.2).M1 = 0 ∧
    (detMoments T p.1 p.2.1 p.2.2).M3 = 0}

lemma feasibleSet_subset {T : DetTriangle} : feasibleSet T ⊆ ternarySources := by
  intro p hp
  refine ⟨hp.1, hp.2.1, hp.2.2.1⟩

lemma isClosed_feasibleSet (T : DetTriangle) : IsClosed (feasibleSet T) := by
  have c1 : Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.1 :=
    continuous_fst
  have c2 : Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.2.1 :=
    continuous_fst.comp continuous_snd
  have c3 : Continuous fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.2.2 :=
    continuous_snd.comp continuous_snd
  have h1 : IsClosed {p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) |
      p.1 ∈ stdSimplex ℝ (Fin 3)} :=
    IsClosed.preimage c1 (isCompact_stdSimplex _).isClosed
  have h2 : IsClosed {p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) |
      p.2.1 ∈ stdSimplex ℝ (Fin 3)} :=
    IsClosed.preimage c2 (isCompact_stdSimplex _).isClosed
  have h3 : IsClosed {p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) |
      p.2.2 ∈ stdSimplex ℝ (Fin 3)} :=
    IsClosed.preimage c3 (isCompact_stdSimplex _).isClosed
  have hM1 : IsClosed {p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) |
      (detMoments T p.1 p.2.1 p.2.2).M1 = 0} :=
    IsClosed.preimage (continuous_detM1 T) isClosed_singleton
  have hM3 : IsClosed {p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) |
      (detMoments T p.1 p.2.1 p.2.2).M3 = 0} :=
    IsClosed.preimage (continuous_detM3 T) isClosed_singleton
  -- Match the association `h1 ∩ (h2 ∩ (h3 ∩ (hM1 ∩ hM3)))`.
  have key : feasibleSet T =
      {p | p.1 ∈ stdSimplex ℝ (Fin 3)} ∩
        ({p | p.2.1 ∈ stdSimplex ℝ (Fin 3)} ∩
          ({p | p.2.2 ∈ stdSimplex ℝ (Fin 3)} ∩
            ({p | (detMoments T p.1 p.2.1 p.2.2).M1 = 0} ∩
              {p | (detMoments T p.1 p.2.1 p.2.2).M3 = 0}))) := by
    ext p
    simp [feasibleSet]
  rw [key]
  exact h1.inter (h2.inter (h3.inter (hM1.inter hM3)))

lemma isCompact_feasibleSet (T : DetTriangle) : IsCompact (feasibleSet T) :=
  isCompact_ternarySources.of_isClosed_subset
    (isClosed_feasibleSet T) feasibleSet_subset

/-- On a compact feasible set, `M2` attains a maximum. -/
lemma exists_isMaxOn_M2 {T : DetTriangle} (hne : (feasibleSet T).Nonempty) :
    ∃ p ∈ feasibleSet T,
      ∀ q ∈ feasibleSet T,
        (detMoments T q.1 q.2.1 q.2.2).M2 ≤ (detMoments T p.1 p.2.1 p.2.2).M2 := by
  obtain ⟨p, hp, hmax⟩ :=
    (isCompact_feasibleSet T).exists_isMaxOn hne ((continuous_detM2 T).continuousOn)
  refine ⟨p, hp, fun q hq => ?_⟩
  exact isMaxOn_iff.1 hmax q hq

/-! ### A concrete feasible ternary model -/

/-- Table with `f j k = 1` iff `j = 0`. -/
def signTable : RespTable where
  f j _ := if j = 0 then (1 : ℝ) else -1
  legal j _ := by
    by_cases h : j = 0
    · rw [if_pos h]
      exact legalSign.one
    · rw [if_neg h]
      exact legalSign.neg_one

/-- Witness table: all three parties use `signTable`. -/
def witnessTable : DetTriangle := ⟨signTable, signTable, signTable⟩

instance : Nonempty DetTriangle := ⟨witnessTable⟩

/-- Witness law: `(1/2, 1/2, 0)` on `Fin 3`. -/
def witnessQ : Simplex2 where
  v i := if i = 0 then 1 / 2 else if i = 1 then 1 / 2 else 0
  nonneg := by
    intro i
    by_cases h0 : i = 0
    · subst h0; simp
    by_cases h1 : i = 1
    · subst h1; simp
    · simp [h0, h1]
  sum_eq := by
    rw [Fin.sum_univ_three]
    simp
    norm_num

@[simp] lemma witnessQ_zero : (witnessQ : Fin 3 → ℝ) 0 = 1 / 2 := by
  simp [witnessQ]

@[simp] lemma witnessQ_one : (witnessQ : Fin 3 → ℝ) 1 = 1 / 2 := by
  simp [witnessQ]

@[simp] lemma witnessQ_two : (witnessQ : Fin 3 → ℝ) 2 = 0 := by
  simp [witnessQ]

lemma signTable_val (j k : Fin 3) :
    signTable j k = if j = 0 then (1 : ℝ) else -1 := rfl

/-- The witness satisfies `M1 = 0`. -/
lemma witnessM1_zero :
    (detMoments witnessTable (witnessQ : Fin 3 → ℝ) (witnessQ : Fin 3 → ℝ)
      (witnessQ : Fin 3 → ℝ)).M1 = 0 := by
  simp only [detMoments, witnessQ, witnessTable, signTable_val]
  repeat' rw [Fin.sum_univ_three]
  simp
  abel

/-- The witness satisfies `M3 = 0`. -/
lemma witnessM3_zero :
    (detMoments witnessTable (witnessQ : Fin 3 → ℝ) (witnessQ : Fin 3 → ℝ)
      (witnessQ : Fin 3 → ℝ)).M3 = 0 := by
  simp only [detMoments, witnessQ, witnessTable, signTable_val]
  repeat' rw [Fin.sum_univ_three]
  simp

lemma witnessQ_mem : (witnessQ : Fin 3 → ℝ) ∈ stdSimplex ℝ (Fin 3) :=
  ⟨witnessQ.nonneg, witnessQ.sum_eq⟩

/-- The constrained set is nonempty for the witness table. -/
lemma witness_mem_feasibleSet :
    ((witnessQ : Fin 3 → ℝ), (witnessQ : Fin 3 → ℝ), (witnessQ : Fin 3 → ℝ))
      ∈ feasibleSet witnessTable :=
  ⟨witnessQ_mem, witnessQ_mem, witnessQ_mem, witnessM1_zero, witnessM3_zero⟩

lemma feasibleSet_witness_nonempty :
    (feasibleSet witnessTable).Nonempty :=
  ⟨_, witness_mem_feasibleSet⟩

/-- Feasible set of some deterministic table is nonempty. -/
lemma exists_feasible_det :
    ∃ (T : DetTriangle) (p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ)),
      p ∈ feasibleSet T :=
  ⟨witnessTable, ((witnessQ : Fin 3 → ℝ), (witnessQ : Fin 3 → ℝ),
    (witnessQ : Fin 3 → ℝ)), witness_mem_feasibleSet⟩

/-! ## Lemma 4: ternary optimizing reduction

Among all deterministic ternary models with `M1 = M3 = 0`, a global maximum of
`M2` is attained.  This is the finite form of Lemma 4 used by Theorem 1.
-/

open Classical in
/-- A feasible maximizer for `T`, or a dummy point when the constraint set is
empty. -/
noncomputable def pickPoint (T : DetTriangle) :
    (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ) :=
  if h : (feasibleSet T).Nonempty then
    (exists_isMaxOn_M2 h).choose
  else (0, 0, 0)

open Classical in
lemma pickPoint_mem {T : DetTriangle} (h : (feasibleSet T).Nonempty) :
    pickPoint T ∈ feasibleSet T := by
  simp only [pickPoint, dif_pos h]
  exact (exists_isMaxOn_M2 h).choose_spec.1

open Classical in
lemma pickPoint_isMax {T : DetTriangle} (h : (feasibleSet T).Nonempty) :
    ∀ q ∈ feasibleSet T,
      (detMoments T q.1 q.2.1 q.2.2).M2 ≤
        (detMoments T (pickPoint T).1 (pickPoint T).2.1 (pickPoint T).2.2).M2 := by
  simp only [pickPoint, dif_pos h]
  exact (exists_isMaxOn_M2 h).choose_spec.2

open Classical in
/-- Objective value of a table: its constrained maximum of `M2`, or `-1` when
infeasible. -/
noncomputable def valOf (T : DetTriangle) : ℝ :=
  if (feasibleSet T).Nonempty then
    (detMoments T (pickPoint T).1 (pickPoint T).2.1 (pickPoint T).2.2).M2
  else -1

open Classical in
lemma valOf_ge_of_mem {T : DetTriangle} {q : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hq : q ∈ feasibleSet T) :
    (detMoments T q.1 q.2.1 q.2.2).M2 ≤ valOf T := by
  have hne : (feasibleSet T).Nonempty := ⟨q, hq⟩
  show _ ≤ if (feasibleSet T).Nonempty then _ else _
  rw [if_pos hne]
  exact pickPoint_isMax hne q hq

/-- `M2` of the witness laws under the witness table. -/
lemma witnessM2_zero :
    (detMoments witnessTable (witnessQ : Fin 3 → ℝ) (witnessQ : Fin 3 → ℝ)
      (witnessQ : Fin 3 → ℝ)).M2 = 0 := by
  simp only [detMoments, witnessQ, witnessTable, signTable_val]
  repeat' rw [Fin.sum_univ_three]
  simp
  abel

open Classical in
lemma valOf_witness_nonneg : 0 ≤ valOf witnessTable := by
  have hne : (feasibleSet witnessTable).Nonempty := feasibleSet_witness_nonempty
  show 0 ≤ if (feasibleSet witnessTable).Nonempty then _ else _
  rw [if_pos hne]
  have h := pickPoint_isMax hne _ witness_mem_feasibleSet
  linarith [witnessM2_zero]

set_option maxRecDepth 8192 in
/-- **Lemma 4 (finite ternary form).**  The maximum of `M2` over all
deterministic ternary models with `M1 = M3 = 0` is attained. -/
lemma lemma4_ternary_reduction :
    ∃ (T : DetTriangle) (p : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ)),
      p ∈ feasibleSet T ∧
      ∀ (T' : DetTriangle) (q : (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ)),
        q ∈ feasibleSet T' →
          (detMoments T' q.1 q.2.1 q.2.2).M2 ≤
            (detMoments T p.1 p.2.1 p.2.2).M2 := by
  classical
  obtain ⟨T, -, hmax⟩ :=
    Finset.exists_max_image (univ : Finset DetTriangle) valOf univ_nonempty
  have hfeas : (feasibleSet T).Nonempty := by
    by_contra hempty
    have hval : valOf T = -1 := by
      show (if (feasibleSet T).Nonempty then _ else _) = -1
      exact if_neg hempty
    have hle : valOf witnessTable ≤ valOf T := hmax witnessTable (mem_univ _)
    rw [hval] at hle
    exact absurd (le_trans valOf_witness_nonneg hle) (by norm_num)
  refine ⟨T, pickPoint T, pickPoint_mem hfeas, ?_⟩
  intro T' q hq
  have h1 : (detMoments T' q.1 q.2.1 q.2.2).M2 ≤ valOf T' := valOf_ge_of_mem hq
  have h2 : valOf T' ≤ valOf T := hmax T' (mem_univ _)
  have h3 : valOf T = (detMoments T (pickPoint T).1 (pickPoint T).2.1
      (pickPoint T).2.2).M2 := by
    show (if (feasibleSet T).Nonempty then _ else _) = _
    exact if_pos hfeas
  calc (detMoments T' q.1 q.2.1 q.2.2).M2 ≤ valOf T' := h1
    _ ≤ valOf T := h2
    _ = (detMoments T (pickPoint T).1 (pickPoint T).2.1 (pickPoint T).2.2).M2 := h3

set_option maxRecDepth 8192 in
/-- Restatement of Lemma 4 in the `Simplex2` / `detMoments'` form. -/
lemma lemma4_ternary_reduction' :
    ∃ (T : DetTriangle) (qx qy qz : Simplex2),
      (detMoments' T qx qy qz).M1 = 0 ∧
      (detMoments' T qx qy qz).M3 = 0 ∧
      ∀ (T' : DetTriangle) (qx' qy' qz' : Simplex2),
        (detMoments' T' qx' qy' qz').M1 = 0 →
        (detMoments' T' qx' qy' qz').M3 = 0 →
        (detMoments' T' qx' qy' qz').M2 ≤ (detMoments' T qx qy qz).M2 := by
  obtain ⟨T, p, hp, hmax⟩ := lemma4_ternary_reduction
  have h1 : p.1 ∈ stdSimplex ℝ (Fin 3) := hp.1
  have h2 : p.2.1 ∈ stdSimplex ℝ (Fin 3) := hp.2.1
  have h3 : p.2.2 ∈ stdSimplex ℝ (Fin 3) := hp.2.2.1
  let qx' : Simplex2 := ⟨p.1, h1.1, h1.2⟩
  let qy' : Simplex2 := ⟨p.2.1, h2.1, h2.2⟩
  let qz' : Simplex2 := ⟨p.2.2, h3.1, h3.2⟩
  refine ⟨T, qx', qy', qz', ?_, ?_, ?_⟩
  · show (detMoments T p.1 p.2.1 p.2.2).M1 = 0
    exact hp.2.2.2.1
  · show (detMoments T p.1 p.2.1 p.2.2).M3 = 0
    exact hp.2.2.2.2
  · intro T' sx sy sz hM1 hM3
    have hx' : (sx : Fin 3 → ℝ) ∈ stdSimplex ℝ (Fin 3) := ⟨sx.nonneg, sx.sum_eq⟩
    have hy' : (sy : Fin 3 → ℝ) ∈ stdSimplex ℝ (Fin 3) := ⟨sy.nonneg, sy.sum_eq⟩
    have hz' : (sz : Fin 3 → ℝ) ∈ stdSimplex ℝ (Fin 3) := ⟨sz.nonneg, sz.sum_eq⟩
    have hq : ((sx : Fin 3 → ℝ), (sy : Fin 3 → ℝ), (sz : Fin 3 → ℝ))
        ∈ feasibleSet T' :=
      ⟨hx', hy', hz', hM1, hM3⟩
    have := hmax T' ((sx : Fin 3 → ℝ), (sy : Fin 3 → ℝ), (sz : Fin 3 → ℝ)) hq
    simpa [detMoments'] using this

end Paper15
