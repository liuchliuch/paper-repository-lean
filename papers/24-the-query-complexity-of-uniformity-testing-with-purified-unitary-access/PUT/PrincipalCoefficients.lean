import PUT.Creation
import PUT.Erasure
import PUT.Adversary
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Actual principal Fourier coefficient vectors, equations (12)--(15)

The coefficients here use the normalization printed in the paper. In
particular the posterior coefficient is not divided by `sqrt d` a second
time. All norms below are genuine Euclidean norms of complex vectors.
-/
noncomputable section
namespace PUT.Principal

/-- A real coefficient family as an actual complex Euclidean vector. -/
def vector {ι : Type*} [Fintype ι] (c : ι → ℝ) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => (c i : ℂ))

@[simp] theorem vector_apply {ι : Type*} [Fintype ι] (c : ι → ℝ) (i : ι) :
    vector c i = (c i : ℂ) := rfl

theorem norm_vector_sq {ι : Type*} [Fintype ι] (c : ι → ℝ) :
    ‖vector c‖ ^ 2 = ∑ i, c i ^ 2 := by
  simp [PiLp.norm_sq_eq_of_L2, vector, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem norm_vector_le {ι : Type*} [Fintype ι] (c : ι → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hc : ∑ i, c i ^ 2 ≤ C ^ 2) : ‖vector c‖ ≤ C := by
  rw [← norm_vector_sq] at hc
  exact le_of_sq_le_sq hc hC

/-- Correct unreplicated creation coefficient for `D₊`. -/
def creationPlus {d : ℕ} (a A : ℝ) (k : Fin d → ℕ) (i : Fin d) : ℝ :=
  cutoff A (degUp k i) * createCoeff a k i - cutoff A k / Real.sqrt d

/-- Correct unreplicated creation coefficient for `D₋`. -/
def creationMinus {d : ℕ} (a A : ℝ) (k : Fin d → ℕ) (i : Fin d) : ℝ :=
  cutoff A k * createCoeff a k i - cutoff A (degUp k i) / Real.sqrt d

def creationBound (a A d : ℝ) : ℝ :=
  Real.sqrt (1 + 8 * A / d) + A ^ (3 / 2 : ℝ) / (a * Real.sqrt d)

private theorem sum_slope_square {d : ℕ} (k : Fin d → ℕ) :
    ∑ i, (2 * (k i : ℝ) + 1) ^ 2 = 4 * (degR k : ℝ) + 4 * degK k + d := by
  simp_rw [show ∀ i : Fin d, (2 * (k i : ℝ) + 1) ^ 2 =
    4 * (k i : ℝ) ^ 2 + 4 * (k i : ℝ) + 1 by intro i; ring]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    ← degR_coe, ← degK_coe, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]

private theorem slope_norm {d : ℕ} (k : Fin d → ℕ) (A : ℝ)
    (hd : 0 < d) (hR : (degR k : ℝ) < A) (c : Fin d → ℝ)
    (hc : ∀ i, |c i| ≤ 2 * (k i : ℝ) + 1) :
    ‖vector (fun i => c i / Real.sqrt d)‖ ≤ Real.sqrt (1 + 8 * A / d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hA : 0 < A := lt_of_le_of_lt (Nat.cast_nonneg _) hR
  apply norm_vector_le _ _ (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (by positivity : 0 ≤ 1 + 8 * A / d)]
  calc
    (∑ i, (c i / Real.sqrt d) ^ 2)
        = (∑ i, c i ^ 2) / d := by
      simp_rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
      rw [Finset.sum_div]
    _ ≤ (∑ i, (2 * (k i : ℝ) + 1) ^ 2) / d := by
      apply div_le_div_of_nonneg_right _ hd0.le
      apply Finset.sum_le_sum
      intro i _
      have h := pow_le_pow_left₀ (abs_nonneg (c i)) (hc i) 2
      simpa [sq_abs] using h
    _ ≤ 1 + 8 * A / d := by
      rw [sum_slope_square]
      have hK : (degK k : ℝ) ≤ degR k := by exact_mod_cast degK_le_degR k
      apply (div_le_iff₀ hd0).mpr
      have he : (1 + 8 * A / (d : ℝ)) * d = d + 8 * A := by field_simp
      rw [he]
      linarith

private theorem displacement_norm {d : ℕ} (a A : ℝ) (k : Fin d → ℕ)
    (ha : 0 < a) (hd : 0 < d) (hR : (degR k : ℝ) < A)
    (w : Fin d → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hwA : ∀ i, w i ≤ A) :
    ‖vector (fun i => w i * (createCoeff a k i - 1 / Real.sqrt d))‖ ≤
      A ^ (3 / 2 : ℝ) / (a * Real.sqrt d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hA : 0 < A := lt_of_le_of_lt (Nat.cast_nonneg _) hR
  have hroot : Real.sqrt ((1 : ℝ) / d) = 1 / Real.sqrt d := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_one]
  have hdev := sqrt_mean_dev a k ha hd
  simp only [createCoeff, postTotal] at *
  change (∑ i, (Real.sqrt ((a + k i) / (a * d + degK k)) - Real.sqrt ((1 : ℝ) / d)) ^ 2)
    ≤ (degR k : ℝ) / (a ^ 2 * d) at hdev
  rw [hroot] at hdev
  apply norm_vector_le _ _ (by positivity)
  have hsum :
      (∑ i, (w i * (Real.sqrt ((a + k i) / (a * d + degK k)) - 1 / Real.sqrt d)) ^ 2)
        ≤ A ^ 2 * ((degR k : ℝ) / (a ^ 2 * d)) := by
    calc
      _ ≤ ∑ i, A ^ 2 * (Real.sqrt ((a + k i) / (a * d + degK k)) - 1 / Real.sqrt d) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (hw0 i) (hwA i) 2) (sq_nonneg _)
      _ = A ^ 2 * ∑ i, (Real.sqrt ((a + k i) / (a * d + degK k)) - 1 / Real.sqrt d) ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hdev (sq_nonneg A)
  have hR' : A ^ 2 * ((degR k : ℝ) / (a ^ 2 * d)) ≤ A ^ 3 / (a ^ 2 * d) := by
    have ht := mul_le_mul_of_nonneg_left hR.le (sq_nonneg A)
    calc
      _ = (A ^ 2 * (degR k : ℝ)) / (a ^ 2 * d) := by ring
      _ ≤ A ^ 3 / (a ^ 2 * d) := div_le_div_of_nonneg_right
        (by simpa [pow_succ] using ht) (by positivity)
  have heq : (A ^ (3 / 2 : ℝ) / (a * Real.sqrt d)) ^ 2 = A ^ 3 / (a ^ 2 * d) := by
    rw [h_term_bound A a d hA ha hd0, div_pow, mul_pow, mul_pow,
      Real.sq_sqrt hA.le, Real.sq_sqrt hd0.le]
    ring
  rw [heq]
  exact hsum.trans hR'

private theorem cutoff_up_zero {d : ℕ} (A : ℝ) (k : Fin d → ℕ) (i : Fin d)
    (hR : A ≤ (degR k : ℝ)) : cutoff A (degUp k i) = 0 := by
  apply cutoff_finite_support
  rw [sum_sq_degUp, ← degR_coe]
  have : (0 : ℝ) ≤ k i := Nat.cast_nonneg _
  linarith

/-- The entire creation column coefficient vector has the paper's bound;
indices beyond the cutoff are proved to give the zero vector. -/
theorem creationPlus_norm {d : ℕ} (a A : ℝ) (k : Fin d → ℕ)
    (ha : 0 < a) (hA : 0 < A) (hd : 0 < d) :
    ‖vector (creationPlus a A k)‖ ≤ creationBound a A d := by
  by_cases hR : (degR k : ℝ) < A
  · let c := fun i => cutoff A (degUp k i) - cutoff A k
    let v := fun i => cutoff A (degUp k i) * (createCoeff a k i - 1 / Real.sqrt d)
    have heq : vector (creationPlus a A k) = vector (fun i => c i / Real.sqrt d) + vector v := by
      ext i
      simp only [vector_apply, PiLp.add_apply]
      norm_cast
      dsimp [creationPlus, c, v]
      ring
    rw [heq]
    have hc := slope_norm k A hd hR c (fun i => cutoff_succ_le A k i)
    have hv := displacement_norm a A k ha hd hR (fun i => cutoff A (degUp k i))
      (fun i => cutoff_nonneg A (degUp k i))
      (fun i => cutoff_le_of_nonneg hA.le (degUp k i))
    exact (norm_add_le _ _).trans (add_le_add hc hv)
  · have heq : vector (creationPlus a A k) = 0 := by
      ext i
      have hk := cutoff_finite_support_degR A k (le_of_not_gt hR)
      have hu := cutoff_up_zero A k i (le_of_not_gt hR)
      simp [creationPlus, hk, hu]
    rw [heq, norm_zero]
    unfold creationBound
    positivity

/-- The entire creation row coefficient vector has the same bound. -/
theorem creationMinus_norm {d : ℕ} (a A : ℝ) (k : Fin d → ℕ)
    (ha : 0 < a) (hA : 0 < A) (hd : 0 < d) :
    ‖vector (creationMinus a A k)‖ ≤ creationBound a A d := by
  by_cases hR : (degR k : ℝ) < A
  · let c := fun i => cutoff A k - cutoff A (degUp k i)
    let v := fun i => cutoff A k * (createCoeff a k i - 1 / Real.sqrt d)
    have heq : vector (creationMinus a A k) = vector (fun i => c i / Real.sqrt d) + vector v := by
      ext i
      simp only [vector_apply, PiLp.add_apply]
      norm_cast
      dsimp [creationMinus, c, v]
      ring
    rw [heq]
    have hc := slope_norm k A hd hR c (fun i => by
      dsimp [c]; rw [abs_sub_comm]; exact cutoff_succ_le A k i)
    have hv := displacement_norm a A k ha hd hR (fun _ => cutoff A k)
      (fun _ => cutoff_nonneg A k) (fun _ => cutoff_le_of_nonneg hA.le k)
    exact (norm_add_le _ _).trans (add_le_add hc hv)
  · have heq : vector (creationMinus a A k) = 0 := by
      ext i
      have hk := cutoff_finite_support_degR A k (le_of_not_gt hR)
      have hu := cutoff_up_zero A k i (le_of_not_gt hR)
      simp [creationMinus, hk, hu]
    rw [heq, norm_zero]
    unfold creationBound
    positivity

end PUT.Principal

namespace PUT.Principal

/-- Repeating one coefficient M times and dividing by sqrt M is an isometry;
masking an arbitrary set of coordinates can only reduce its norm. -/
theorem masked_replication_norm_le {d M : ℕ} (c : Fin d → ℝ)
    (mask : Fin d × Fin M → Prop) [DecidablePred mask] (hM : 0 < M) :
    ‖vector (fun ij => if mask ij then c ij.1 / Real.sqrt M else 0)‖ ≤ ‖vector c‖ := by
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [norm_vector_sq, norm_vector_sq]
  calc
    (∑ ij : Fin d × Fin M, (if mask ij then c ij.1 / Real.sqrt M else 0) ^ 2)
      ≤ ∑ ij : Fin d × Fin M, (c ij.1 / Real.sqrt M) ^ 2 := by
        apply Finset.sum_le_sum
        intro ij _
        split_ifs <;> simp [sq_nonneg]
    _ = ∑ i, c i ^ 2 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
        div_pow, Real.sq_sqrt (Nat.cast_nonneg M)]
      have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      field_simp

/-- Number of negative phase coordinates is at most the total degree. -/
theorem negativeCount_le_degree {d M : ℕ} (n : PhaseIndex d M) :
    (∑ ij : Fin d × Fin M, if n ij.1 ij.2 < 0 then (1 : ℝ) else 0) ≤
      (degK (degreeOf n) : ℝ) := by
  have hnat : (∑ ij : Fin d × Fin M, if n ij.1 ij.2 < 0 then (1 : ℕ) else 0) ≤
      degK (degreeOf n) := by
    calc
      _ ≤ ∑ ij : Fin d × Fin M, (n ij.1 ij.2).natAbs := by
        apply Finset.sum_le_sum
        intro ij _
        split_ifs with h
        · have : 0 < (n ij.1 ij.2).natAbs := Int.natAbs_pos.mpr (ne_of_lt h)
          omega
        · exact Nat.zero_le _
      _ = degK (degreeOf n) := by
        simp only [Fintype.sum_prod_type, degK, degreeOf, labelDegree]
  exact_mod_cast hnat

/-- Any negative coordinate has positive label degree. -/
theorem degree_pos_of_negative {d M : ℕ} (n : PhaseIndex d M) (i : Fin d) (j : Fin M)
    (h : n i j < 0) : 0 < degreeOf n i := by
  have hpos : 0 < (n i j).natAbs := Int.natAbs_pos.mpr (ne_of_lt h)
  have hle : (n i j).natAbs ≤ degreeOf n i := by
    exact Finset.single_le_sum (fun t _ => Nat.zero_le ((n i t).natAbs)) (Finset.mem_univ j)
  omega

/-- Correct unreplicated erasure coefficient in a preparation column. -/
def erasurePlus {d : ℕ} (a A : ℝ) (k : Fin d → ℕ) (i : Fin d) : ℝ :=
  cutoff A (degDown k i) * eraseCoeff a k i - cutoff A k / Real.sqrt d

/-- Correct unreplicated erasure coefficient in an erasure row. -/
def erasureMinus {d : ℕ} (a A : ℝ) (k : Fin d → ℕ) (i : Fin d) : ℝ :=
  cutoff A k * eraseCoeff a k i - cutoff A (degDown k i) / Real.sqrt d

theorem eraseCoeff_le_one {d : ℕ} (a : ℝ) (k : Fin d → ℕ) (i : Fin d)
    (ha : 0 < a) (hd : 0 < d) (hi : 0 < k i) : eraseCoeff a k i ≤ 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hk : (k i : ℝ) ≤ degK k := by
    exact_mod_cast (Finset.single_le_sum (fun t _ => Nat.zero_le (k t)) (Finset.mem_univ i))
  have hk1 : (1 : ℝ) ≤ k i := by exact_mod_cast hi
  have hS : 0 < postTotal a k - 1 := by
    unfold postTotal
    nlinarith
  have hq0 : 0 ≤ (a + k i - 1) / (postTotal a k - 1) :=
    div_nonneg (by linarith) hS.le
  have hq1 : (a + k i - 1) / (postTotal a k - 1) ≤ 1 := by
    apply (div_le_one hS).mpr
    unfold postTotal
    nlinarith
  unfold eraseCoeff
  exact (Real.sqrt_le_one).mpr hq1

private theorem uniformRoot_le_one {d : ℕ} (hd : 0 < d) : (1 : ℝ) / Real.sqrt d ≤ 1 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : (1 : ℝ) ≤ Real.sqrt d := by
    simpa using Real.sqrt_le_sqrt hd1
  exact (div_le_one (by positivity : 0 < Real.sqrt d)).mpr hs

private theorem erasure_abs_le {d : ℕ} (a A : ℝ) (k : Fin d → ℕ) (i : Fin d)
    (ha : 0 < a) (hA : 0 ≤ A) (hd : 0 < d) (hi : 0 < k i) :
    |erasurePlus a A k i| ≤ 2 * A ∧ |erasureMinus a A k i| ≤ 2 * A := by
  have hb0 : 0 ≤ eraseCoeff a k i := Real.sqrt_nonneg _
  have hb1 := eraseCoeff_le_one a k i ha hd hi
  have hu0 : 0 ≤ (1 : ℝ) / Real.sqrt d := by positivity
  have hu1 := uniformRoot_le_one hd
  have hk0 := cutoff_nonneg A k
  have hk1 := cutoff_le_of_nonneg hA k
  have hl0 := cutoff_nonneg A (degDown k i)
  have hl1 := cutoff_le_of_nonneg hA (degDown k i)
  have hkB : cutoff A k * eraseCoeff a k i ≤ A := by nlinarith
  have hlB : cutoff A (degDown k i) * eraseCoeff a k i ≤ A := by nlinarith
  have hkU : cutoff A k / Real.sqrt d ≤ A := by
    rw [div_eq_mul_inv]
    have : (Real.sqrt (d : ℝ))⁻¹ ≤ 1 := by simpa [one_div] using hu1
    nlinarith
  have hlU : cutoff A (degDown k i) / Real.sqrt d ≤ A := by
    rw [div_eq_mul_inv]
    have : (Real.sqrt (d : ℝ))⁻¹ ≤ 1 := by simpa [one_div] using hu1
    nlinarith
  have hku0 : 0 ≤ cutoff A k / Real.sqrt d := by positivity
  have hlu0 : 0 ≤ cutoff A (degDown k i) / Real.sqrt d := by positivity
  constructor <;> dsimp only [erasurePlus, erasureMinus] <;> apply abs_le.mpr <;>
    constructor <;> nlinarith [mul_nonneg hk0 hb0, mul_nonneg hl0 hb0]

/-- Coefficients of the complete principal preparation column. -/
def principalPlus {d M : ℕ} (a A : ℝ) (n : PhaseIndex d M)
    (ij : Fin d × Fin M) : ℝ :=
  (if 0 ≤ n ij.1 ij.2 then creationPlus a A (degreeOf n) ij.1
    else erasurePlus a A (degreeOf n) ij.1) / Real.sqrt M

/-- Coefficients of the complete principal erasure row. -/
def principalMinus {d M : ℕ} (a A : ℝ) (n : PhaseIndex d M)
    (ij : Fin d × Fin M) : ℝ :=
  (if 0 ≤ n ij.1 ij.2 then creationMinus a A (degreeOf n) ij.1
    else erasureMinus a A (degreeOf n) ij.1) / Real.sqrt M

end PUT.Principal

namespace PUT.Principal

private theorem erasure_mask_norm {d M : ℕ} (A : ℝ) (n : PhaseIndex d M)
    (c : Fin d → ℝ) (hA : 0 ≤ A) (hM : 0 < M)
    (hbound : ∀ i, 0 < degreeOf n i → |c i| ≤ 2 * A)
    (hzero : LA A ≤ (degR (degreeOf n) : ℝ) → ∀ i, 0 < degreeOf n i → c i = 0) :
    ‖vector (fun ij : Fin d × Fin M => if n ij.1 ij.2 < 0 then
      c ij.1 / Real.sqrt M else 0)‖ ≤ etaM A M := by
  by_cases hR : (degR (degreeOf n) : ℝ) < LA A
  · have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
    have hLA0 : 0 ≤ LA A := by unfold LA; positivity
    have hC0 : 0 ≤ 2 * A / Real.sqrt M := by positivity
    apply norm_vector_le _ _ (by unfold etaM; positivity)
    have hs : (∑ ij : Fin d × Fin M,
        (if n ij.1 ij.2 < 0 then c ij.1 / Real.sqrt M else 0) ^ 2)
        ≤ (2 * A / Real.sqrt M) ^ 2 *
          (∑ ij : Fin d × Fin M, if n ij.1 ij.2 < 0 then (1 : ℝ) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro ij _
      by_cases hneg : n ij.1 ij.2 < 0
      · simp only [if_pos hneg, mul_one]
        have hb := hbound ij.1 (degree_pos_of_negative n ij.1 ij.2 hneg)
        have hdiv : |c ij.1 / Real.sqrt M| ≤ 2 * A / Real.sqrt M := by
          rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
          exact div_le_div_of_nonneg_right hb (Real.sqrt_nonneg _)
        have := pow_le_pow_left₀ (abs_nonneg _) hdiv 2
        simpa [sq_abs] using this
      · simp [hneg]
    have hc := negativeCount_le_degree n
    have hK : (degK (degreeOf n) : ℝ) ≤ degR (degreeOf n) := by
      exact_mod_cast degK_le_degR (degreeOf n)
    have hcount : (∑ ij : Fin d × Fin M, if n ij.1 ij.2 < 0 then (1 : ℝ) else 0) ≤ LA A := by
      linarith
    have hh := mul_le_mul_of_nonneg_left hcount (sq_nonneg (2 * A / Real.sqrt M))
    have he : (2 * A / Real.sqrt M) ^ 2 * LA A = (etaM A M) ^ 2 := by
      unfold etaM
      rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt hM0.le,
        Real.sq_sqrt (div_nonneg hLA0 hM0.le)]
      ring
    exact hs.trans (by simpa only [he] using hh)
  · have hz : vector (fun ij : Fin d × Fin M => if n ij.1 ij.2 < 0 then
        c ij.1 / Real.sqrt M else 0) = 0 := by
      ext ij
      by_cases hneg : n ij.1 ij.2 < 0
      · simp [hneg, hzero (le_of_not_gt hR) ij.1
          (degree_pos_of_negative n ij.1 ij.2 hneg)]
      · simp [hneg]
    rw [hz, norm_zero]
    unfold etaM
    positivity

private theorem erasure_zero_outside {d : ℕ} (a A : ℝ) (k : Fin d → ℕ)
    (hA : 0 ≤ A) (hR : LA A ≤ (degR k : ℝ)) (i : Fin d) (hi : 0 < k i) :
    erasurePlus a A k i = 0 ∧ erasureMinus a A k i = 0 := by
  have hLA : A ≤ LA A := by
    unfold LA
    nlinarith [Real.sq_sqrt hA, Real.sqrt_nonneg A]
  have hk : cutoff A k = 0 := cutoff_finite_support_degR A k (hLA.trans hR)
  have hl : cutoff A (degDown k i) = 0 := by
    by_contra h
    have ht := erasure_R_lt_LA k i A h hA hi
    linarith
  simp [erasurePlus, erasureMinus, hk, hl]

theorem erasurePlus_norm {d M : ℕ} (a A : ℝ) (n : PhaseIndex d M)
    (ha : 0 < a) (hA : 0 ≤ A) (hd : 0 < d) (hM : 0 < M) :
    ‖vector (fun ij : Fin d × Fin M => if n ij.1 ij.2 < 0 then
      erasurePlus a A (degreeOf n) ij.1 / Real.sqrt M else 0)‖ ≤ etaM A M := by
  apply erasure_mask_norm A n _ hA hM
  · intro i hi
    exact (erasure_abs_le a A (degreeOf n) i ha hA hd hi).1
  · intro hR i hi
    exact (erasure_zero_outside a A (degreeOf n) hA hR i hi).1

theorem erasureMinus_norm {d M : ℕ} (a A : ℝ) (n : PhaseIndex d M)
    (ha : 0 < a) (hA : 0 ≤ A) (hd : 0 < d) (hM : 0 < M) :
    ‖vector (fun ij : Fin d × Fin M => if n ij.1 ij.2 < 0 then
      erasureMinus a A (degreeOf n) ij.1 / Real.sqrt M else 0)‖ ≤ etaM A M := by
  apply erasure_mask_norm A n _ hA hM
  · intro i hi
    exact (erasure_abs_le a A (degreeOf n) i ha hA hd hi).2
  · intro hR i hi
    exact (erasure_zero_outside a A (degreeOf n) hA hR i hi).2

/-- Complete source principal column norm, creation and erasure included. -/
theorem principalPlus_norm {d M : ℕ} (a A : ℝ) (n : PhaseIndex d M)
    (ha : 0 < a) (hA : 0 < A) (hd : 0 < d) (hM : 0 < M) :
    ‖vector (principalPlus a A n)‖ ≤ creationBound a A d + etaM A M := by
  let c := fun ij : Fin d × Fin M => if 0 ≤ n ij.1 ij.2 then
    creationPlus a A (degreeOf n) ij.1 / Real.sqrt M else 0
  let e := fun ij : Fin d × Fin M => if n ij.1 ij.2 < 0 then
    erasurePlus a A (degreeOf n) ij.1 / Real.sqrt M else 0
  have heq : vector (principalPlus a A n) = vector c + vector e := by
    ext ij
    by_cases hneg : n ij.1 ij.2 < 0
    · simp [principalPlus, c, e, hneg, not_le.mpr hneg]
    · simp [principalPlus, c, e, hneg, le_of_not_gt hneg]
  have hc : ‖vector c‖ ≤ creationBound a A d :=
    (masked_replication_norm_le (creationPlus a A (degreeOf n)) _ hM).trans
      (creationPlus_norm a A _ ha hA hd)
  have he := erasurePlus_norm a A n ha hA.le hd hM
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add hc he)

/-- Complete source principal row norm, creation and erasure included. -/
theorem principalMinus_norm {d M : ℕ} (a A : ℝ) (n : PhaseIndex d M)
    (ha : 0 < a) (hA : 0 < A) (hd : 0 < d) (hM : 0 < M) :
    ‖vector (principalMinus a A n)‖ ≤ creationBound a A d + etaM A M := by
  let c := fun ij : Fin d × Fin M => if 0 ≤ n ij.1 ij.2 then
    creationMinus a A (degreeOf n) ij.1 / Real.sqrt M else 0
  let e := fun ij : Fin d × Fin M => if n ij.1 ij.2 < 0 then
    erasureMinus a A (degreeOf n) ij.1 / Real.sqrt M else 0
  have heq : vector (principalMinus a A n) = vector c + vector e := by
    ext ij
    by_cases hneg : n ij.1 ij.2 < 0
    · simp [principalMinus, c, e, hneg, not_le.mpr hneg]
    · simp [principalMinus, c, e, hneg, le_of_not_gt hneg]
  have hc : ‖vector c‖ ≤ creationBound a A d :=
    (masked_replication_norm_le (creationMinus a A (degreeOf n)) _ hM).trans
      (creationMinus_norm a A _ ha hA hd)
  have he := erasureMinus_norm a A n ha hA.le hd hM
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add hc he)

end PUT.Principal
