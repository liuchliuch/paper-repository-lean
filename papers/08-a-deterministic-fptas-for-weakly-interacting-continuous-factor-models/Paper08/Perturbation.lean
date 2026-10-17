import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import Paper08.Basic

/-!
# Stability of finite multilinear quadrature

The estimates in this file apply to an arbitrary retained subset of a finite
box of levels.  In particular they apply to the total-level rule (3.4).
The proof sums the actual differences of products; it does not assume a
quadrature error estimate.
-/

noncomputable section
open scoped BigOperators
namespace Paper08.Quadrature

/-- A finite product is Lipschitz in its factors, with the products of the
other majorants appearing as its coordinatewise constants. -/
theorem abs_prod_sub_prod_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b c d : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hd : ∀ i ∈ s, 0 ≤ d i)
    (ha : ∀ i ∈ s, |a i| ≤ c i) (hb : ∀ i ∈ s, |b i| ≤ c i)
    (hab : ∀ i ∈ s, |a i - b i| ≤ d i) :
    |(∏ i ∈ s, a i) - ∏ i ∈ s, b i| ≤
      ∑ i ∈ s, d i * ∏ j ∈ s.erase i, c j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    have hc' : ∀ i ∈ s, 0 ≤ c i := fun i hi => hc i (Finset.mem_insert_of_mem hi)
    have hd' : ∀ i ∈ s, 0 ≤ d i := fun i hi => hd i (Finset.mem_insert_of_mem hi)
    have ha' : ∀ i ∈ s, |a i| ≤ c i := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, |b i| ≤ c i := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hab' : ∀ i ∈ s, |a i - b i| ≤ d i := fun i hi => hab i (Finset.mem_insert_of_mem hi)
    have hprod : |∏ i ∈ s, b i| ≤ ∏ i ∈ s, c i := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) hb'
    have hdiff := ih hc' hd' ha' hb' hab'
    have hrewrite :
        (∑ i ∈ insert k s, d i * ∏ j ∈ (insert k s).erase i, c j) =
        d k * (∏ j ∈ s, c j) + c k * (∑ i ∈ s, d i * ∏ j ∈ s.erase i, c j) := by
      rw [Finset.sum_insert hk, Finset.erase_insert hk, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hki : k ≠ i := fun h => hk (h ▸ hi)
      rw [Finset.erase_insert_of_ne hki, Finset.prod_insert]
      · ring
      · simp [hk]
    rw [hrewrite, Finset.prod_insert hk, Finset.prod_insert hk]
    calc
      |a k * (∏ i ∈ s, a i) - b k * (∏ i ∈ s, b i)|
          = |(a k - b k) * (∏ i ∈ s, b i) +
              a k * ((∏ i ∈ s, a i) - ∏ i ∈ s, b i)| := by ring_nf
      _ ≤ |(a k - b k) * (∏ i ∈ s, b i)| +
              |a k * ((∏ i ∈ s, a i) - ∏ i ∈ s, b i)| := abs_add_le _ _
      _ ≤ d k * (∏ i ∈ s, c i) +
              c k * (∑ i ∈ s, d i * ∏ j ∈ s.erase i, c j) := by
        simp only [abs_mul]
        exact add_le_add
          (mul_le_mul (hab k (Finset.mem_insert_self _ _)) hprod
            (abs_nonneg _) (hd k (Finset.mem_insert_self _ _)))
          (mul_le_mul (ha k (Finset.mem_insert_self _ _)) hdiff
            (abs_nonneg _) (hc k (Finset.mem_insert_self _ _)))

/-- An alternative form suited to factoring a sum over a box. -/
theorem abs_prod_sub_prod_le_sum_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b c d : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 0 ≤ d i)
    (ha : ∀ i, |a i| ≤ c i) (hb : ∀ i, |b i| ≤ c i)
    (hab : ∀ i, |a i - b i| ≤ d i) :
    |(∏ i, a i) - ∏ i, b i| ≤ ∑ i, ∏ j, if j = i then d j else c j := by
  refine (abs_prod_sub_prod_le Finset.univ a b c d
    (fun i _ => hc i) (fun i _ => hd i) (fun i _ => ha i)
    (fun i _ => hb i) (fun i _ => hab i)).trans_eq ?_
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_prod_erase Finset.univ (fun j => if j = i then d j else c j)
    (Finset.mem_univ i)]
  simp only [ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
  simp [hj]

/-- Sum of the actual product perturbations on any subset of a level box.
The right-hand side factors into one-dimensional sums of error majorants and
ordinary majorants, exactly as in the proof of Lemma 3.2. -/
theorem finite_multilinear_perturbation {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] (levels : ι → Finset κ) (retained : Finset (ι → κ))
    (hretained : retained ⊆ Fintype.piFinset levels)
    (a b c d : ι → κ → ℝ)
    (hc : ∀ i l, l ∈ levels i → 0 ≤ c i l)
    (hd : ∀ i l, l ∈ levels i → 0 ≤ d i l)
    (ha : ∀ i l, l ∈ levels i → |a i l| ≤ c i l)
    (hb : ∀ i l, l ∈ levels i → |b i l| ≤ c i l)
    (hab : ∀ i l, l ∈ levels i → |a i l - b i l| ≤ d i l) :
    |(∑ ν ∈ retained, ∏ i, a i (ν i)) - ∑ ν ∈ retained, ∏ i, b i (ν i)| ≤
      ∑ i, ∏ j, ∑ l ∈ levels j, if j = i then d j l else c j l := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ ν ∈ retained, ((∏ i, a i (ν i)) - ∏ i, b i (ν i))|
        ≤ ∑ ν ∈ retained, |(∏ i, a i (ν i)) - ∏ i, b i (ν i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ν ∈ retained, ∑ i, ∏ j, if j = i then d j (ν j) else c j (ν j) := by
      apply Finset.sum_le_sum
      intro ν hν
      have hmem := Fintype.mem_piFinset.mp (hretained hν)
      exact abs_prod_sub_prod_le_sum_prod _ _ _ _
        (fun i => hc i (ν i) (hmem i)) (fun i => hd i (ν i) (hmem i))
        (fun i => ha i (ν i) (hmem i)) (fun i => hb i (ν i) (hmem i))
        (fun i => hab i (ν i) (hmem i))
    _ ≤ ∑ ν ∈ Fintype.piFinset levels,
          ∑ i, ∏ j, if j = i then d j (ν j) else c j (ν j) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hretained
      intro ν hν _
      apply Finset.sum_nonneg
      intro i _
      apply Finset.prod_nonneg
      intro j _
      split_ifs
      · exact hd j (ν j) (Fintype.mem_piFinset.mp hν j)
      · exact hc j (ν j) (Fintype.mem_piFinset.mp hν j)
    _ = ∑ i, ∏ j, ∑ l ∈ levels j, if j = i then d j l else c j l := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact (Finset.prod_univ_sum levels (fun j l => if j = i then d j l else c j l)).symm

/-- Increments formed from a single stored sample function at every level. -/
def sampleIncrement (samples : ℕ → ℝ) : ℕ → ℝ
  | 0 => samples 0
  | l + 1 => samples (l + 1) - samples l

/-- Perturbing each stored sample by at most `ζ` gives error `ζ` at level
zero and `2ζ` at every positive level. -/
lemma sampleIncrement_error {J : ℕ} (a b : ℕ → ℝ) (ζ : ℝ)
    (hsample : ∀ l, l ≤ J → |a l - b l| ≤ ζ) (l : ℕ) (hl : l ≤ J) :
    |sampleIncrement a l - sampleIncrement b l| ≤ (if l = 0 then ζ else 2 * ζ) := by
  cases l with
  | zero => simpa only [sampleIncrement, ite_true] using hsample 0 hl
  | succ l =>
    have ha := hsample (l + 1) hl
    have hb := hsample l (Nat.le_trans (Nat.le_succ _) hl)
    simp only [sampleIncrement, Nat.succ_ne_zero, ite_false]
    calc
      _ = |(a (l + 1) - b (l + 1)) - (a l - b l)| := by congr 1; ring
      _ ≤ |a (l + 1) - b (l + 1)| + |a l - b l| := abs_sub _ _
      _ ≤ _ := by linarith

lemma sum_sampleIncrement (samples : ℕ → ℝ) (N : ℕ) :
    (∑ l ∈ Finset.range (N + 1), sampleIncrement samples l) = samples N := by
  induction N with
  | zero => simp [sampleIncrement]
  | succ N ih => rw [Finset.sum_range_succ, ih]; simp [sampleIncrement]

/-- All level vectors in the finite box `{0,…,J}^t`. -/
def levelBox (t J : ℕ) : Finset (Fin t → ℕ) :=
  Fintype.piFinset fun _ => Finset.range (J + 1)

/-- The actual total-level set retained in equation (3.4). -/
def totalLevels (t J : ℕ) : Finset (Fin t → ℕ) :=
  (levelBox t J).filter fun ν => ∑ i, ν i ≤ J

lemma totalLevels_subset_box (t J : ℕ) : totalLevels t J ⊆ levelBox t J :=
  Finset.filter_subset _ _

lemma mem_totalLevels {t J : ℕ} {ν : Fin t → ℕ} :
    ν ∈ totalLevels t J ↔ (∀ i, ν i ≤ J) ∧ ∑ i, ν i ≤ J := by
  simp only [totalLevels, levelBox, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range, Nat.lt_succ_iff]

/-- The first increment uses one sample; all positive-level increments use two. -/
def incrementError (ζ : ℝ) (l : ℕ) : ℝ := if l = 0 then ζ else 2 * ζ

lemma incrementError_nonneg {ζ : ℝ} (hζ : 0 ≤ ζ) (l : ℕ) :
    0 ≤ incrementError ζ l := by unfold incrementError; split_ifs <;> positivity

lemma sum_incrementError (J : ℕ) (ζ : ℝ) :
    (∑ l ∈ Finset.range (J + 1), incrementError ζ l) = (2 * (J : ℝ) + 1) * ζ := by
  induction J with
  | zero => simp [incrementError]
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [incrementError, Nat.succ_ne_zero, ite_false,
      Nat.cast_add, Nat.cast_one]
    ring

lemma sum_incrementError_le {J : ℕ} {ζ : ℝ} (hζ : 0 ≤ ζ) :
    (∑ l ∈ Finset.range (J + 1), incrementError ζ l) ≤ 2 * (J + 1 : ℝ) * ζ := by
  rw [sum_incrementError]
  nlinarith

/-- A common majorant for both exact and perturbed increments. -/
def incrementMajorant (B ζ : ℝ) (l : ℕ) : ℝ :=
  B * (1 / 2 : ℝ) ^ l + incrementError ζ l

lemma incrementMajorant_nonneg {B ζ : ℝ} (hB : 0 ≤ B) (hζ : 0 ≤ ζ) (l : ℕ) :
    0 ≤ incrementMajorant B ζ l :=
  add_nonneg (mul_nonneg hB (pow_nonneg (by norm_num) _)) (incrementError_nonneg hζ l)

lemma sum_incrementMajorant_le {J : ℕ} {B ζ : ℝ} (hB : 0 ≤ B) (hζ : 0 ≤ ζ)
    (hprecision : 2 * (J + 1 : ℝ) * ζ ≤ B) :
    (∑ l ∈ Finset.range (J + 1), incrementMajorant B ζ l) ≤ 3 * B := by
  simp only [incrementMajorant, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hgeom := sum_geometric_two_le (J + 1)
  have herror := sum_incrementError_le (J := J) hζ
  have hdyadic : B * (∑ l ∈ Finset.range (J + 1), (1 / 2 : ℝ) ^ l) ≤ 2 * B := by
    nlinarith
  linarith

/-- The coordinate factor in the factored perturbation sum, with the constant
`3^(t-1)` and the product of all `B_i` explicitly recovered. -/
lemma sample_factor_identity {t J : ℕ} (B ζ : Fin t → ℝ)
    (hB : ∀ i, 0 < B i) (i : Fin t) :
    (∏ j, if j = i then 2 * (J + 1 : ℝ) * ζ j else 3 * B j) =
      (2 * (J + 1 : ℝ) * 3 ^ (t - 1) * ∏ j, B j) * (ζ i / B i) := by
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => if j = i then 2 * (J + 1 : ℝ) * ζ j else 3 * B j) (Finset.mem_univ i)]
  simp only [ite_true]
  have herase :
      (∏ j ∈ Finset.univ.erase i, if j = i then 2 * (J + 1 : ℝ) * ζ j else 3 * B j) =
        3 ^ (t - 1) * (∏ j ∈ Finset.univ.erase i, B j) := by
    calc
      _ = ∏ j ∈ Finset.univ.erase i, 3 * B j := by
        apply Finset.prod_congr rfl
        intro j hj
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
        simp [hj]
      _ = _ := by simp [Finset.prod_mul_distrib, Finset.card_erase_of_mem]
  rw [herase]
  have hprod : (∏ j ∈ Finset.univ.erase i, B j) = (∏ j, B j) / B i := by
    apply (eq_div_iff (ne_of_gt (hB i))).mpr
    exact Finset.prod_erase_mul Finset.univ B (Finset.mem_univ i)
  rw [hprod]
  ring

/-- First inequality of (3.7), for the actual finite sum of products on every
retained subset of the box.  The hypotheses are the increment norm bounds
(3.3) and the sample errors, rather than the desired quadrature estimate. -/
theorem sample_perturbation_first {t J : ℕ}
    (retained : Finset (Fin t → ℕ)) (hretained : retained ⊆ levelBox t J)
    (a b : Fin t → ℕ → ℝ) (B ζ : Fin t → ℝ)
    (hB : ∀ i, 1 ≤ B i) (hζ : ∀ i, 0 ≤ ζ i)
    (hprecision : ∀ i, 2 * (J + 1 : ℝ) * ζ i ≤ B i)
    (hb : ∀ i l, l ≤ J → |b i l| ≤ B i * (1 / 2 : ℝ) ^ l)
    (hab : ∀ i l, l ≤ J → |a i l - b i l| ≤ incrementError (ζ i) l) :
    |(∑ ν ∈ retained, ∏ i, a i (ν i)) - ∑ ν ∈ retained, ∏ i, b i (ν i)| ≤
      2 * (J + 1 : ℝ) * 3 ^ (t - 1) * (∏ i, B i) * ∑ i, ζ i / B i := by
  have hB0 : ∀ i, 0 ≤ B i := fun i => le_trans (by norm_num) (hB i)
  have hBpos : ∀ i, 0 < B i := fun i => lt_of_lt_of_le (by norm_num) (hB i)
  have hmajor : ∀ i l, l ∈ Finset.range (J + 1) →
      |a i l| ≤ incrementMajorant (B i) (ζ i) l := by
    intro i l hl
    have hbound := hb i l (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl))
    have herror := hab i l (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl))
    have htri : |a i l| ≤ |a i l - b i l| + |b i l| := by
      simpa using abs_add_le (a i l - b i l) (b i l)
    exact htri.trans (add_le_add herror hbound) |>.trans_eq (by unfold incrementMajorant; ring)
  have hraw := finite_multilinear_perturbation
    (fun _ : Fin t => Finset.range (J + 1)) retained hretained a b
    (fun i => incrementMajorant (B i) (ζ i)) (fun i => incrementError (ζ i))
    (fun i l _ => incrementMajorant_nonneg (hB0 i) (hζ i) l)
    (fun i l _ => incrementError_nonneg (hζ i) l) hmajor
    (fun i l hl => (hb i l (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl))).trans
      (le_add_of_nonneg_right (incrementError_nonneg (hζ i) l)))
    (fun i l hl => hab i l (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)))
  calc
    _ ≤ ∑ i, ∏ j, ∑ l ∈ Finset.range (J + 1),
        if j = i then incrementError (ζ j) l else incrementMajorant (B j) (ζ j) l := hraw
    _ ≤ ∑ i, ∏ j, if j = i then 2 * (J + 1 : ℝ) * ζ j else 3 * B j := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.prod_le_prod
      · intro j _
        exact Finset.sum_nonneg fun l _ => by
          split_ifs
          · exact incrementError_nonneg (hζ j) l
          · exact incrementMajorant_nonneg (hB0 j) (hζ j) l
      · intro j _
        by_cases hji : j = i
        · simp only [hji, ite_true]
          exact sum_incrementError_le (hζ i)
        · simp only [hji, ite_false]
          exact sum_incrementMajorant_le (hB0 j) (hζ j) (hprecision j)
    _ = _ := by
      simp_rw [sample_factor_identity B ζ hBpos]
      rw [Finset.mul_sum]

/-- The second inequality of (3.7), expressed with any upper bound for the
sample errors (hence also their maximum). -/
theorem sample_perturbation_max_bound {t J : ℕ}
    (retained : Finset (Fin t → ℕ)) (hretained : retained ⊆ levelBox t J)
    (a b : Fin t → ℕ → ℝ) (B ζ : Fin t → ℝ) (ζmax : ℝ)
    (hB : ∀ i, 1 ≤ B i) (hζ : ∀ i, 0 ≤ ζ i) (hζmax : ∀ i, ζ i ≤ ζmax)
    (hprecision : ∀ i, 2 * (J + 1 : ℝ) * ζ i ≤ B i)
    (hb : ∀ i l, l ≤ J → |b i l| ≤ B i * (1 / 2 : ℝ) ^ l)
    (hab : ∀ i l, l ≤ J → |a i l - b i l| ≤ incrementError (ζ i) l) :
    |(∑ ν ∈ retained, ∏ i, a i (ν i)) - ∑ ν ∈ retained, ∏ i, b i (ν i)| ≤
      2 * (t : ℝ) * (J + 1 : ℝ) * 3 ^ (t - 1) * (∏ i, B i) * ζmax := by
  have hsum : (∑ i, ζ i / B i) ≤ (t : ℝ) * ζmax := by
    calc
      _ ≤ ∑ _i : Fin t, ζmax := by
        apply Finset.sum_le_sum
        intro i _
        have hBi : 0 < B i := lt_of_lt_of_le (by norm_num) (hB i)
        have hdiv : ζ i / B i ≤ ζ i := by
          rw [div_le_iff₀ hBi]
          nlinarith [hζ i, hB i]
        exact hdiv.trans (hζmax i)
      _ = _ := by simp
  have hconst : 0 ≤ 2 * (J + 1 : ℝ) * 3 ^ (t - 1) * (∏ i, B i) := by
    apply mul_nonneg
    · positivity
    · exact Finset.prod_nonneg fun i _ => le_trans (by norm_num) (hB i)
  calc
    _ ≤ 2 * (J + 1 : ℝ) * 3 ^ (t - 1) * (∏ i, B i) * ∑ i, ζ i / B i :=
      sample_perturbation_first retained hretained a b B ζ hB hζ hprecision hb hab
    _ ≤ (2 * (J + 1 : ℝ) * 3 ^ (t - 1) * (∏ i, B i)) * ((t : ℝ) * ζmax) :=
      mul_le_mul_of_nonneg_left hsum hconst
    _ = _ := by ring

/-- Equation (3.7) for the total-level sum itself. -/
theorem total_level_sample_perturbation {t J : ℕ}
    (a b : Fin t → ℕ → ℝ) (B ζ : Fin t → ℝ) (ζmax : ℝ)
    (hB : ∀ i, 1 ≤ B i) (hζ : ∀ i, 0 ≤ ζ i) (hζmax : ∀ i, ζ i ≤ ζmax)
    (hprecision : ∀ i, 2 * (J + 1 : ℝ) * ζ i ≤ B i)
    (hb : ∀ i l, l ≤ J → |b i l| ≤ B i * (1 / 2 : ℝ) ^ l)
    (hab : ∀ i l, l ≤ J → |a i l - b i l| ≤ incrementError (ζ i) l) :
    |(∑ ν ∈ totalLevels t J, ∏ i, a i (ν i)) -
        ∑ ν ∈ totalLevels t J, ∏ i, b i (ν i)| ≤
      2 * (J + 1 : ℝ) * 3 ^ (t - 1) * (∏ i, B i) * (∑ i, ζ i / B i) ∧
    |(∑ ν ∈ totalLevels t J, ∏ i, a i (ν i)) -
        ∑ ν ∈ totalLevels t J, ∏ i, b i (ν i)| ≤
      2 * (t : ℝ) * (J + 1 : ℝ) * 3 ^ (t - 1) * (∏ i, B i) * ζmax :=
  ⟨sample_perturbation_first _ (totalLevels_subset_box t J) a b B ζ hB hζ hprecision hb hab,
    sample_perturbation_max_bound _ (totalLevels_subset_box t J) a b B ζ ζmax hB hζ hζmax
      hprecision hb hab⟩

end Paper08.Quadrature
