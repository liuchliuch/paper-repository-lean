import Paper34.ConstantCase
import Paper34.SampleMedian
import Paper34.MainAlgorithm
import Paper34.LinearPrograms
import Mathlib.Tactic.Module
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card

/-!
# Appendix A.1 and the genuine total-degree restriction in A.3

The degree-zero results concern the actual polynomial-space LAD objective.
The total-degree extension uses a submodule of the actual source space, so its
optimizer queries and every iterate remain in the restricted polynomial space.
-/

open Set MeasureTheory
open scoped BigOperators

namespace Paper34.AppendixSpaces

noncomputable section

/-- The actual constant polynomial of coordinate degree zero. -/
def constantPolynomial (n : ℕ) (c : ℝ) : PolynomialSpace n 0 := by
  classical
  refine ⟨MvPolynomial.C c, ?_⟩
  rw [MvPolynomial.mem_restrictDegree_iff_sup]
  simp [MvPolynomial.degrees_C]

@[simp] lemma constantPolynomial_coefficient (n : ℕ) (c : ℝ) :
    (constantPolynomial n c).1.coeff 0 = c := by simp [constantPolynomial]

@[simp] lemma constantPolynomial_eval (n : ℕ) (c : ℝ) (x : Point n) :
    polyEval (constantPolynomial n c) x = c := by simp [polyEval, constantPolynomial]

lemma constantPolynomial_coefficient_inverse {n : ℕ} (q : PolynomialSpace n 0) :
    constantPolynomial n (q.1.coeff 0) = q := by
  apply Subtype.ext
  exact (degree_zero_eq_C q).symm

/-- The unique grid cell contains the entire finite sample batch. -/
def oneCellSamples (n M : ℕ) : CellIndex n 1 → Finset (Fin M) := fun _ => Finset.univ

/-- The actual one-cell source objective is exactly the scalar mean LAD. -/
lemma degree_zero_weightedLAD {n M : ℕ} (X : Fin M → Point n) (Y : Fin M → ℝ)
    (q : PolynomialSpace n 0) :
    weightedLAD (oneCellSamples n M) X Y q =
      (M : ℝ)⁻¹ * sampleLADSum Finset.univ Y (q.1.coeff 0) := by
  classical
  simp [weightedLAD, weightedAverage, oneCellSamples, degree_zero_eval_constant,
    sampleLADSum, CellIndex]

/-- Appendix A.1's exact native characterization: every and only median
constant is a minimizer over the actual degree-zero polynomial space. -/
theorem degree_zero_minimizer_iff_median {n M : ℕ} (hM : 0 < M)
    (X : Fin M → Point n) (Y : Fin M → ℝ) (q : PolynomialSpace n 0) :
    (∀ r : PolynomialSpace n 0, weightedLAD (oneCellSamples n M) X Y q ≤
      weightedLAD (oneCellSamples n M) X Y r) ↔
      IsSampleMedian Finset.univ Y (q.1.coeff 0) := by
  haveI : NeZero M := ⟨Nat.ne_of_gt hM⟩
  rw [sampleMedian_iff_minimizes_mean_lad Finset.univ Y (q.1.coeff 0) Finset.univ_nonempty]
  constructor
  · intro h t
    have ht := h (constantPolynomial n t)
    simpa only [degree_zero_weightedLAD, constantPolynomial_coefficient,
      Finset.card_univ, Fintype.card_fin] using ht
  · intro h r
    simpa only [degree_zero_weightedLAD, Finset.card_univ, Fintype.card_fin] using h (r.1.coeff 0)

/-- A concrete estimator for the native constant-polynomial problem; it uses
only the observed labels and sample cardinality. -/
def constantEstimator (n M : ℕ) (hM : 0 < M) (Y : Fin M → ℝ) : PolynomialSpace n 0 := by
  haveI : NeZero M := ⟨Nat.ne_of_gt hM⟩
  exact constantPolynomial n (enumeratedMedian Finset.univ Y Finset.univ_nonempty)

theorem constantEstimator_minimizes {n M : ℕ} (hM : 0 < M)
    (X : Fin M → Point n) (Y : Fin M → ℝ) :
    ∀ r : PolynomialSpace n 0,
      weightedLAD (oneCellSamples n M) X Y (constantEstimator n M hM Y) ≤
      weightedLAD (oneCellSamples n M) X Y r := by
  apply (degree_zero_minimizer_iff_median hM X Y _).mpr
  haveI : NeZero M := ⟨Nat.ne_of_gt hM⟩
  simpa [constantEstimator] using enumeratedMedian_spec Finset.univ Y Finset.univ_nonempty

/-- Every native zero-degree LAD minimizer has error at most sigma under the
actual strict-majority inlier condition. No restriction on the other labels. -/
theorem degree_zero_minimizer_error {n M : ℕ} (hM : 0 < M)
    (X : Fin M → Point n) (Y : Fin M → ℝ) (p q : PolynomialSpace n 0)
    (G : Finset (Fin M)) {sigma : ℝ} (hmajor : M < 2 * G.card)
    (hnoise : ∀ i ∈ G, |Y i - polyEval p (X i)| ≤ sigma)
    (hmin : ∀ r : PolynomialSpace n 0, weightedLAD (oneCellSamples n M) X Y q ≤
      weightedLAD (oneCellSamples n M) X Y r) :
    supNorm (q - p) ≤ sigma := by
  have hmed := (degree_zero_minimizer_iff_median hM X Y q).mp hmin
  have h := constant_median_error Y (p := p.1.coeff 0)
    (Finset.subset_univ G) (by simpa using hmajor)
    (fun i hi => by simpa only [degree_zero_eval_constant] using hnoise i hi) hmed
  obtain ⟨x, hx, heq⟩ := supNorm_attained (q-p)
  rw [← heq, polyEval_sub, degree_zero_eval_constant, degree_zero_eval_constant]
  exact h

theorem degree_zero_minimizer_exact {n M : ℕ} (hM : 0 < M)
    (X : Fin M → Point n) (Y : Fin M → ℝ) (p q : PolynomialSpace n 0)
    (G : Finset (Fin M)) (hmajor : M < 2 * G.card)
    (hnoise : ∀ i ∈ G, Y i = polyEval p (X i))
    (hmin : ∀ r : PolynomialSpace n 0, weightedLAD (oneCellSamples n M) X Y q ≤
      weightedLAD (oneCellSamples n M) X Y r) : q = p := by
  have h := degree_zero_minimizer_error hM X Y p q G hmajor
    (sigma := 0) (fun i hi => by simp [hnoise i hi]) hmin
  rw [← norm_eq_supNorm] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

/-- The actual total-degree restriction, inside the already normed source space. -/
def totalDegreeSubspace (n d : ℕ) : Submodule ℝ (PolynomialSpace n d) :=
  (MvPolynomial.restrictTotalDegree (Fin n) ℝ d).comap
    (MvPolynomial.restrictDegree (Fin n) ℝ d).subtype

lemma mem_totalDegreeSubspace {n d : ℕ} (q : PolynomialSpace n d) :
    q ∈ totalDegreeSubspace n d ↔ q.1.totalDegree ≤ d :=
  MvPolynomial.mem_restrictTotalDegree (Fin n) d q.1

/-- The restricted estimator's type is linearly equivalent to the actual
mathlib total-degree polynomial submodule, with identical underlying polynomial. -/
def totalDegreeEquiv (n d : ℕ) : totalDegreeSubspace n d ≃ₗ[ℝ]
    MvPolynomial.restrictTotalDegree (Fin n) ℝ d where
  toFun q := ⟨q.1.1, q.2⟩
  invFun q := ⟨⟨q.1, totalDegree_subspace n d q.2⟩, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Adding the slack degree gives a genuine bijection between bounded
monomial exponents and fixed-mass multisets over n+1 letters. -/
def boundedExponentEquivSym (n d : ℕ) :
    {a : Fin n →₀ ℕ // a.sum (fun _ e => e) ≤ d} ≃ Sym (Option (Fin n)) d := by
  classical
  let E : {a : Fin n →₀ ℕ // a.sum (fun _ e => e) ≤ d} ≃
      {b : Option (Fin n) → ℕ // ∑ i, b i = d} :=
    { toFun := fun a => ⟨fun i => Option.elim i (d-a.1.sum (fun _ e => e)) a.1, by
        rw [Fintype.sum_option]
        have hsum : ∑ k, a.1 k = a.1.sum (fun _ e => e) := by simp [Finsupp.sum_fintype]
        change d-a.1.sum (fun _ e => e)+(∑ k, a.1 k) = d
        rw [hsum]
        omega⟩
      invFun := fun b => ⟨Finsupp.equivFunOnFinite.symm (fun k => b.1 (some k)), by
        have hb := b.2
        rw [Fintype.sum_option] at hb
        simpa [Finsupp.sum_fintype] using (Nat.le.intro (by simpa [Nat.add_comm] using hb) :
          (∑ k, b.1 (some k)) ≤ d)⟩
      left_inv := fun a => by apply Subtype.ext; ext k; rfl
      right_inv := fun b => by
        apply Subtype.ext
        funext i
        cases i with
        | none =>
            have hb := b.2
            rw [Fintype.sum_option] at hb
            change d-(Finsupp.equivFunOnFinite.symm (fun k => b.1 (some k))).sum
              (fun _ e => e) = b.1 none
            have hsum : (Finsupp.equivFunOnFinite.symm (fun k => b.1 (some k))).sum
                (fun _ e => e) = ∑ k, b.1 (some k) := by simp [Finsupp.sum_fintype]
            rw [hsum]
            omega
        | some k => rfl }
  exact E.trans (Sym.equivNatSumOfFintype (Option (Fin n)) d).symm

/-- Exact stars-and-bars monomial count, proved from mathlib's symmetric-power
cardinality theorem. No external counting hypothesis is required. -/
theorem boundedExponent_card (n d : ℕ) :
    Nat.card {a : Fin n →₀ ℕ // a.sum (fun _ e => e) ≤ d} = (n+d).choose n := by
  rw [Nat.card_congr (boundedExponentEquivSym n d), Nat.card_eq_fintype_card,
    Sym.card_sym_eq_choose]
  simp only [Fintype.card_option, Fintype.card_fin]
  have hsum : n+1+d-1 = n+d := by omega
  rw [hsum]
  exact (Nat.choose_symm_add (a := n) (b := d)).symm

/-- Exact coefficient dimension of the actual total-degree subspace. -/
theorem totalDegree_dimension (n d : ℕ) :
    Module.finrank ℝ (totalDegreeSubspace n d) = (n+d).choose n := by
  rw [(totalDegreeEquiv n d).finrank_eq]
  let b := MvPolynomial.basisRestrictSupport ℝ
    {a : Fin n →₀ ℕ | a.sum (fun _ e => e) ≤ d}
  letI : Module.Finite ℝ (MvPolynomial.restrictSupport ℝ
      {a : Fin n →₀ ℕ | a.sum (fun _ e => e) ≤ d}) :=
    inferInstanceAs (Module.Finite ℝ (MvPolynomial.restrictTotalDegree (Fin n) ℝ d))
  have h := congrArg Cardinal.toNat (Module.mk_finrank_eq_card_basis b)
  have hdim : Module.finrank ℝ (MvPolynomial.restrictTotalDegree (Fin n) ℝ d) =
      Nat.card {a : Fin n →₀ ℕ // a.sum (fun _ e => e) ≤ d} := by
    simpa only [Cardinal.toNat_natCast, Nat.card] using h
  exact hdim.trans (boundedExponent_card n d)


/-- Every internal multiset-norming estimate restricts to the actual subspace. -/
theorem subspace_multisetNorming {n d m : ℕ} (R : Submodule ℝ (PolynomialSpace n d))
    {z : ℝ} (hnorm : MultisetNorming n d m z) (q : R)
    (A : CellIndex n m → Multiset (Point n)) (hA : ∀ j, A j ≠ 0)
    (hAC : ∀ j x, x ∈ A j → x ∈ closedCell j) :
    (1-z)*l1Norm q.1 ≤ multisetPhi A q.1 ∧ multisetPhi A q.1 ≤ (1+z)*l1Norm q.1 :=
  hnorm q.1 A hA hAC

/-- Internal sup/L¹ conversion restricts with exactly the same degree constant. -/
theorem subspace_l1_to_sup {n d : ℕ} (R : Submodule ℝ (PolynomialSpace n d))
    (hnik : L1ToSup n d) (q : R) : supNorm q.1 ≤ (2*(d : ℝ)+1)^n*l1Norm q.1 := hnik q.1

/-- Internal cell oscillation restricts with exactly the same grid constant. -/
theorem subspace_oscillation {n d m : ℕ} (R : Submodule ℝ (PolynomialSpace n d))
    {gamma : ℝ} (hosc : ∀ q : PolynomialSpace n d, CellOscillation (m := m) gamma q)
    (q : R) : CellOscillation (m := m) gamma q.1 := hosc q.1

/-- The same nonempty-grid coercive norm bound holds before restricting the
optimization domain. It depends only on the proved internal norming chain. -/
lemma lad_norm_lower {n m d : ℕ} [NeZero m] {ι : Type*}
    (D : GoodSampleGrid n m ι) (Y : ι → ℝ) {z : ℝ} (hz : z < 1)
    (hnorm : MultisetNorming n d m z) (hnik : L1ToSup n d) (q : PolynomialSpace n d) :
    ((1-z)/(2*(d : ℝ)+1)^n)*‖q‖-weightedLAD D.samples D.location Y (0 : PolynomialSpace n d) ≤
      weightedLAD D.samples D.location Y q := by
  let A := fun j => locationMultiset (D.samples j) D.location
  have hA : ∀ j, A j ≠ 0 := by
    intro j he
    have hc := congrArg Multiset.card he
    apply Finset.card_ne_zero.mpr (D.nonempty j)
    simpa [A, locationMultiset] using hc
  have hAC : ∀ j x, x ∈ A j → x ∈ closedCell j := by
    intro j x hx
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
    exact D.inside j i hi
  have hc : 0 < (1-z)/(2*(d : ℝ)+1)^n := div_pos (by linarith) (by positivity)
  have hpoint : ∀ j, ∀ i ∈ D.samples j,
      |polyEval q (D.location i)|-|Y i| ≤ |polyEval q (D.location i)-Y i| := by
    intro j i hi
    have ht : |polyEval q (D.location i)| ≤
        |polyEval q (D.location i)-Y i|+|Y i| := by
      simpa only [sub_add_cancel] using abs_add_le (polyEval q (D.location i)-Y i) (Y i)
    linarith
  have hraw := weightedAverage_mono D.samples hpoint
  rw [weightedAverage_sub, weightedEvaluation_eq_Phi] at hraw
  have hzero : weightedAverage D.samples (fun _ i => |Y i|) =
      weightedLAD D.samples D.location Y (0 : PolynomialSpace n d) := by
    simp [weightedLAD, polyEval]
  rw [hzero] at hraw
  change multisetPhi A q -
    weightedLAD D.samples D.location Y (0 : PolynomialSpace n d) ≤
      weightedLAD D.samples D.location Y q at hraw
  have hnormq := (hnorm q A hA hAC).1
  have hnikq := mul_le_mul_of_nonneg_left (hnik q) hc.le
  have hid : (1-z)/(2*(d : ℝ)+1)^n*((2*(d : ℝ)+1)^n*l1Norm q) =
      (1-z)*l1Norm q := by field_simp
  rw [hid, ← norm_eq_supNorm] at hnikq
  dsimp [A] at hnormq
  linarith

/-- The actual weighted LAD has an attained minimum on every linear subspace,
including total-degree polynomials; the labels are unrestricted. -/
theorem subspace_LAD_attains {n d m : ℕ} [NeZero m] {ι : Type*}
    (R : Submodule ℝ (PolynomialSpace n d)) (D : GoodSampleGrid n m ι) (Y : ι → ℝ)
    {z : ℝ} (hz : z < 1) (hnorm : MultisetNorming n d m z) (hnik : L1ToSup n d) :
    ∃ q : R, ∀ r : R,
      weightedLAD D.samples D.location Y q.1 ≤ weightedLAD D.samples D.location Y r.1 := by
  apply exists_min_of_lower_norm (B := weightedLAD D.samples D.location Y (0 : PolynomialSpace n d))
    ((continuous_weightedLAD D.samples D.location Y).comp continuous_subtype_val)
    (div_pos (by linarith) (by positivity) : 0 < (1-z)/(2*(d : ℝ)+1)^n)
  intro q
  exact lad_norm_lower D Y hz hnorm hnik q.1

/-- The actual minimax objective also has an attained subspace minimum. -/
theorem subspace_minimax_attains {n d m : ℕ} [NeZero m]
    (R : Submodule ℝ (PolynomialSpace n d))
    (a : CellIndex n m → Point n) (y : CellIndex n m → ℝ)
    (ha : ∀ j, a j ∈ closedCell j) {gamma : ℝ} (hg : gamma < 1)
    (hosc : ∀ q : PolynomialSpace n d, CellOscillation (m := m) gamma q) :
    ∃ r : R, ∀ q : R, representativeResidual a y r.1 ≤ representativeResidual a y q.1 := by
  apply exists_min_of_lower_norm
    ((continuous_representativeResidual a y).comp continuous_subtype_val)
    (by linarith : 0 < 1-gamma)
  intro q
  exact norm_le_residual_add_oscillation a y ha q.1 (hosc q.1)

/-- The exact-real optimizer primitive on the actual restricted domain.
Every returned value, rather than only its ambient evaluation, belongs to R. -/
structure RestrictedLPOracle {n d : ℕ} (R : Submodule ℝ (PolynomialSpace n d))
    (m : ℕ) [NeZero m] where
  solveLAD : ∀ M (S : CellIndex n m → Finset (Fin M)) (X : Fin M → Point n) (Y : Fin M → ℝ),
    (∃ q : R, ∀ r : R, weightedLAD S X Y q.1 ≤ weightedLAD S X Y r.1) → R
  lad_optimal : ∀ M (S : CellIndex n m → Finset (Fin M)) (X : Fin M → Point n) (Y : Fin M → ℝ)
    (h : ∃ q : R, ∀ r : R, weightedLAD S X Y q.1 ≤ weightedLAD S X Y r.1),
    ∀ r : R, weightedLAD S X Y (solveLAD M S X Y h).1 ≤ weightedLAD S X Y r.1
  solveMinimax : ∀ (a : CellIndex n m → Point n) (y : CellIndex n m → ℝ),
    (∃ r : R, ∀ q : R, representativeResidual a y r.1 ≤ representativeResidual a y q.1) → R
  minimax_optimal : ∀ (a : CellIndex n m → Point n) (y : CellIndex n m → ℝ)
    (h : ∃ r : R, ∀ q : R, representativeResidual a y r.1 ≤ representativeResidual a y q.1),
    ∀ q : R, representativeResidual a y (solveMinimax a y h).1 ≤ representativeResidual a y q.1

def canonicalRestrictedLPOracle {n d : ℕ} (R : Submodule ℝ (PolynomialSpace n d))
    (m : ℕ) [NeZero m] : RestrictedLPOracle R m where
  solveLAD _ _ _ _ h := Classical.choose h
  lad_optimal _ _ _ _ h := Classical.choose_spec h
  solveMinimax _ _ h := Classical.choose h
  minimax_optimal _ _ h := Classical.choose_spec h

/-- Native subspace initializer: same observed batch, same weights, restricted LP. -/
def restrictedInitial {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (R : Submodule ℝ (PolynomialSpace n d)) (O : RestrictedLPOracle R m)
    (C : RegressionAnalysis n d m rho) (D : ObservedGrid n m M)
    (hN : ∀ j, (D.samples j).Nonempty) : R :=
  O.solveLAD M D.samples D.location D.label
    (subspace_LAD_attains R (D.toGood hN (fun _ => False)) D.label
      C.accuracy_lt_one C.norming C.l1_to_sup)

/-- Native subspace minimax correction with the actual residual medians. -/
def restrictedCorrection {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (R : Submodule ℝ (PolynomialSpace n d)) (O : RestrictedLPOracle R m)
    (C : RegressionAnalysis n d m rho) (D : ObservedGrid n m M)
    (hN : ∀ j, (D.samples j).Nonempty) (q : R) : R :=
  O.solveMinimax (D.representative hN) (D.residualMedians hN q.1)
    (subspace_minimax_attains R _ _ (D.representative_inside hN) C.gamma_lt_one C.oscillation)

structure RestrictedState {n d : ℕ} (R : Submodule ℝ (PolynomialSpace n d)) where
  estimate : R
  oracleCalls : ℕ

def restrictedIteration {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (R : Submodule ℝ (PolynomialSpace n d)) (O : RestrictedLPOracle R m)
    (C : RegressionAnalysis n d m rho) (D : ObservedGrid n m M)
    (hN : ∀ j, (D.samples j).Nonempty) : ℕ → RestrictedState R
  | 0 => ⟨restrictedInitial R O C D hN, 1⟩
  | t+1 => let s := restrictedIteration R O C D hN t
    ⟨s.estimate + restrictedCorrection R O C D hN s.estimate, s.oracleCalls+1⟩

/-- Every iterate lies in R by construction; the source oracle budget is unchanged. -/
theorem restrictedIteration_calls {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (R : Submodule ℝ (PolynomialSpace n d)) (O : RestrictedLPOracle R m)
    (C : RegressionAnalysis n d m rho) (D : ObservedGrid n m M)
    (hN : ∀ j, (D.samples j).Nonempty) (T : ℕ) :
    (restrictedIteration R O C D hN T).oracleCalls = 1+T := by
  induction T with
  | zero => rfl
  | succ t ih => simp [restrictedIteration, ih, Nat.add_assoc]

/-- The complete restricted estimator, including the same empty-cell branch. -/
def runRestricted {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (R : Submodule ℝ (PolynomialSpace n d)) (O : RestrictedLPOracle R m)
    (C : RegressionAnalysis n d m rho) (D : ObservedGrid n m M) (T : ℕ) : RestrictedState R := by
  classical
  exact if hN : ∀ j, (D.samples j).Nonempty then restrictedIteration R O C D hN T else ⟨0,0⟩

/-- In particular, this estimator's output has actual total degree at most d. -/
theorem runRestricted_totalDegree {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (O : RestrictedLPOracle (totalDegreeSubspace n d) m)
    (C : RegressionAnalysis n d m rho) (D : ObservedGrid n m M) (T : ℕ) :
    (runRestricted (totalDegreeSubspace n d) O C D T).estimate.1.1.totalDegree ≤ d :=
  (mem_totalDegreeSubspace _).mp (runRestricted (totalDegreeSubspace n d) O C D T).estimate.2


/-- Exact LAD optimality is over R itself. -/
theorem restrictedInitial_optimal {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (R : Submodule ℝ (PolynomialSpace n d)) (O : RestrictedLPOracle R m)
    (C : RegressionAnalysis n d m rho) (D : ObservedGrid n m M)
    (hN : ∀ j, (D.samples j).Nonempty) :
    ∀ r : R, weightedLAD D.samples D.location D.label (restrictedInitial R O C D hN).1 ≤
      weightedLAD D.samples D.location D.label r.1 :=
  O.lad_optimal _ _ _ _ _

/-- Exact minimax optimality is over R itself. -/
theorem restrictedCorrection_optimal {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (R : Submodule ℝ (PolynomialSpace n d)) (O : RestrictedLPOracle R m)
    (C : RegressionAnalysis n d m rho) (D : ObservedGrid n m M)
    (hN : ∀ j, (D.samples j).Nonempty) (q : R) :
    ∀ r : R, representativeResidual (D.representative hN) (D.residualMedians hN q.1)
      (restrictedCorrection R O C D hN q).1 ≤
      representativeResidual (D.representative hN) (D.residualMedians hN q.1) r.1 :=
  O.minimax_optimal _ _ _

/-- The source initialization bound needs only the feasible competitor p,
which belongs to the same restricted optimization domain as q. -/
theorem subspace_initializer_error {n m d : ℕ} [NeZero m] {ι : Type*}
    (R : Submodule ℝ (PolynomialSpace n d))
    (D : GoodSampleGrid n m ι) (Y : ι → ℝ) (p q : R)
    {rho sigma : ℝ} (hr0 : 0 ≤ rho) (hr : rho < 1/2) (hs : 0 ≤ sigma)
    (hgood : D.GoodAt rho)
    (hnoise : ∀ j, ∀ i ∈ D.samples j, D.inlier i → |polyEval p.1 (D.location i)-Y i| ≤ sigma)
    (hnorm : MultisetNorming n d m (zeta rho)) (hnik : L1ToSup n d)
    (hmin : ∀ r : R, weightedLAD D.samples D.location Y q.1 ≤
      weightedLAD D.samples D.location Y r.1) :
    l1Norm (q.1-p.1) ≤ 4*sigma/gap rho ∧
      supNorm (q.1-p.1) ≤ initializationFactor n d rho*sigma := by
  have hg : 0 < gap rho := by unfold gap; linarith
  have hraw := coercive_lad_lower D Y p.1 (q.1-p.1) hr0 hr hs hgood hnoise hnorm
  have heq : p.1+(q.1-p.1) = q.1 := by module
  rw [heq] at hraw
  have hcomp := hmin p
  have hL : l1Norm (q.1-p.1) ≤ 4*sigma/gap rho := by
    apply (le_div_iff₀ hg).mpr
    nlinarith
  refine ⟨hL, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hL
    (by positivity : 0 ≤ (2*(d : ℝ)+1)^n)
  calc
    supNorm (q.1-p.1) ≤ (2*(d : ℝ)+1)^n*l1Norm (q.1-p.1) := hnik (q.1-p.1)
    _ ≤ (2*(d : ℝ)+1)^n*(4*sigma/gap rho) := hmul
    _ = initializationFactor n d rho*sigma := by unfold initializationFactor; ring

/-- The refinement argument only compares the optimizer to the true residual.
This form applies unchanged when minimization is restricted to a subspace. -/
theorem one_step_of_competitor {n d m : ℕ} [NeZero m]
    (e r : PolynomialSpace n d) (a : CellIndex n m → Point n)
    (y : CellIndex n m → ℝ) {sigma gamma b : ℝ}
    (ha : ∀ j, a j ∈ closedCell j)
    (hwitness : ∀ j, ∃ z ∈ closedCell j, |polyEval e z-y j| ≤ sigma)
    (heosc : CellOscillation (m := m) gamma e)
    (hrosc : CellOscillation (m := m) gamma (r-e))
    (hcomp : representativeResidual a y r ≤ representativeResidual a y e)
    (hs : 0 ≤ sigma) (hb : 0 ≤ b) (hg0 : 0 ≤ gamma)
    (hg : gamma ≤ b/(2+b)) :
    supNorm (r-e) ≤ (2+b)*sigma+b*supNorm e := by
  have heval : ∀ j, |polyEval e (a j)-y j| ≤ sigma+gamma*supNorm e := by
    intro j
    obtain ⟨z, hz, hw⟩ := hwitness j
    calc |polyEval e (a j)-y j| ≤
        |polyEval e (a j)-polyEval e z|+|polyEval e z-y j| := abs_sub_le _ _ _
      _ ≤ gamma*supNorm e+sigma := add_le_add (heosc j (a j) z (ha j) hz) hw
      _ = sigma+gamma*supNorm e := add_comm _ _
  have hrval : ∀ j, |polyEval r (a j)-y j| ≤ sigma+gamma*supNorm e := by
    intro j
    exact (representative_le_residual a y r j).trans
      (hcomp.trans (residual_le_of_forall a y e heval))
  have hdiff : ∀ j, |polyEval (r-e) (a j)| ≤ 2*sigma+2*gamma*supNorm e := by
    intro j
    rw [polyEval_sub]
    calc |polyEval r (a j)-polyEval e (a j)| ≤
        |polyEval r (a j)-y j|+|y j-polyEval e (a j)| := abs_sub_le _ _ _
      _ = |polyEval r (a j)-y j|+|polyEval e (a j)-y j| := by rw [abs_sub_comm (y j)]
      _ ≤ (sigma+gamma*supNorm e)+(sigma+gamma*supNorm e) := add_le_add (hrval j) (heval j)
      _ = 2*sigma+2*gamma*supNorm e := by ring
  obtain ⟨x, hx, hmax⟩ := supNorm_attained (r-e)
  obtain ⟨j, hj⟩ := cube_covered_by_closedCells (NeZero.pos m) x hx
  have hraw : supNorm (r-e) ≤ 2*sigma+2*gamma*supNorm e+gamma*supNorm (r-e) := by
    calc supNorm (r-e) = |polyEval (r-e) x| := hmax.symm
      _ ≤ |polyEval (r-e) (a j)|+|polyEval (r-e) x-polyEval (r-e) (a j)| := by
        calc |polyEval (r-e) x| =
            |polyEval (r-e) (a j)+(polyEval (r-e) x-polyEval (r-e) (a j))| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      _ ≤ (2*sigma+2*gamma*supNorm e)+gamma*supNorm (r-e) :=
        add_le_add (hdiff j) (hrosc j x (a j) hj (ha j))
  exact absorb_oscillation (supNorm_nonneg _) (supNorm_nonneg _) hs hb hg0 hg hraw

/-- Actual median witnesses and restricted exact minimization give the same
one-step contraction as in the coordinate-degree space. -/
theorem restrictedCorrection_contracts {n d m M : ℕ} [NeZero m] {rho eps sigma : ℝ}
    (R : Submodule ℝ (PolynomialSpace n d)) (O : RestrictedLPOracle R m)
    (C : RegressionAnalysis n d m rho) (D : ObservedGrid n m M)
    (hN : ∀ j, (D.samples j).Nonempty)
    (inlier : Fin M → Prop) [DecidablePred inlier] (p q : R)
    (hr : rho < 1/2) (hs : 0 ≤ sigma) (hb : 0 ≤ beta eps)
    (hg0 : 0 ≤ C.gamma) (hg : C.gamma ≤ beta eps/(2+beta eps))
    (hgood : (D.toGood hN inlier).GoodAt rho)
    (hnoise : ∀ j, ∀ i ∈ D.samples j, inlier i → |polyEval p.1 (D.location i)-D.label i| ≤ sigma) :
    supNorm (q.1+(restrictedCorrection R O C D hN q).1-p.1) ≤
      (2+beta eps)*sigma+beta eps*supNorm (q.1-p.1) := by
  let E := D.toGood hN inlier
  let Z : Fin M → ℝ := fun i => D.label i-polyEval q.1 (D.location i)
  have hn : ∀ j, ∀ i ∈ E.good j, |Z i-polyEval (p.1-q.1) (D.location i)| ≤ sigma := by
    intro j i hi
    have hh := hnoise j i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
    dsimp [Z]
    rw [polyEval_sub]
    rw [show (D.label i-polyEval q.1 (D.location i))-
      (polyEval p.1 (D.location i)-polyEval q.1 (D.location i)) =
      -(polyEval p.1 (D.location i)-D.label i) by ring, abs_neg]
    exact hh
  have hw : ∀ j, ∃ z ∈ closedCell j,
      |polyEval (p.1-q.1) z-D.residualMedians hN q.1 j| ≤ sigma := by
    intro j
    exact median_witness j (p.1-q.1) D.location Z (Finset.filter_subset _ _)
      (E.good_strict_majority hr hgood j) (D.inside j) (hn j)
      (enumeratedMedian_spec (D.samples j) Z (hN j))
  have h := one_step_of_competitor (p.1-q.1) (restrictedCorrection R O C D hN q).1
    (D.representative hN) (D.residualMedians hN q.1) (D.representative_inside hN)
    hw (C.oscillation _) (C.oscillation _)
    (restrictedCorrection_optimal R O C D hN q (p-q)) hs hb hg0 hg
  have heq : q.1+(restrictedCorrection R O C D hN q).1-p.1 =
      (restrictedCorrection R O C D hN q).1-(p.1-q.1) := by module
  rw [heq]
  have hrev : supNorm (p.1-q.1) = supNorm (q.1-p.1) := by
    simpa only [← norm_eq_supNorm] using norm_sub_rev p.1 q.1
  simpa only [hrev] using h


/-- The same recurrence and error constants hold for every exact restricted
oracle trajectory, with no full-space optimality premise. -/
theorem restrictedIteration_error {n d m M : ℕ} [NeZero m] {rho eps sigma : ℝ}
    (R : Submodule ℝ (PolynomialSpace n d)) (O : RestrictedLPOracle R m)
    (C : RegressionAnalysis n d m rho) (D : ObservedGrid n m M)
    (hN : ∀ j, (D.samples j).Nonempty)
    (inlier : Fin M → Prop) [DecidablePred inlier] (p : R)
    (hr0 : 0 ≤ rho) (hr : rho < 1/2) (he0 : 0 < eps) (he : eps ≤ 1/2)
    (hs : 0 ≤ sigma) (hg0 : 0 ≤ C.gamma) (hg : C.gamma ≤ beta eps/(2+beta eps))
    (hgood : (D.toGood hN inlier).GoodAt rho)
    (hnoise : ∀ j, ∀ i ∈ D.samples j, inlier i → |polyEval p.1 (D.location i)-D.label i| ≤ sigma)
    (T : ℕ) (hT : beta eps^T*initializationFactor n d rho ≤ eps/2) :
    supNorm ((restrictedIteration R O C D hN T).estimate.1-p.1) ≤ (2+eps)*sigma := by
  let error : ℕ → ℝ := fun t => supNorm ((restrictedIteration R O C D hN t).estimate.1-p.1)
  have hinit : error 0 ≤ initializationFactor n d rho*sigma :=
    (subspace_initializer_error R (D.toGood hN inlier) D.label p (restrictedInitial R O C D hN)
      hr0 hr hs hgood hnoise C.norming C.l1_to_sup (restrictedInitial_optimal R O C D hN)).2
  have hb : 0 ≤ beta eps := by unfold beta; positivity
  have hstep : ∀ t, error (t+1) ≤ (2+beta eps)*sigma+beta eps*error t := by
    intro t
    exact restrictedCorrection_contracts R O C D hN inlier p
      (restrictedIteration R O C D hN t).estimate hr hs hb hg0 hg hgood hnoise
  exact target_of_recurrence error hs he0 he hinit hstep T hT

/-- Appendix A.3's genuine restricted estimator uses the same sample batch,
grid, and refinement budget and has the same pure multiplicative error. -/
theorem runRestricted_error_on_good_grid {n d m M : ℕ} [NeZero m] {rho eps sigma : ℝ}
    (R : Submodule ℝ (PolynomialSpace n d)) (O : RestrictedLPOracle R m)
    (C : RegressionAnalysis n d m rho) (D : ObservedGrid n m M)
    (hN : ∀ j, (D.samples j).Nonempty)
    (inlier : Fin M → Prop) [DecidablePred inlier] (p : R)
    (hr0 : 0 ≤ rho) (hr : rho < 1/2) (he0 : 0 < eps) (he : eps ≤ 1/2)
    (hs : 0 ≤ sigma) (hg0 : 0 ≤ C.gamma) (hg : C.gamma ≤ beta eps/(2+beta eps))
    (hgood : (D.toGood hN inlier).GoodAt rho)
    (hnoise : ∀ j, ∀ i ∈ D.samples j, inlier i → |polyEval p.1 (D.location i)-D.label i| ≤ sigma) :
    supNorm ((runRestricted R O C D (refinementBudget n d rho eps he0 he)).estimate.1-p.1) ≤
      (2+eps)*sigma := by
  classical
  simp only [runRestricted, dif_pos hN]
  exact restrictedIteration_error R O C D hN inlier p hr0 hr he0 he hs hg0 hg hgood hnoise _
    (refinementBudget_spec n d rho eps he0 he)

/-- Zero-noise recovery is equality in the actual restricted polynomial space. -/
theorem runRestricted_exact_on_good_grid {n d m M : ℕ} [NeZero m] {rho eps : ℝ}
    (R : Submodule ℝ (PolynomialSpace n d)) (O : RestrictedLPOracle R m)
    (C : RegressionAnalysis n d m rho) (D : ObservedGrid n m M)
    (hN : ∀ j, (D.samples j).Nonempty)
    (inlier : Fin M → Prop) [DecidablePred inlier] (p : R)
    (hr0 : 0 ≤ rho) (hr : rho < 1/2) (he0 : 0 < eps) (he : eps ≤ 1/2)
    (hg0 : 0 ≤ C.gamma) (hg : C.gamma ≤ beta eps/(2+beta eps))
    (hgood : (D.toGood hN inlier).GoodAt rho)
    (hnoise : ∀ j, ∀ i ∈ D.samples j, inlier i → polyEval p.1 (D.location i) = D.label i) :
    (runRestricted R O C D (refinementBudget n d rho eps he0 he)).estimate = p := by
  have h := runRestricted_error_on_good_grid R O C D hN inlier p hr0 hr he0 he (le_refl 0)
    hg0 hg hgood (fun j i hi hg => by simp [hnoise j i hi hg])
  simp only [mul_zero] at h
  rw [← norm_eq_supNorm] at h
  apply Subtype.ext
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

/-- The LP-call budget is unchanged, including the empty-cell branch. -/
theorem runRestricted_calls_le {n d m M : ℕ} [NeZero m] {rho : ℝ}
    (R : Submodule ℝ (PolynomialSpace n d)) (O : RestrictedLPOracle R m)
    (C : RegressionAnalysis n d m rho) (D : ObservedGrid n m M) (T : ℕ) :
    (runRestricted R O C D T).oracleCalls ≤ 1+T := by
  classical
  unfold runRestricted
  split_ifs with hN
  · exact le_of_eq (restrictedIteration_calls R O C D hN T)
  · exact Nat.zero_le _

/-- A real coefficient vector parameterizes precisely R, not the ambient
coordinate-degree polynomial space. -/
def subspaceCoefficientEquiv {n d : ℕ} (R : Submodule ℝ (PolynomialSpace n d)) :
    R ≃ₗ[ℝ] (Fin (Module.finrank ℝ R) → ℝ) :=
  (Module.finBasis ℝ R).equivFun

def subspacePolynomial {n d : ℕ} (R : Submodule ℝ (PolynomialSpace n d))
    (c : Fin (Module.finrank ℝ R) → ℝ) : R := (subspaceCoefficientEquiv R).symm c

/-- Every restricted polynomial, including every oracle optimizer, has a
coefficient encoding with precisely finrank R coordinates. -/
theorem subspacePolynomial_surjective {n d : ℕ} (R : Submodule ℝ (PolynomialSpace n d)) :
    Function.Surjective (subspacePolynomial R) := (subspaceCoefficientEquiv R).symm.surjective

/-- Evaluation is linear in these restricted coefficients, so the absolute
residual inequalities are actual linear-program inequalities on R. -/
def subspaceCoefficientEval {n d : ℕ} (R : Submodule ℝ (PolynomialSpace n d)) (x : Point n) :
    (Fin (Module.finrank ℝ R) → ℝ) →ₗ[ℝ] ℝ :=
  { toFun := fun c => polyEval (subspacePolynomial R c).1 x
    map_add' := fun c b => by simp [subspacePolynomial, polyEval_add]
    map_smul' := fun t c => by simp [subspacePolynomial, polyEval] }


abbrev RestrictedInitializerVariable {n d : ℕ} (R : Submodule ℝ (PolynomialSpace n d))
    (M : ℕ) := Sum (Fin (Module.finrank ℝ R)) (Fin M)

abbrev RestrictedRefinementVariable {n d : ℕ} (R : Submodule ℝ (PolynomialSpace n d)) :=
  Option (Fin (Module.finrank ℝ R))

def restrictedInitializerConstraint {n d M : ℕ} (R : Submodule ℝ (PolynomialSpace n d))
    (X : Fin M → Point n) (Y : Fin M → ℝ)
    (v : RestrictedInitializerVariable R M → ℝ) (row : InitializerRow M) : Prop :=
  if row.2 then subspaceCoefficientEval R (X row.1) (fun a => v (Sum.inl a))-Y row.1 ≤ v (Sum.inr row.1)
  else -v (Sum.inr row.1) ≤ subspaceCoefficientEval R (X row.1) (fun a => v (Sum.inl a))-Y row.1

/-- The restricted initializer is still a linear program with the same two
residual inequalities per observation. -/
theorem restrictedInitializer_constraints_iff {n d M : ℕ}
    (R : Submodule ℝ (PolynomialSpace n d)) (X : Fin M → Point n) (Y : Fin M → ℝ)
    (v : RestrictedInitializerVariable R M → ℝ) :
    (∀ row, restrictedInitializerConstraint R X Y v row) ↔
      ∀ i, |polyEval (subspacePolynomial R (fun a => v (Sum.inl a))).1 (X i)-Y i| ≤ v (Sum.inr i) := by
  constructor
  · intro h i
    exact abs_le.mpr ⟨by simpa [restrictedInitializerConstraint, subspaceCoefficientEval] using h (i, false),
      by simpa [restrictedInitializerConstraint, subspaceCoefficientEval] using h (i, true)⟩
  · intro h row
    rcases row with ⟨i,b⟩
    cases b with
    | false => simpa [restrictedInitializerConstraint, subspaceCoefficientEval] using (abs_le.mp (h i)).1
    | true => simpa [restrictedInitializerConstraint, subspaceCoefficientEval] using (abs_le.mp (h i)).2

def restrictedInitializerObjective {n d m M : ℕ}
    (R : Submodule ℝ (PolynomialSpace n d)) (S : CellIndex n m → Finset (Fin M))
    (v : RestrictedInitializerVariable R M → ℝ) : ℝ :=
  weightedAverage S (fun _ i => v (Sum.inr i))

def restrictedInitializerWitness {n d M : ℕ} (R : Submodule ℝ (PolynomialSpace n d))
    (X : Fin M → Point n) (Y : Fin M → ℝ) (q : R) : RestrictedInitializerVariable R M → ℝ :=
  Sum.elim (subspaceCoefficientEquiv R q) (fun i => |polyEval q.1 (X i)-Y i|)

@[simp] theorem restrictedInitializerWitness_polynomial {n d M : ℕ}
    (R : Submodule ℝ (PolynomialSpace n d)) (X : Fin M → Point n) (Y : Fin M → ℝ) (q : R) :
    subspacePolynomial R (fun a => restrictedInitializerWitness R X Y q (Sum.inl a)) = q := by
  simp [restrictedInitializerWitness, subspacePolynomial]

theorem restrictedInitializerWitness_feasible {n d M : ℕ}
    (R : Submodule ℝ (PolynomialSpace n d)) (X : Fin M → Point n) (Y : Fin M → ℝ) (q : R) :
    ∀ row, restrictedInitializerConstraint R X Y (restrictedInitializerWitness R X Y q) row := by
  apply (restrictedInitializer_constraints_iff R X Y _).mpr
  simp [restrictedInitializerWitness, subspacePolynomial]

@[simp] theorem restrictedInitializerWitness_objective {n d m M : ℕ}
    (R : Submodule ℝ (PolynomialSpace n d)) (S : CellIndex n m → Finset (Fin M))
    (X : Fin M → Point n) (Y : Fin M → ℝ) (q : R) :
    restrictedInitializerObjective R S (restrictedInitializerWitness R X Y q) = weightedLAD S X Y q.1 := rfl

/-- A solution of the explicit restricted coefficient LP is a minimizer of
the actual restricted source LAD objective. -/
theorem restrictedInitializerLP_to_minimizer {n d m M : ℕ}
    (R : Submodule ℝ (PolynomialSpace n d)) (S : CellIndex n m → Finset (Fin M))
    (X : Fin M → Point n) (Y : Fin M → ℝ) (v : RestrictedInitializerVariable R M → ℝ)
    (hfeas : ∀ row, restrictedInitializerConstraint R X Y v row)
    (hmin : ∀ w, (∀ row, restrictedInitializerConstraint R X Y w row) →
      restrictedInitializerObjective R S v ≤ restrictedInitializerObjective R S w) :
    ∀ r : R, weightedLAD S X Y (subspacePolynomial R (fun a => v (Sum.inl a))).1 ≤ weightedLAD S X Y r.1 := by
  intro r
  have h := (restrictedInitializer_constraints_iff R X Y v).mp hfeas
  calc
    weightedLAD S X Y (subspacePolynomial R (fun a => v (Sum.inl a))).1 ≤
        restrictedInitializerObjective R S v := weightedAverage_mono S (fun _ i _ => h i)
    _ ≤ restrictedInitializerObjective R S (restrictedInitializerWitness R X Y r) :=
      hmin _ (restrictedInitializerWitness_feasible R X Y r)
    _ = weightedLAD S X Y r.1 := rfl

def restrictedRefinementConstraint {n d m : ℕ} (R : Submodule ℝ (PolynomialSpace n d))
    (a : CellIndex n m → Point n) (y : CellIndex n m → ℝ)
    (v : RestrictedRefinementVariable R → ℝ) (row : RefinementRow n m) : Prop :=
  if row.2 then subspaceCoefficientEval R (a row.1) (fun k => v (some k))-y row.1 ≤ v none
  else -v none ≤ subspaceCoefficientEval R (a row.1) (fun k => v (some k))-y row.1

/-- The restricted minimax LP has the same two residual inequalities per cell. -/
theorem restrictedRefinement_constraints_iff {n d m : ℕ} [NeZero m]
    (R : Submodule ℝ (PolynomialSpace n d)) (a : CellIndex n m → Point n) (y : CellIndex n m → ℝ)
    (v : RestrictedRefinementVariable R → ℝ) :
    (∀ row, restrictedRefinementConstraint R a y v row) ↔
      representativeResidual a y (subspacePolynomial R (fun k => v (some k))).1 ≤ v none := by
  constructor
  · intro h
    apply residual_le_of_forall
    intro j
    exact abs_le.mpr ⟨by simpa [restrictedRefinementConstraint, subspaceCoefficientEval] using h (j,false),
      by simpa [restrictedRefinementConstraint, subspaceCoefficientEval] using h (j,true)⟩
  · intro h row
    have hj := (representative_le_residual a y (subspacePolynomial R (fun k => v (some k))).1 row.1).trans h
    rcases row with ⟨j,b⟩
    cases b with
    | false => simpa [restrictedRefinementConstraint, subspaceCoefficientEval] using (abs_le.mp hj).1
    | true => simpa [restrictedRefinementConstraint, subspaceCoefficientEval] using (abs_le.mp hj).2

def restrictedRefinementWitness {n d m : ℕ} [NeZero m]
    (R : Submodule ℝ (PolynomialSpace n d)) (a : CellIndex n m → Point n) (y : CellIndex n m → ℝ)
    (q : R) : RestrictedRefinementVariable R → ℝ :=
  fun k => Option.elim k (representativeResidual a y q.1) (subspaceCoefficientEquiv R q)

@[simp] theorem restrictedRefinementWitness_polynomial {n d m : ℕ} [NeZero m]
    (R : Submodule ℝ (PolynomialSpace n d)) (a : CellIndex n m → Point n) (y : CellIndex n m → ℝ) (q : R) :
    subspacePolynomial R (fun k => restrictedRefinementWitness R a y q (some k)) = q := by
  simp [restrictedRefinementWitness, subspacePolynomial]

theorem restrictedRefinementWitness_feasible {n d m : ℕ} [NeZero m]
    (R : Submodule ℝ (PolynomialSpace n d)) (a : CellIndex n m → Point n) (y : CellIndex n m → ℝ) (q : R) :
    ∀ row, restrictedRefinementConstraint R a y (restrictedRefinementWitness R a y q) row := by
  apply (restrictedRefinement_constraints_iff R a y _).mpr
  simp [restrictedRefinementWitness, subspacePolynomial]

/-- A solution of the explicit restricted coefficient minimax LP is an actual
minimizer over the restricted source polynomial space. -/
theorem restrictedRefinementLP_to_minimizer {n d m : ℕ} [NeZero m]
    (R : Submodule ℝ (PolynomialSpace n d)) (a : CellIndex n m → Point n) (y : CellIndex n m → ℝ)
    (v : RestrictedRefinementVariable R → ℝ)
    (hfeas : ∀ row, restrictedRefinementConstraint R a y v row)
    (hmin : ∀ w, (∀ row, restrictedRefinementConstraint R a y w row) → v none ≤ w none) :
    ∀ r : R, representativeResidual a y (subspacePolynomial R (fun k => v (some k))).1 ≤
      representativeResidual a y r.1 := by
  intro r
  exact ((restrictedRefinement_constraints_iff R a y v).mp hfeas).trans
    (hmin _ (restrictedRefinementWitness_feasible R a y r))

/-- Exact coefficient-block replacement in both LPs of Appendix A.3; all
sample and cell residual-row counts are unchanged. -/
theorem totalDegree_lp_counts (n d m M : ℕ) :
    Fintype.card (RestrictedInitializerVariable (totalDegreeSubspace n d) M) = (n+d).choose n+M ∧
    Fintype.card (InitializerRow M) = 2*M ∧
    Fintype.card (RestrictedRefinementVariable (totalDegreeSubspace n d)) = (n+d).choose n+1 ∧
    Fintype.card (RefinementRow n m) = 2*m^n := by
  simp [RestrictedInitializerVariable, RestrictedRefinementVariable, InitializerRow,
    RefinementRow, CellIndex, totalDegree_dimension, Nat.mul_comm]

/-- The actual Lemma 3.3 estimate restricts without changing its grid or law. -/
theorem totalDegree_lemma_3_3 {n d m : ℕ} (hd : 1 ≤ d) (hm : d ≤ m)
    (q : totalDegreeSubspace n d) (xi : CellIndex n m → Point n) (hxi : IsCellRepresentative xi) :
    (∫ x, |polyEval q.1 x-representativeStep q.1 xi x| ∂chebyshevLaw n) ≤
      arbitraryRepresentativeConstant n*(d : ℝ)/m*l1Norm q.1 := lemma_3_3 hd hm q.1 xi hxi

end

end Paper34.AppendixSpaces
