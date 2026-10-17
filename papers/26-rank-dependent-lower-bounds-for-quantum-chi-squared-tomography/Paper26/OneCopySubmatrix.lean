import Paper26.OneCopyObservation
import Paper26.MeasurableSpectralSelection
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.Probability.Independence.Basic

/-!
# Spectral truncation for the actual one-copy submatrix routine

The Weyl input below is only the standard eigenvalue perturbation theorem for
arbitrary Hermitian matrices. The actual positive rank truncation and every
matrix error conclusion are constructed and proved here.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory
namespace Paper26.OneCopySubmatrix
open QuantumModel
open OneCopyObservation

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

local instance : CStarAlgebra (Matrix ι ι ℂ) where

/-- The standard raw Hermitian Weyl eigenvalue perturbation inequality. It has
no rank truncation, estimator, probability, or P26 error conclusion in its interface. -/
structure WeylEigenvalueInput (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop where
  perturbation : ∀ (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (i : Fin (Fintype.card ι)),
    |hA.eigenvalues₀ i - hB.eigenvalues₀ i| ≤ operatorNorm (A - B)

/-- The index map used by mathlib's actual chosen ordered Hermitian eigenbasis. -/
def orderedIndex : ι ≃ Fin (Fintype.card ι) :=
  (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm

lemma eigenvalues_ordered (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (i : ι) :
    hA.eigenvalues i = hA.eigenvalues₀ (orderedIndex i) := rfl

/-- Retain only the first r ordered eigenvalues and replace negative ones by 0. -/
def truncatedSpectrum (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (r : ℕ) (i : ι) : ℝ :=
  if (orderedIndex i).val < r then max (hA.eigenvalues i) 0 else 0

/-- The actual matrix output in the chosen ordered spectral basis. -/
def rankTruncation (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (r : ℕ) : Matrix ι ι ℂ :=
  Normalization.conjugate (hA.eigenvectorUnitary : Matrix ι ι ℂ)
    (Normalization.diagonalMatrix (truncatedSpectrum A hA r))

lemma truncatedSpectrum_nonneg (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (r : ℕ) (i : ι) :
    0 ≤ truncatedSpectrum A hA r i := by
  unfold truncatedSpectrum
  split_ifs
  · exact le_max_right _ _
  · exact le_rfl

lemma rankTruncation_posSemidef (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (r : ℕ) :
    (rankTruncation A hA r).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℂ) ≤ (truncatedSpectrum A hA r i : ℂ)
  exact_mod_cast truncatedSpectrum_nonneg A hA r i

lemma rankTruncation_rank (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (r : ℕ) :
    (rankTruncation A hA r).rank ≤ r := by
  let d : ι → ℂ := fun i => (truncatedSpectrum A hA r i : ℂ)
  have hs : ∀ i, d i ≠ 0 → (orderedIndex i).val < r := by
    intro i hi
    by_contra h
    exact hi (by simp [d, truncatedSpectrum, h])
  let f : {i // d i ≠ 0} → Fin r := fun i => ⟨(orderedIndex i.val).val, hs i.val i.property⟩
  have hf : Function.Injective f := by
    intro i j h
    apply Subtype.ext
    apply orderedIndex.injective
    apply Fin.ext
    exact congrArg (fun z : Fin r => z.val) h
  have hc : Fintype.card {i // d i ≠ 0} ≤ r := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
  calc
    (rankTruncation A hA r).rank ≤ (Matrix.diagonal d).rank :=
      (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    _ = Fintype.card {i // d i ≠ 0} := Matrix.rank_diagonal d
    _ ≤ r := hc

lemma spectral_frobeniusSq (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ShellAccounting.frobeniusSq A = ∑ i, hA.eigenvalues i ^ 2 := by
  let U := hA.eigenvectorUnitary
  have he : A = Normalization.conjugate (U : Matrix ι ι ℂ)
      (Normalization.diagonalMatrix hA.eigenvalues) := by
    simpa only [U, Normalization.conjugate, Normalization.diagonalMatrix,
      Function.comp_def, Matrix.star_eq_conjTranspose] using hA.spectral_theorem
  conv_lhs => rw [he]
  unfold Normalization.conjugate
  have hus : (U : Matrix ι ι ℂ)ᴴ * ((U : Matrix ι ι ℂ)ᴴ)ᴴ = 1 := by
    simpa only [Matrix.conjTranspose_conjTranspose] using PositiveLossBridge.unitary_left U
  rw [ShellAccounting.frobeniusSq_mul_unitary _ _ hus,
    ShellAccounting.frobeniusSq_unitary_mul _ _ (PositiveLossBridge.unitary_left U),
    CollectiveSubmatrix.frobeniusSq_diagonal]

/-- The standard rank factor is proved on the actual Hermitian matrix, using
its spectral theorem and its actual algebraic matrix rank. -/
lemma frobeniusSq_le_rank_mul_operatorNorm_sq (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ShellAccounting.frobeniusSq A ≤ A.rank * operatorNorm A ^ 2 := by
  have he : ∀ i, |hA.eigenvalues i| ≤ operatorNorm A := by
    intro i
    change |hA.eigenvalues i| ≤ ‖A‖
    simpa only [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem (hA.eigenvalues_mem_spectrum_real i)
  rw [spectral_frobeniusSq A hA, hA.rank_eq_card_non_zero_eigs]
  let s := Finset.univ.filter (fun i => hA.eigenvalues i ≠ 0)
  have hs : (∑ i, hA.eigenvalues i ^ 2) = ∑ i ∈ s, hA.eigenvalues i ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
    simp [hi]
  rw [hs]
  calc
    _ ≤ ∑ _i ∈ s, operatorNorm A ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [he i, abs_nonneg (hA.eigenvalues i), sq_abs (hA.eigenvalues i)]
    _ = Fintype.card {i // hA.eigenvalues i ≠ 0} * operatorNorm A ^ 2 := by
      simp [s, Fintype.card_subtype]

/-- Generic matrix rank subadditivity derived from the native linear-map rank theorem. -/
lemma matrix_rank_add_le (A B : Matrix ι ι ℂ) : (A + B).rank ≤ A.rank + B.rank := by
  change Module.finrank ℂ (LinearMap.range (A + B).mulVecLin) ≤
    Module.finrank ℂ (LinearMap.range A.mulVecLin) + Module.finrank ℂ (LinearMap.range B.mulVecLin)
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

lemma ordered_eigenvalues_nonneg (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (i : Fin (Fintype.card ι)) : 0 ≤ hR.1.eigenvalues₀ i := by
  have h := hR.eigenvalues_nonneg (orderedIndex.symm i)
  simpa only [eigenvalues_ordered, Equiv.apply_symm_apply] using h

/-- A sorted PSD spectrum vanishes beyond its actual matrix rank. -/
lemma ordered_eigenvalue_zero_of_rank_le (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (r : ℕ) (hr : R.rank ≤ r) (i : Fin (Fintype.card ι)) (hi : r ≤ i.val) :
    hR.1.eigenvalues₀ i = 0 := by
  by_contra hn
  have hp : 0 < hR.1.eigenvalues₀ i :=
    lt_of_le_of_ne (ordered_eigenvalues_nonneg R hR i) (Ne.symm hn)
  have hcard : r + 1 ≤ Fintype.card ι := by omega
  let f : Fin (r + 1) → {j // hR.1.eigenvalues j ≠ 0} := fun j =>
    ⟨orderedIndex.symm ⟨j.val, lt_of_lt_of_le j.isLt hcard⟩, by
      rw [eigenvalues_ordered, Equiv.apply_symm_apply]
      have hji : (⟨j.val, lt_of_lt_of_le j.isLt hcard⟩ : Fin (Fintype.card ι)) ≤ i := by
        change j.val ≤ i.val
        omega
      exact ne_of_gt (hp.trans_le (hR.1.eigenvalues₀_antitone hji))⟩
  have hf : Function.Injective f := by
    intro j l h
    apply Fin.ext
    have hval := congrArg (fun x : {j // hR.1.eigenvalues j ≠ 0} => (orderedIndex x.val).val) h
    simpa only [f, Equiv.apply_symm_apply] using hval
  have hc := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin, ← hR.1.rank_eq_card_non_zero_eigs] at hc
  omega

/-- A diagonal real spectrum bounded in absolute value gives a true Euclidean
operator bound after actual unitary conjugation. -/
lemma conjugate_diagonal_operatorNorm_le (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hd : ∀ i, |d i| ≤ u) :
    operatorNorm (Normalization.conjugate (U : Matrix ι ι ℂ) (Normalization.diagonalMatrix d)) ≤ u := by
  let C := Normalization.conjugate (U : Matrix ι ι ℂ) (Normalization.diagonalMatrix d)
  have hC : C.IsHermitian := by
    change (Normalization.conjugate (U : Matrix ι ι ℂ) (Normalization.diagonalMatrix d))ᴴ = _
    simp only [C, Normalization.conjugate, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Normalization.diagonalMatrix_conjTranspose,
      Matrix.mul_assoc]
  have hd₂ : Normalization.diagonalMatrix (fun i => u^2 - d i^2) =
      ((u^2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) -
        Normalization.diagonalMatrix d * Normalization.diagonalMatrix d := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Normalization.diagonalMatrix, Matrix.diagonal_mul_diagonal, pow_two]
    · simp only [Normalization.diagonalMatrix, Matrix.diagonal_mul_diagonal]
      simp [Matrix.diagonal, hij]
  have hpd : (Normalization.diagonalMatrix (fun i => u^2 - d i^2)).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ ((u^2 - d i^2 : ℝ) : ℂ)
    have hsq : d i^2 ≤ u^2 := by nlinarith [hd i, abs_nonneg (d i), sq_abs (d i)]
    exact_mod_cast sub_nonneg.mpr hsq
  have hi : Normalization.conjugate (U : Matrix ι ι ℂ) 1 = 1 := by
    simpa only [Normalization.conjugate, Matrix.mul_one] using PositiveLossBridge.unitary_right U
  have hbound := hpd.mul_mul_conjTranspose_same (U : Matrix ι ι ℂ)
  change (Normalization.conjugate (U : Matrix ι ι ℂ) _).PosSemidef at hbound
  rw [hd₂, Normalization.conjugate_sub, Normalization.conjugate_smul, hi,
    Normalization.conjugate_mul _ _ _ (PositiveLossBridge.unitary_left U)] at hbound
  have hs : (C * C).PosSemidef := by
    simpa only [hC.eq] using Matrix.posSemidef_conjTranspose_mul_self C
  have hn := operatorNorm_le_of_psd (C*C) hs (u^2) (sq_nonneg _) hbound
  change ‖C*C‖ ≤ u^2 at hn
  have he := Matrix.l2_opNorm_conjTranspose_mul_self C
  rw [hC.eq] at he
  rw [he] at hn
  change ‖C‖ ≤ u
  nlinarith [norm_nonneg C]

lemma truncation_spectrum_error (Weyl : WeylEigenvalueInput ι)
    (A R : Matrix ι ι ℂ) (hA : A.IsHermitian) (hR : R.PosSemidef)
    (r : ℕ) (hr : R.rank ≤ r) (u : ℝ) (hu : 0 ≤ u)
    (herr : operatorNorm (A - R) ≤ u) (i : ι) :
    |truncatedSpectrum A hA r i - hA.eigenvalues i| ≤ u := by
  have hw := (Weyl.perturbation A R hA hR.1 (orderedIndex i)).trans herr
  have hnonneg := ordered_eigenvalues_nonneg R hR (orderedIndex i)
  rw [← eigenvalues_ordered A hA i] at hw
  unfold truncatedSpectrum
  split_ifs with hi
  · by_cases ha : 0 ≤ hA.eigenvalues i
    · simpa only [max_eq_left ha, sub_self, abs_zero] using hu
    · rw [max_eq_right (le_of_not_ge ha), zero_sub, abs_neg]
      have hl := (abs_le.mp hw).1
      rw [abs_of_neg (lt_of_not_ge ha)]
      linarith
  · rw [ordered_eigenvalue_zero_of_rank_le R hR r hr (orderedIndex i) (by omega), sub_zero] at hw
    simpa only [zero_sub, abs_neg] using hw

/-- Weyl's raw eigenvalue theorem proves the actual truncation is within u of
A. The output error conclusion is derived here, rather than supplied as input. -/
theorem rankTruncation_distance_to_input (Weyl : WeylEigenvalueInput ι)
    (A R : Matrix ι ι ℂ) (hA : A.IsHermitian) (hR : R.PosSemidef)
    (r : ℕ) (hr : R.rank ≤ r) (u : ℝ) (hu : 0 ≤ u)
    (herr : operatorNorm (A - R) ≤ u) :
    operatorNorm (rankTruncation A hA r - A) ≤ u := by
  have he : A = Normalization.conjugate (hA.eigenvectorUnitary : Matrix ι ι ℂ)
      (Normalization.diagonalMatrix hA.eigenvalues) := by
    simpa only [Normalization.conjugate, Normalization.diagonalMatrix,
      Function.comp_def, Matrix.star_eq_conjTranspose] using hA.spectral_theorem
  have hd : Normalization.diagonalMatrix (fun i => truncatedSpectrum A hA r i - hA.eigenvalues i) =
      Normalization.diagonalMatrix (truncatedSpectrum A hA r) -
        Normalization.diagonalMatrix hA.eigenvalues := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Normalization.diagonalMatrix]
    · simp [Normalization.diagonalMatrix, Matrix.diagonal, hij]
  have hdC : rankTruncation A hA r - A =
      Normalization.conjugate (hA.eigenvectorUnitary : Matrix ι ι ℂ)
        (Normalization.diagonalMatrix (fun i => truncatedSpectrum A hA r i - hA.eigenvalues i)) := by
    rw [hd, Normalization.conjugate_sub, ← he]
    rfl
  rw [hdC]
  exact conjugate_diagonal_operatorNorm_le hA.eigenvectorUnitary _ u hu
    (truncation_spectrum_error Weyl A R hA hR r hr u hu herr)

/-- The actual spectral output has squared Frobenius error at most 8 r u². -/
theorem rankTruncation_error (Weyl : WeylEigenvalueInput ι)
    (A R : Matrix ι ι ℂ) (hA : A.IsHermitian) (hR : R.PosSemidef)
    (r : ℕ) (hr : R.rank ≤ r) (u : ℝ) (hu : 0 ≤ u)
    (herr : operatorNorm (A - R) ≤ u) :
    (rankTruncation A hA r).PosSemidef ∧ (rankTruncation A hA r).rank ≤ r ∧
      operatorNorm (rankTruncation A hA r - R) ≤ 2*u ∧
      ShellAccounting.frobeniusSq (rankTruncation A hA r - R) ≤ 8*r*u^2 := by
  have hp := rankTruncation_posSemidef A hA r
  have hrank := rankTruncation_rank A hA r
  have ht := rankTruncation_distance_to_input Weyl A R hA hR r hr u hu herr
  have hnorm : operatorNorm (rankTruncation A hA r - R) ≤ 2*u := by
    calc
      _ = operatorNorm ((rankTruncation A hA r - A) + (A - R)) := by congr 1; abel
      _ ≤ operatorNorm (rankTruncation A hA r - A) + operatorNorm (A - R) := by
        change ‖(rankTruncation A hA r - A) + (A - R)‖ ≤ ‖rankTruncation A hA r - A‖ + ‖A-R‖
        exact norm_add_le _ _
      _ ≤ 2*u := by linarith
  have hrankdiff : (rankTruncation A hA r - R).rank ≤ 2*r := by
    have hadd := matrix_rank_add_le (rankTruncation A hA r) (-R)
    have hneg : (-R).rank = R.rank := by
      change Module.finrank ℂ (LinearMap.range (-R).mulVecLin) = _
      have he : (-R).mulVecLin = -R.mulVecLin := by
        ext x i
        simp [Matrix.neg_mulVec]
      rw [he, LinearMap.range_neg]
      rfl
    rw [hneg] at hadd
    change (rankTruncation A hA r - R).rank ≤ _ at hadd
    omega
  refine ⟨hp, hrank, hnorm, ?_⟩
  have hF := frobeniusSq_le_rank_mul_operatorNorm_sq _ (hp.1.sub hR.1)
  have hn₀ : 0 ≤ operatorNorm (rankTruncation A hA r - R) := norm_nonneg _
  have hrankℝ : ((rankTruncation A hA r - R).rank : ℝ) ≤ 2*r := by exact_mod_cast hrankdiff
  calc
    _ ≤ (rankTruncation A hA r - R).rank * operatorNorm (rankTruncation A hA r - R)^2 := hF
    _ ≤ (2*r) * (2*u)^2 := by
      apply mul_le_mul hrankℝ _ (sq_nonneg _) (by positivity)
      nlinarith
    _ = 8*r*u^2 := by ring

/-- The actual largest eigenvalue; the non-Hermitian branch is unused in all
applications and makes the event a function of matrices alone. -/
def topEigenvalue (A : Matrix ι ι ℂ) : ℝ :=
  if hA : A.IsHermitian then hA.eigenvalues₀ ⟨0, Fintype.card_pos⟩ else 0

lemma topEigenvalue_eq (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    topEigenvalue A = hA.eigenvalues₀ ⟨0, Fintype.card_pos⟩ := dif_pos hA

lemma eigenvalue_le_top (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (i : ι) :
    hA.eigenvalues i ≤ topEigenvalue A := by
  rw [eigenvalues_ordered, topEigenvalue_eq A hA]
  exact hA.eigenvalues₀_antitone (Fin.zero_le _)

lemma spectralValue_le_top (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (x : ℝ) (hx : x ∈ spectrum ℝ A) : x ≤ topEigenvalue A := by
  rw [hA.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact eigenvalue_le_top A hA i

/-- The operator-norm tail of a Hermitian matrix is covered by its two actual
largest-eigenvalue tails. This matrix fact is proved internally. -/
lemma operatorNorm_tail_subset (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (t : ℝ) (ht : 0 ≤ t) (h : t < operatorNorm A) :
    t ≤ topEigenvalue A ∨ t ≤ topEigenvalue (-A) := by
  by_contra hn
  push_neg at hn
  have hb : ∀ i, |hA.eigenvalues i| ≤ t := by
    intro i
    apply abs_le.mpr
    constructor
    · have hm : -hA.eigenvalues i ∈ spectrum ℝ (-A) := by
        rw [← spectrum.neg_eq]
        change -(-hA.eigenvalues i) ∈ spectrum ℝ A
        simpa only [neg_neg] using hA.eigenvalues_mem_spectrum_real i
      have hl := spectralValue_le_top (-A) hA.neg _ hm
      linarith [hn.2]
    · exact (eigenvalue_le_top A hA i).trans (le_of_lt hn.1)
  have he : A = Normalization.conjugate (hA.eigenvectorUnitary : Matrix ι ι ℂ)
      (Normalization.diagonalMatrix hA.eigenvalues) := by
    simpa only [Normalization.conjugate, Normalization.diagonalMatrix,
      Function.comp_def, Matrix.star_eq_conjTranspose] using hA.spectral_theorem
  have hg := conjugate_diagonal_operatorNorm_le hA.eigenvectorUnitary hA.eigenvalues t ht hb
  rw [← he] at hg
  exact not_lt_of_ge hg h

/-- Exact standard matrix Bernstein upper-tail theorem (Tropp 2012, Thm. 1.4).
It quantifies over arbitrary independent Hermitian matrices. In particular it
contains no P26 observation, sample average, estimator or risk conclusion. -/
structure MatrixBernsteinInput (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι] : Prop where
  upperTail : ∀ {Ω : Type u} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (N : ℕ) (X : Fin N → Ω → Matrix ι ι ℂ) (L v t : ℝ),
    0 < L → 0 ≤ v → 0 < t →
    (∀ i, Measurable (X i)) → ProbabilityTheory.iIndepFun X ν →
    (∀ i ω, (X i ω).IsHermitian) →
    (∀ i, matrixExpectation ν (X i) = 0) →
    (∀ i ω, operatorNorm (X i ω) ≤ L) →
    (∀ i a b, Integrable (fun ω => X i ω a b) ν) →
    (∀ i a b, Integrable (fun ω => (X i ω * X i ω) a b) ν) →
    operatorNorm (∑ i, matrixExpectation ν (fun ω => X i ω * X i ω)) ≤ v →
    ν {ω | t ≤ topEigenvalue (∑ i, X i ω)} ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) * Real.exp (-(t^2) / (2*(v + L*t/3))))

/-- Native independent full-copy sample space. Failed block projections remain
in every coordinate, exactly as they do in the one-copy outcome law. -/
def sampleMeasure (μ : Measure (OneCopyObservation.PureFrame ι)) (R : Matrix ι ι ℂ)
    (N : ℕ) : Measure (Fin N → Outcome ι) :=
  Measure.pi (fun _ : Fin N => outcomeMeasure μ R)

def centeredObservation (R : Matrix ι ι ℂ) (z : Outcome ι) : Matrix ι ι ℂ := observation z - R

def sampleCentered (R : Matrix ι ι ℂ) {N : ℕ} (i : Fin N) (z : Fin N → Outcome ι) :
    Matrix ι ι ℂ := centeredObservation R (z i)

lemma centeredObservation_measurable (R : Matrix ι ι ℂ) : Measurable (centeredObservation R) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact (measurable_affine_entry _ _ i j).sub measurable_const

lemma sampleCentered_measurable (R : Matrix ι ι ℂ) {N : ℕ} (i : Fin N) :
    Measurable (sampleCentered R i) :=
  (centeredObservation_measurable R).comp (measurable_pi_apply i)

lemma sampleCentered_independent (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (N : ℕ) :
    ProbabilityTheory.iIndepFun (sampleCentered R (N := N)) (sampleMeasure μ R N) := by
  letI : IsProbabilityMeasure (outcomeMeasure μ R) := ⟨outcomeMeasure_univ μ H R hR hw⟩
  exact ProbabilityTheory.iIndepFun_pi (fun _ : Fin N => (centeredObservation_measurable R).aemeasurable)

lemma sample_integral_eval (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) {N : ℕ} (i : Fin N)
    (f : Outcome ι → ℂ) (hf : Integrable f (outcomeMeasure μ R)) :
    (∫ z, f (z i) ∂sampleMeasure μ R N) = ∫ z, f z ∂outcomeMeasure μ R := by
  letI : IsProbabilityMeasure (outcomeMeasure μ R) := ⟨outcomeMeasure_univ μ H R hR hw⟩
  have hm : MeasurePreserving (Function.eval i) (sampleMeasure μ R N) (outcomeMeasure μ R) :=
    measurePreserving_eval (fun _ : Fin N => outcomeMeasure μ R) i
  have hfmap : AEStronglyMeasurable f ((sampleMeasure μ R N).map (Function.eval i)) := by
    rw [hm.map_eq]
    exact hf.aestronglyMeasurable
  rw [← integral_map hm.measurable.aemeasurable hfmap, hm.map_eq]

lemma sample_entry_integrable (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) {N : ℕ} (i : Fin N) (a b : ι) :
    Integrable (fun z => sampleCentered R i z a b) (sampleMeasure μ R N) := by
  letI : IsProbabilityMeasure (outcomeMeasure μ R) := ⟨outcomeMeasure_univ μ H R hR hw⟩
  exact (measurePreserving_eval (fun _ : Fin N => outcomeMeasure μ R) i).integrable_comp_of_integrable
    (centered_entry_integrable μ H R hR hw a b)

lemma sample_square_entry_integrable (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) {N : ℕ} (i : Fin N) (a b : ι) :
    Integrable (fun z => (sampleCentered R i z * sampleCentered R i z) a b) (sampleMeasure μ R N) := by
  letI : IsProbabilityMeasure (outcomeMeasure μ R) := ⟨outcomeMeasure_univ μ H R hR hw⟩
  exact (measurePreserving_eval (fun _ : Fin N => outcomeMeasure μ R) i).integrable_comp_of_integrable
    (centered_square_entry_integrable μ H R hR hw a b)

lemma sample_mean_zero (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) {N : ℕ} (i : Fin N) :
    matrixExpectation (sampleMeasure μ R N) (sampleCentered R i) = 0 := by
  ext a b
  change (∫ z, (observation (z i) - R) a b ∂sampleMeasure μ R N) = 0
  rw [sample_integral_eval μ H R hR hw i _ (centered_entry_integrable μ H R hR hw a b)]
  exact congrArg (fun M : Matrix ι ι ℂ => M a b) (centered_mean_zero μ H R hR hw)

lemma sample_variance_eq (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) {N : ℕ} (i : Fin N) :
    matrixExpectation (sampleMeasure μ R N) (fun z => sampleCentered R i z * sampleCentered R i z) =
      varianceMatrix R := by
  ext a b
  change (∫ z, ((observation (z i) - R) * (observation (z i) - R)) a b ∂sampleMeasure μ R N) = _
  rw [sample_integral_eval μ H R hR hw i _ (centered_square_entry_integrable μ H R hR hw a b)]
  exact centered_second_moment μ H R hR hw a b

lemma matrix_neg_measurable : Measurable (fun A : Matrix ι ι ℂ => -A) := by
  apply measurable_pi_lambda
  intro a
  apply measurable_pi_lambda
  intro b
  exact (show Measurable (fun A : Matrix ι ι ℂ => A a b) from
    (measurable_pi_apply b).comp (measurable_pi_apply a)).neg

lemma hermitian_sum {N : ℕ} (X : Fin N → Matrix ι ι ℂ) (hX : ∀ i, (X i).IsHermitian) :
    (∑ i, X i).IsHermitian := by
  change (∑ i, X i)ᴴ = ∑ i, X i
  simp only [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun i _ => (hX i).eq)

/-- The two signs and the union bound are internal consequences of the generic
one-sided Bernstein theorem. -/
theorem matrixBernstein_two_sided (B : MatrixBernsteinInput ι)
    {Ω : Type u} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (N : ℕ) (X : Fin N → Ω → Matrix ι ι ℂ) (L v t : ℝ)
    (hL : 0 < L) (hv : 0 ≤ v) (ht : 0 < t)
    (hmeas : ∀ i, Measurable (X i)) (hind : ProbabilityTheory.iIndepFun X ν)
    (hHerm : ∀ i ω, (X i ω).IsHermitian)
    (hmean : ∀ i, matrixExpectation ν (X i) = 0)
    (hbound : ∀ i ω, operatorNorm (X i ω) ≤ L)
    (hint : ∀ i a b, Integrable (fun ω => X i ω a b) ν)
    (hsq : ∀ i a b, Integrable (fun ω => (X i ω * X i ω) a b) ν)
    (hvar : operatorNorm (∑ i, matrixExpectation ν (fun ω => X i ω * X i ω)) ≤ v) :
    ν {ω | t < operatorNorm (∑ i, X i ω)} ≤
      ENNReal.ofReal (2*(Fintype.card ι : ℝ) * Real.exp (-(t^2) / (2*(v + L*t/3)))) := by
  have hp := B.upperTail ν N X L v t hL hv ht hmeas hind hHerm hmean hbound hint hsq hvar
  let Xn : Fin N → Ω → Matrix ι ι ℂ := fun i ω => -X i ω
  have hm : ∀ i, Measurable (Xn i) := fun i => matrix_neg_measurable.comp (hmeas i)
  have hi : ProbabilityTheory.iIndepFun Xn ν := hind.comp (fun _ => fun A => -A) (fun _ => matrix_neg_measurable)
  have hh : ∀ i ω, (Xn i ω).IsHermitian := fun i ω => (hHerm i ω).neg
  have hz : ∀ i, matrixExpectation ν (Xn i) = 0 := by
    intro i
    ext a b
    change (∫ ω, -(X i ω a b) ∂ν) = 0
    rw [integral_neg]
    have he := congrArg (fun M : Matrix ι ι ℂ => M a b) (hmean i)
    change (∫ ω, X i ω a b ∂ν) = 0 at he
    rw [he, neg_zero]
  have hb : ∀ i ω, operatorNorm (Xn i ω) ≤ L := by
    intro i ω
    change ‖-(X i ω)‖ ≤ L
    rw [norm_neg]
    exact hbound i ω
  have hni : ∀ i a b, Integrable (fun ω => Xn i ω a b) ν := fun i a b => (hint i a b).neg
  have hns : ∀ i a b, Integrable (fun ω => (Xn i ω * Xn i ω) a b) ν := by
    intro i a b
    simpa only [Xn, neg_mul_neg] using hsq i a b
  have hnv : operatorNorm (∑ i, matrixExpectation ν (fun ω => Xn i ω * Xn i ω)) ≤ v := by
    simpa only [Xn, neg_mul_neg] using hvar
  have hn := B.upperTail ν N Xn L v t hL hv ht hm hi hh hz hb hni hns hnv
  simp only [Xn, Finset.sum_neg_distrib] at hn
  calc
    _ ≤ ν ({ω | t ≤ topEigenvalue (∑ i, X i ω)} ∪
        {ω | t ≤ topEigenvalue (-(∑ i, X i ω))}) := by
      apply measure_mono
      intro ω hω
      exact operatorNorm_tail_subset _ (hermitian_sum _ (fun i => hHerm i ω)) t (le_of_lt ht) hω
    _ ≤ ν {ω | t ≤ topEigenvalue (∑ i, X i ω)} +
        ν {ω | t ≤ topEigenvalue (-(∑ i, X i ω))} := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * Real.exp (-(t^2)/(2*(v+L*t/3)))) +
        ENNReal.ofReal ((Fintype.card ι : ℝ) * Real.exp (-(t^2)/(2*(v+L*t/3)))) := add_le_add hp hn
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

lemma sample_variance_bound (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (N : ℕ) (W : ℝ) (hW : (Matrix.trace R).re ≤ W) :
    operatorNorm (∑ i : Fin N, matrixExpectation (sampleMeasure μ R N)
      (fun z => sampleCentered R i z * sampleCentered R i z)) ≤ (N : ℝ) * (2*Fintype.card ι*W) := by
  simp_rw [sample_variance_eq μ H R hR hw]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  change ‖N • varianceMatrix R‖ ≤ _
  rw [RCLike.norm_nsmul ℂ, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left (variance_operatorNorm R hR hw W hW) (Nat.cast_nonneg _)

/-- Bernstein for the native independent centered observations, before dividing
by N. Every moment, norm, independence and variance hypothesis is discharged. -/
theorem sample_sum_operatorNorm_tail (B : MatrixBernsteinInput ι)
    (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (N : ℕ) (W : ℝ) (hW : (Matrix.trace R).re ≤ W)
    (t : ℝ) (ht : 0 < t) :
    sampleMeasure μ R N {z | t < operatorNorm (∑ i, sampleCentered R i z)} ≤
      ENNReal.ofReal (2*(Fintype.card ι : ℝ) * Real.exp
        (-(t^2)/(2*((N : ℝ)*(2*Fintype.card ι*W) + (2*Fintype.card ι)*t/3)))) := by
  letI : IsProbabilityMeasure (outcomeMeasure μ R) := ⟨outcomeMeasure_univ μ H R hR hw⟩
  letI : IsProbabilityMeasure (sampleMeasure μ R N) := by unfold sampleMeasure; infer_instance
  have hW₀ : 0 ≤ W := ((hR.trace_nonneg).1).trans hW
  apply matrixBernstein_two_sided B (sampleMeasure μ R N) N (sampleCentered R)
    (2*Fintype.card ι) ((N : ℝ)*(2*Fintype.card ι*W)) t (by positivity)
    (by positivity) ht
  · exact sampleCentered_measurable R
  · exact sampleCentered_independent μ H R hR hw N
  · exact fun i z => (observation_hermitian (z i)).sub hR.1
  · exact sample_mean_zero μ H R hR hw
  · exact fun i z => centered_operatorNorm R hR hw (z i)
  · exact sample_entry_integrable μ H R hR hw
  · exact sample_square_entry_integrable μ H R hR hw
  · exact sample_variance_bound μ H R hR hw N W hW

/-- The average is computed only from observed outcomes and consumes N full copies. -/
def sampleAverage (N : ℕ) (z : Fin N → Outcome ι) : Matrix ι ι ℂ :=
  (N : ℂ)⁻¹ • ∑ i, observation (z i)

lemma sampleAverage_hermitian (N : ℕ) (z : Fin N → Outcome ι) : (sampleAverage N z).IsHermitian := by
  have h := hermitian_sum (fun i => observation (z i)) (fun i => observation_hermitian (z i))
  change ((N : ℂ)⁻¹ • ∑ i, observation (z i))ᴴ = _
  simp [sampleAverage, Matrix.conjTranspose_smul, h.eq]

lemma sample_sum_centered_eq (N : ℕ) (hN : 0 < N) (R : Matrix ι ι ℂ) (z : Fin N → Outcome ι) :
    ∑ i, sampleCentered R i z = (N : ℂ) • (sampleAverage N z - R) := by
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  simp only [sampleCentered, centeredObservation, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, sampleAverage, smul_sub, smul_smul,
    mul_inv_cancel₀ hn, one_smul, Nat.cast_smul_eq_nsmul]

lemma sample_sum_centered_norm (N : ℕ) (hN : 0 < N) (R : Matrix ι ι ℂ) (z : Fin N → Outcome ι) :
    operatorNorm (∑ i, sampleCentered R i z) = (N : ℝ) * operatorNorm (sampleAverage N z - R) := by
  rw [sample_sum_centered_eq N hN R z]
  change ‖(N : ℂ) • (sampleAverage N z - R)‖ = _
  rw [norm_smul]
  simp only [Complex.norm_natCast]
  rfl

/-- The exact two-sided average tail of Eq. (43), on the actual native product
measure of full-copy observations. -/
theorem sampleAverage_operatorNorm_tail (B : MatrixBernsteinInput ι)
    (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (N : ℕ) (hN : 0 < N)
    (W : ℝ) (hW : (Matrix.trace R).re ≤ W) (u : ℝ) (hu : 0 < u) :
    sampleMeasure μ R N {z | u < operatorNorm (sampleAverage N z - R)} ≤
      ENNReal.ofReal (2*(Fintype.card ι : ℝ) * Real.exp
        (-(N : ℝ)*u^2 / (4*Fintype.card ι*W + (4/3:ℝ)*Fintype.card ι*u))) := by
  have hNℝ : (0 : ℝ) < N := by exact_mod_cast hN
  have ht := sample_sum_operatorNorm_tail B μ H R hR hw N W hW ((N:ℝ)*u) (mul_pos hNℝ hu)
  have he : {z : Fin N → Outcome ι | (N:ℝ)*u < operatorNorm (∑ i, sampleCentered R i z)} =
      {z | u < operatorNorm (sampleAverage N z - R)} := by
    ext z
    simp only [Set.mem_setOf_eq, sample_sum_centered_norm N hN R z,
      mul_lt_mul_iff_right₀ hNℝ]
  rw [he] at ht
  have hW₀ : 0 ≤ W := ((hR.trace_nonneg).1).trans hW
  have hk : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  have hd : 0 < 4*(Fintype.card ι : ℝ)*W + (4/3:ℝ)*Fintype.card ι*u := by positivity
  have hexp : -(((N:ℝ)*u)^2) /
      (2*((N:ℝ)*(2*(Fintype.card ι : ℝ)*W)+(2*Fintype.card ι)*((N:ℝ)*u)/3)) =
      -(N:ℝ)*u^2/(4*Fintype.card ι*W+(4/3:ℝ)*Fintype.card ι*u) := by
    have hden : 2*((N:ℝ)*(2*(Fintype.card ι : ℝ)*W)+(2*Fintype.card ι)*((N:ℝ)*u)/3) =
        (N:ℝ)*(4*Fintype.card ι*W+(4/3:ℝ)*Fintype.card ι*u) := by ring
    rw [hden]
    field_simp
  simpa only [hexp] using ht

/-- The actual PSD spectral estimate, using no information about the true R. -/
def estimate (N r : ℕ) (z : Fin N → Outcome ι) : Matrix ι ι ℂ :=
  rankTruncation (sampleAverage N z) (sampleAverage_hermitian N z) r

lemma estimate_posSemidef (N r : ℕ) (z : Fin N → Outcome ι) : (estimate N r z).PosSemidef :=
  rankTruncation_posSemidef _ _ _

lemma estimate_rank (N r : ℕ) (z : Fin N → Outcome ι) : (estimate N r z).rank ≤ r :=
  rankTruncation_rank _ _ _

/-- The actual Frobenius-error event is controlled by the proved average tail. -/
theorem estimate_error_tail (B : MatrixBernsteinInput ι) (Weyl : WeylEigenvalueInput ι)
    (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (r : ℕ) (hr : R.rank ≤ r)
    (N : ℕ) (hN : 0 < N) (W : ℝ) (hW : (Matrix.trace R).re ≤ W)
    (u : ℝ) (hu : 0 < u) (η : ℝ) (hη : 8*(r:ℝ)*u^2 ≤ η) :
    sampleMeasure μ R N {z | η < ShellAccounting.frobeniusSq (estimate N r z - R)} ≤
      ENNReal.ofReal (2*(Fintype.card ι : ℝ) * Real.exp
        (-(N : ℝ)*u^2 / (4*Fintype.card ι*W + (4/3:ℝ)*Fintype.card ι*u))) := by
  apply le_trans (measure_mono (t := {z | u < operatorNorm (sampleAverage N z - R)}) _) 
    (sampleAverage_operatorNorm_tail B μ H R hR hw N hN W hW u hu)
  intro z hz
  by_contra h
  have hg := rankTruncation_error Weyl (sampleAverage N z) R
    (sampleAverage_hermitian N z) hR r hr u (le_of_lt hu) (le_of_not_gt h)
  exact not_lt_of_ge (hg.2.2.2.trans hη) hz

/-- The same truncation, parameterized by any actual ordered diagonalizing
unitary. This permits a Borel spectral selection at repeated eigenvalues. -/
def rankTruncationWith (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (r : ℕ)
    (U : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ :=
  Normalization.conjugate (U : Matrix ι ι ℂ)
    (Normalization.diagonalMatrix (truncatedSpectrum A hA r))

lemma rank_conjugate_unitary (U : Matrix.unitaryGroup ι ℂ) (X : Matrix ι ι ℂ) :
    (Normalization.conjugate (U : Matrix ι ι ℂ) X).rank = X.rank := by
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · have he : X = (U : Matrix ι ι ℂ)ᴴ *
        Normalization.conjugate (U : Matrix ι ι ℂ) X * (U : Matrix ι ι ℂ) := by
      simp only [Normalization.conjugate, ← Matrix.mul_assoc, PositiveLossBridge.unitary_left U,
        Matrix.one_mul]
      rw [Matrix.mul_assoc, PositiveLossBridge.unitary_left U, Matrix.mul_one]
    calc
      X.rank = ((U : Matrix ι ι ℂ)ᴴ * Normalization.conjugate (U : Matrix ι ι ℂ) X *
        (U : Matrix ι ι ℂ)).rank := congrArg Matrix.rank he
      _ ≤ (Normalization.conjugate (U : Matrix ι ι ℂ) X).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

lemma rankTruncationWith_posSemidef (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (r : ℕ)
    (U : Matrix.unitaryGroup ι ℂ) : (rankTruncationWith A hA r U).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℂ) ≤ (truncatedSpectrum A hA r i : ℂ)
  exact_mod_cast truncatedSpectrum_nonneg A hA r i

lemma rankTruncationWith_rank (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (r : ℕ)
    (U : Matrix.unitaryGroup ι ℂ) : (rankTruncationWith A hA r U).rank ≤ r := by
  have he : (rankTruncationWith A hA r U).rank = (rankTruncation A hA r).rank := by
    simp only [rankTruncationWith, rankTruncation, rank_conjugate_unitary]
  rw [he]
  exact rankTruncation_rank A hA r

/-- This error proof uses only the actual ordered diagonalization equation,
not any particular eigenvector choice. -/
theorem rankTruncationWith_distance_to_input (Weyl : WeylEigenvalueInput ι)
    (A R : Matrix ι ι ℂ) (hA : A.IsHermitian) (hR : R.PosSemidef)
    (U : Matrix.unitaryGroup ι ℂ)
    (hrec : A = Normalization.conjugate (U : Matrix ι ι ℂ) (Normalization.diagonalMatrix hA.eigenvalues))
    (r : ℕ) (hr : R.rank ≤ r) (u : ℝ) (hu : 0 ≤ u)
    (herr : operatorNorm (A-R) ≤ u) : operatorNorm (rankTruncationWith A hA r U - A) ≤ u := by
  have hd : Normalization.diagonalMatrix (fun i => truncatedSpectrum A hA r i - hA.eigenvalues i) =
      Normalization.diagonalMatrix (truncatedSpectrum A hA r) - Normalization.diagonalMatrix hA.eigenvalues := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Normalization.diagonalMatrix]
    · simp [Normalization.diagonalMatrix, Matrix.diagonal, hij]
  have he : rankTruncationWith A hA r U - A = Normalization.conjugate (U : Matrix ι ι ℂ)
      (Normalization.diagonalMatrix (fun i => truncatedSpectrum A hA r i - hA.eigenvalues i)) := by
    rw [hd, Normalization.conjugate_sub, ← hrec]
    rfl
  rw [he]
  exact conjugate_diagonal_operatorNorm_le U _ u hu
    (truncation_spectrum_error Weyl A R hA hR r hr u hu herr)

/-- The full deterministic output bound for any actual ordered spectral basis,
including a separately chosen measurable basis. -/
theorem rankTruncationWith_error (Weyl : WeylEigenvalueInput ι)
    (A R : Matrix ι ι ℂ) (hA : A.IsHermitian) (hR : R.PosSemidef)
    (U : Matrix.unitaryGroup ι ℂ)
    (hrec : A = Normalization.conjugate (U : Matrix ι ι ℂ) (Normalization.diagonalMatrix hA.eigenvalues))
    (r : ℕ) (hr : R.rank ≤ r) (u : ℝ) (hu : 0 ≤ u)
    (herr : operatorNorm (A-R) ≤ u) :
    (rankTruncationWith A hA r U).PosSemidef ∧ (rankTruncationWith A hA r U).rank ≤ r ∧
      operatorNorm (rankTruncationWith A hA r U - R) ≤ 2*u ∧
      ShellAccounting.frobeniusSq (rankTruncationWith A hA r U - R) ≤ 8*r*u^2 := by
  have hp := rankTruncationWith_posSemidef A hA r U
  have hrank := rankTruncationWith_rank A hA r U
  have ht := rankTruncationWith_distance_to_input Weyl A R hA hR U hrec r hr u hu herr
  have hnorm : operatorNorm (rankTruncationWith A hA r U - R) ≤ 2*u := by
    calc
      _ = operatorNorm ((rankTruncationWith A hA r U - A) + (A - R)) := by congr 1; abel
      _ ≤ operatorNorm (rankTruncationWith A hA r U - A) + operatorNorm (A - R) := by
        change ‖(rankTruncationWith A hA r U - A) + (A - R)‖ ≤ ‖rankTruncationWith A hA r U - A‖ + ‖A-R‖
        exact norm_add_le _ _
      _ ≤ 2*u := by linarith
  have hrankdiff : (rankTruncationWith A hA r U - R).rank ≤ 2*r := by
    have hadd := matrix_rank_add_le (rankTruncationWith A hA r U) (-R)
    have hneg : (-R).rank = R.rank := by
      change Module.finrank ℂ (LinearMap.range (-R).mulVecLin) = _
      have he : (-R).mulVecLin = -R.mulVecLin := by ext x i; simp
      rw [he, LinearMap.range_neg]
      rfl
    rw [hneg] at hadd
    change (rankTruncationWith A hA r U - R).rank ≤ _ at hadd
    omega
  refine ⟨hp, hrank, hnorm, ?_⟩
  have hF := frobeniusSq_le_rank_mul_operatorNorm_sq _ (hp.1.sub hR.1)
  have hn₀ : 0 ≤ operatorNorm (rankTruncationWith A hA r U - R) := norm_nonneg _
  have hrankℝ : ((rankTruncationWith A hA r U - R).rank : ℝ) ≤ 2*r := by exact_mod_cast hrankdiff
  calc
    _ ≤ (rankTruncationWith A hA r U - R).rank * operatorNorm (rankTruncationWith A hA r U - R)^2 := hF
    _ ≤ (2*r) * (2*u)^2 := by
      apply mul_le_mul hrankℝ _ (sq_nonneg _) (by positivity)
      nlinarith
    _ = 8*r*u^2 := by ring

/-- Explicit positive deviation, chosen so that 8 r u² is below η. -/
def deviation (r : ℕ) (η : ℝ) : ℝ := 1 / (3 * Real.sqrt ((r : ℝ)/η))

/-- An explicit version of the two terms in the source copy bound. -/
def copyBudget (r : ℕ) (W η β : ℝ) : ℝ :=
  (36*(r:ℝ)*Fintype.card ι*W/η + 4*Fintype.card ι*Real.sqrt ((r:ℝ)/η)) *
    Real.log (2*(Fintype.card ι:ℝ)/β)

def copies (r : ℕ) (W η β : ℝ) : ℕ := ⌈copyBudget (ι := ι) r W η β⌉₊

lemma deviation_pos (r : ℕ) (hr : 0 < r) (η : ℝ) (hη : 0 < η) : 0 < deviation r η := by
  unfold deviation
  have hrℝ : (0 : ℝ) < r := by exact_mod_cast hr
  positivity

lemma deviation_sq (r : ℕ) (hr : 0 < r) (η : ℝ) (hη : 0 < η) :
    deviation r η ^ 2 = η/(9*(r:ℝ)) := by
  have hrℝ : (0 : ℝ) < r := by exact_mod_cast hr
  have hs := Real.sq_sqrt (le_of_lt (div_pos hrℝ hη))
  have hsn : Real.sqrt ((r:ℝ)/η) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (div_pos hrℝ hη))
  unfold deviation
  rw [div_pow, mul_pow, hs]
  field_simp
  norm_num

lemma deviation_error (r : ℕ) (hr : 0 < r) (η : ℝ) (hη : 0 < η) :
    8*(r:ℝ)*deviation r η^2 ≤ η := by
  rw [deviation_sq r hr η hη]
  have hrℝ : (0 : ℝ) < r := by exact_mod_cast hr
  have he : 8*(r:ℝ)*(η/(9*(r:ℝ))) = (8/9:ℝ)*η := by field_simp
  rw [he]
  linarith

lemma budget_pos (r : ℕ) (hr : 0 < r) (W η β : ℝ) (hW : 0 ≤ W)
    (hη : 0 < η) (hβ : 0 < β) (hβ₁ : β < 1/2) : 0 < copyBudget (ι := ι) r W η β := by
  have hrℝ : (0 : ℝ) < r := by exact_mod_cast hr
  have hk : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  have hlog : 0 < Real.log (2*(Fintype.card ι:ℝ)/β) := by
    apply Real.log_pos
    apply (lt_div_iff₀ hβ).mpr
    nlinarith
  unfold copyBudget
  apply mul_pos _ hlog
  have hs : 0 < Real.sqrt ((r:ℝ)/η) := Real.sqrt_pos.mpr (div_pos hrℝ hη)
  positivity

lemma copies_pos (r : ℕ) (hr : 0 < r) (W η β : ℝ) (hW : 0 ≤ W)
    (hη : 0 < η) (hβ : 0 < β) (hβ₁ : β < 1/2) : 0 < copies (ι := ι) r W η β :=
  Nat.ceil_pos.mpr (budget_pos r hr W η β hW hη hβ hβ₁)

lemma copies_bound (r : ℕ) (hr : 0 < r) (W η β : ℝ) (hW : 0 ≤ W)
    (hη : 0 < η) (hβ : 0 < β) (hβ₁ : β < 1/2) :
    (copies (ι := ι) r W η β : ℝ) < copyBudget (ι := ι) r W η β + 1 :=
  Nat.ceil_lt_add_one (le_of_lt (budget_pos r hr W η β hW hη hβ hβ₁))

lemma copyBudget_eq_bernstein (r : ℕ) (hr : 0 < r) (W η β : ℝ) (hη : 0 < η) :
    copyBudget (ι := ι) r W η β =
      ((4*(Fintype.card ι:ℝ)*W + (4/3:ℝ)*Fintype.card ι*deviation r η) / deviation r η^2) *
        Real.log (2*(Fintype.card ι:ℝ)/β) := by
  have hsn : Real.sqrt ((r:ℝ)/η) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (div_pos (by exact_mod_cast hr : (0:ℝ)<r) hη))
  have hterm1 : (4*(Fintype.card ι:ℝ)*W)/deviation r η^2 = 36*(r:ℝ)*Fintype.card ι*W/η := by
    rw [deviation_sq r hr η hη]
    field_simp
    <;> ring
  have hterm2 : ((4/3:ℝ)*Fintype.card ι*deviation r η)/deviation r η^2 =
      4*(Fintype.card ι:ℝ)*Real.sqrt ((r:ℝ)/η) := by
    unfold deviation
    field_simp
    <;> ring
  unfold copyBudget
  rw [add_div, hterm1, hterm2]

lemma bernstein_factor_le (N : ℕ) (u W β : ℝ) (hu : 0 < u) (hW : 0 ≤ W)
    (hβ : 0 < β)
    (hbudget : ((4*(Fintype.card ι:ℝ)*W+(4/3:ℝ)*Fintype.card ι*u)/u^2) *
      Real.log (2*(Fintype.card ι:ℝ)/β) ≤ (N:ℝ)) :
    2*(Fintype.card ι:ℝ)*Real.exp (-(N:ℝ)*u^2 /
      (4*Fintype.card ι*W+(4/3:ℝ)*Fintype.card ι*u)) ≤ β := by
  have hk : (0:ℝ)<Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  have hd : 0 < 4*(Fintype.card ι:ℝ)*W+(4/3:ℝ)*Fintype.card ι*u := by positivity
  have hu₂ : 0 < u^2 := sq_pos_of_pos hu
  have hb := mul_le_mul_of_nonneg_right hbudget (le_of_lt hu₂)
  have he : (((4*(Fintype.card ι:ℝ)*W+(4/3:ℝ)*Fintype.card ι*u)/u^2) *
      Real.log (2*(Fintype.card ι:ℝ)/β))*u^2 =
      (4*(Fintype.card ι:ℝ)*W+(4/3:ℝ)*Fintype.card ι*u)*Real.log (2*(Fintype.card ι:ℝ)/β) := by
    field_simp
  rw [he] at hb
  have hlog : Real.log (2*(Fintype.card ι:ℝ)/β) ≤
      (N:ℝ)*u^2/(4*(Fintype.card ι:ℝ)*W+(4/3:ℝ)*Fintype.card ι*u) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [hb]
  calc
    _ ≤ 2*(Fintype.card ι:ℝ)*Real.exp (-Real.log (2*(Fintype.card ι:ℝ)/β)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      simpa only [neg_div, neg_mul] using neg_le_neg hlog
    _ = β := by
      rw [Real.exp_neg, Real.exp_log (div_pos (by positivity) hβ)]
      field_simp

/-- Integer copy choice and the actual error-tail conclusion for the native
ordered-basis output. A measurable spectral selection may replace its basis
using `rankTruncationWith_error` below. -/
theorem estimate_failure_le_beta (B : MatrixBernsteinInput ι) (Weyl : WeylEigenvalueInput ι)
    (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (r : ℕ) (hr : 0 < r) (hrank : R.rank ≤ r)
    (W η β : ℝ) (hW : (Matrix.trace R).re ≤ W) (hη : 0 < η)
    (hβ : 0 < β) (hβ₁ : β < 1/2) :
    sampleMeasure μ R (copies (ι:=ι) r W η β)
      {z | η < ShellAccounting.frobeniusSq (estimate (copies (ι:=ι) r W η β) r z - R)} ≤ ENNReal.ofReal β := by
  have hW₀ : 0 ≤ W := ((hR.trace_nonneg).1).trans hW
  have hN := copies_pos (ι := ι) r hr W η β hW₀ hη hβ hβ₁
  have hu := deviation_pos r hr η hη
  apply (estimate_error_tail B Weyl μ H R hR hw r hrank _ hN W hW _ hu η (deviation_error r hr η hη)).trans
  apply ENNReal.ofReal_le_ofReal
  apply bernstein_factor_le _ _ W β hu hW₀ hβ
  rw [← copyBudget_eq_bernstein (ι := ι) r hr W η β hη]
  exact Nat.le_ceil _

/-- The output based on any actual ordered spectral selection. -/
def estimateUsing (S : {A : Matrix ι ι ℂ // A.IsHermitian} → Matrix.unitaryGroup ι ℂ)
    (N r : ℕ) (z : Fin N → Outcome ι) : Matrix ι ι ℂ :=
  rankTruncationWith (sampleAverage N z) (sampleAverage_hermitian N z) r
    (S ⟨sampleAverage N z, sampleAverage_hermitian N z⟩)

/-- The error tail is uniform in the choice of an ordered diagonalizing basis;
therefore it applies directly to a Borel choice at repeated eigenvalues. -/
theorem estimateUsing_error_tail (B : MatrixBernsteinInput ι) (Weyl : WeylEigenvalueInput ι)
    (S : {A : Matrix ι ι ℂ // A.IsHermitian} → Matrix.unitaryGroup ι ℂ)
    (hS : ∀ A, A.val = Normalization.conjugate (S A : Matrix ι ι ℂ)
      (Normalization.diagonalMatrix A.property.eigenvalues))
    (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (r : ℕ) (hr : R.rank ≤ r)
    (N : ℕ) (hN : 0 < N) (W : ℝ) (hW : (Matrix.trace R).re ≤ W)
    (u : ℝ) (hu : 0 < u) (η : ℝ) (hη : 8*(r:ℝ)*u^2 ≤ η) :
    sampleMeasure μ R N {z | η < ShellAccounting.frobeniusSq (estimateUsing S N r z - R)} ≤
      ENNReal.ofReal (2*(Fintype.card ι : ℝ) * Real.exp
        (-(N : ℝ)*u^2 / (4*Fintype.card ι*W + (4/3:ℝ)*Fintype.card ι*u))) := by
  apply le_trans (measure_mono (t := {z | u < operatorNorm (sampleAverage N z - R)}) _)
    (sampleAverage_operatorNorm_tail B μ H R hR hw N hN W hW u hu)
  intro z hz
  by_contra h
  have hg := rankTruncationWith_error Weyl (sampleAverage N z) R
    (sampleAverage_hermitian N z) hR _ (hS ⟨sampleAverage N z, sampleAverage_hermitian N z⟩)
    r hr u (le_of_lt hu) (le_of_not_gt h)
  exact not_lt_of_ge (hg.2.2.2.trans hη) hz

/-- The explicit integer budget works for every ordered basis selection. -/
theorem estimateUsing_failure_le_beta (B : MatrixBernsteinInput ι) (Weyl : WeylEigenvalueInput ι)
    (S : {A : Matrix ι ι ℂ // A.IsHermitian} → Matrix.unitaryGroup ι ℂ)
    (hS : ∀ A, A.val = Normalization.conjugate (S A : Matrix ι ι ℂ)
      (Normalization.diagonalMatrix A.property.eigenvalues))
    (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (r : ℕ) (hr : 0 < r) (hrank : R.rank ≤ r)
    (W η β : ℝ) (hW : (Matrix.trace R).re ≤ W) (hη : 0 < η)
    (hβ : 0 < β) (hβ₁ : β < 1/2) :
    sampleMeasure μ R (copies (ι:=ι) r W η β)
      {z | η < ShellAccounting.frobeniusSq (estimateUsing S (copies (ι:=ι) r W η β) r z - R)} ≤ ENNReal.ofReal β := by
  have hW₀ : 0 ≤ W := ((hR.trace_nonneg).1).trans hW
  have hN := copies_pos (ι:=ι) r hr W η β hW₀ hη hβ hβ₁
  have hu := deviation_pos r hr η hη
  apply (estimateUsing_error_tail B Weyl S hS μ H R hR hw r hrank _ hN W hW _ hu η
    (deviation_error r hr η hη)).trans
  apply ENNReal.ofReal_le_ofReal
  apply bernstein_factor_le _ _ W β hu hW₀ hβ
  rw [← copyBudget_eq_bernstein (ι:=ι) r hr W η β hη]
  exact Nat.le_ceil _

/-- Rounding is absorbed by a constant in the nontrivial branch W²>η. -/
lemma copyBudget_ge_one (r : ℕ) (hr : 0 < r) (W η β : ℝ)
    (hW₀ : 0 ≤ W) (hW : W ≤ 1) (hη : 0 < η) (hηW : η < W^2)
    (hβ : 0 < β) (hβ₁ : β < 1/2) : 1 ≤ copyBudget (ι:=ι) r W η β := by
  have hr₁ : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hk₁ : (1:ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos (α:=ι)
  have hηW' : η < W := by nlinarith [mul_nonneg hW₀ (sub_nonneg.mpr hW)]
  have hratio : 1 ≤ W/η := (le_div_iff₀ hη).mpr (by simpa only [one_mul] using le_of_lt hηW')
  have hp : 1 ≤ (r:ℝ)*(Fintype.card ι:ℝ) := by
    calc
      (1:ℝ) = 1*1 := by ring
      _ ≤ (r:ℝ)*(Fintype.card ι:ℝ) := mul_le_mul hr₁ hk₁ (by norm_num) (by positivity)
  have hfirst : 36 ≤ 36*(r:ℝ)*(Fintype.card ι:ℝ)*W/η := by
    have h := mul_le_mul hp hratio (by norm_num) (by positivity)
    calc
      (36:ℝ) = 36*(1*1) := by ring
      _ ≤ 36*((r:ℝ)*(Fintype.card ι:ℝ)*(W/η)) := mul_le_mul_of_nonneg_left h (by norm_num)
      _ = _ := by ring
  have harg : 0 < 2*(Fintype.card ι:ℝ)/β := by positivity
  have hinv : (2*(Fintype.card ι:ℝ)/β)⁻¹ ≤ 1/2 := by
    rw [inv_div]
    apply (div_le_iff₀ (by positivity : 0 < 2*(Fintype.card ι:ℝ))).mpr
    nlinarith
  have hlog : (1/2:ℝ) ≤ Real.log (2*(Fintype.card ι:ℝ)/β) := by
    linarith [Real.one_sub_inv_le_log_of_pos harg]
  have hs : 0 ≤ 4*(Fintype.card ι:ℝ)*Real.sqrt ((r:ℝ)/η) := by positivity
  unfold copyBudget
  nlinarith [mul_le_mul hfirst hlog (by norm_num) (by positivity)]

lemma copies_nontrivial_bound (r : ℕ) (hr : 0 < r) (W η β : ℝ)
    (hW₀ : 0 ≤ W) (hW : W ≤ 1) (hη : 0 < η) (hηW : η < W^2)
    (hβ : 0 < β) (hβ₁ : β < 1/2) :
    (copies (ι:=ι) r W η β : ℝ) < 2*copyBudget (ι:=ι) r W η β := by
  have h := copies_bound (ι:=ι) r hr W η β hW₀ hη hβ hβ₁
  have hb := copyBudget_ge_one (ι:=ι) r hr W η β hW₀ hW hη hηW hβ hβ₁
  linarith

/-- The zero-copy branch uses the actual PSD block Frobenius bound. -/
theorem zero_branch (R : Matrix ι ι ℂ) (hR : R.PosSemidef) (W η : ℝ)
    (hW : (Matrix.trace R).re ≤ W) (hzero : W^2 ≤ η) :
    (0 : Matrix ι ι ℂ).PosSemidef ∧ ShellAccounting.frobeniusSq (0-R) ≤ η :=
  CollectiveSubmatrix.zero_estimate_suffices R hR _ W η rfl (hR.trace_nonneg).1 hW hzero

/-- The rank promise can always be replaced by min(r,k) on the actual block. -/
lemma rank_promise_min (R : Matrix ι ι ℂ) (r : ℕ) (hr : R.rank ≤ r) :
    R.rank ≤ min r (Fintype.card ι) := le_min hr (Matrix.rank_le_card_width R)

/-- Explicit constant in the source O-bound, including integer rounding. -/
lemma copies_source_bound (r : ℕ) (hr : 0 < r) (W η β : ℝ)
    (hW₀ : 0 ≤ W) (hW : W ≤ 1) (hη : 0 < η) (hηW : η < W^2)
    (hβ : 0 < β) (hβ₁ : β < 1/2) :
    (copies (ι:=ι) r W η β : ℝ) <
      72*((r:ℝ)*Fintype.card ι*W/η + Fintype.card ι*Real.sqrt ((r:ℝ)/η)) *
        Real.log (2*(Fintype.card ι:ℝ)/β) := by
  have hk : (1:ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos (α:=ι)
  have hlog : 0 ≤ Real.log (2*(Fintype.card ι:ℝ)/β) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hβ).mpr
    nlinarith
  apply (copies_nontrivial_bound (ι:=ι) r hr W η β hW₀ hW hη hηW hβ hβ₁).trans_le
  unfold copyBudget
  have he : 72*((r:ℝ)*Fintype.card ι*W/η + Fintype.card ι*Real.sqrt ((r:ℝ)/η)) *
      Real.log (2*(Fintype.card ι:ℝ)/β) =
      2*((36*(r:ℝ)*Fintype.card ι*W/η + 4*Fintype.card ι*Real.sqrt ((r:ℝ)/η)) *
        Real.log (2*(Fintype.card ι:ℝ)/β)) +
      64*(Fintype.card ι:ℝ)*Real.sqrt ((r:ℝ)/η)*Real.log (2*(Fintype.card ι:ℝ)/β) := by ring
  rw [he]
  exact le_add_of_nonneg_right (by positivity)

lemma sampleAverage_measurable (N : ℕ) : Measurable (sampleAverage (ι:=ι) N) := by
  apply measurable_pi_lambda
  intro a
  apply measurable_pi_lambda
  intro b
  simp only [sampleAverage, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
  apply Measurable.const_mul
  apply Finset.measurable_sum Finset.univ
  intro i _
  exact (measurable_affine_entry _ _ a b).comp (measurable_pi_apply i)

lemma sampleAverage_subtype_measurable (N : ℕ) :
    Measurable (fun z : Fin N → Outcome ι =>
      (⟨sampleAverage N z, sampleAverage_hermitian N z⟩ : {A : Matrix ι ι ℂ // A.IsHermitian})) :=
  (sampleAverage_measurable N).subtype_mk

lemma frobenius_error_measurable {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω → Matrix ι ι ℂ) (hT : Measurable T) (R : Matrix ι ι ℂ) :
    Measurable (fun z => ShellAccounting.frobeniusSq (T z-R)) := by
  unfold ShellAccounting.frobeniusSq
  apply Finset.measurable_sum Finset.univ
  intro a _
  apply Finset.measurable_sum Finset.univ
  intro b _
  exact (((measurable_pi_apply b).comp ((measurable_pi_apply a).comp hT)).sub measurable_const).norm.pow_const 2

/-- The event conversion uses only measure monotonicity and the genuine
probability normalization, and therefore also applies before any Borel wrapper. -/
lemma success_lower_from_failure {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → ℝ) (η β : ℝ) (hβ : 0 ≤ β)
    (hfail : ν {z | η < f z} ≤ ENNReal.ofReal β) :
    ENNReal.ofReal (1-β) ≤ ν {z | f z ≤ η} := by
  rw [ENNReal.ofReal_sub 1 hβ, ENNReal.ofReal_one]
  apply tsub_le_iff_right.mpr
  have he : Set.univ = {z | f z ≤ η} ∪ {z | η < f z} := by
    ext z
    simp only [Set.mem_univ, Set.mem_union, Set.mem_setOf_eq, true_iff]
    exact le_or_gt (f z) η
  calc
    (1:ℝ≥0∞) = ν Set.univ := (measure_univ).symm
    _ = ν ({z | f z ≤ η} ∪ {z | η < f z}) := congrArg ν he
    _ ≤ ν {z | f z ≤ η} + ν {z | η < f z} := measure_union_le _ _
    _ ≤ ν {z | f z ≤ η} + ENNReal.ofReal β := add_le_add_left hfail _

section FullCopyProjection
variable {δ : Type*} [Fintype δ] [DecidableEq δ]

/-- The actual ambient projector associated with an isometric block inclusion. -/
def blockProjection (V : Matrix δ ι ℂ) (hV : Vᴴ*V=1) : OrthogonalProjector δ where
  matrix := V*Vᴴ
  hermitian := Matrix.isHermitian_mul_conjTranspose_self V
  idempotent := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V Vᴴ, hV, Matrix.one_mul]

/-- The actual principal block of the true ambient density in an isometric basis. -/
def trueBlock (V : Matrix δ ι ℂ) (ρ : Density δ) : Matrix ι ι ℂ := Vᴴ*ρ.matrix*V

lemma trueBlock_posSemidef (V : Matrix δ ι ℂ) (ρ : Density δ) : (trueBlock V ρ).PosSemidef :=
  ρ.positive.conjTranspose_mul_mul_same V

lemma trueBlock_mass_le_one (V : Matrix δ ι ℂ) (hV : Vᴴ*V=1) (ρ : Density δ) :
    (Matrix.trace (trueBlock V ρ)).re ≤ 1 := by
  have h := TailConvexity.pairing_nonneg_psd ρ.matrix
    (PureMinimax.complement (blockProjection V hV)).matrix ρ.positive
    (PureMinimax.complement (blockProjection V hV)).positive
  change 0 ≤ (Matrix.trace (ρ.matrix*(1-V*Vᴴ))).re at h
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, ρ.trace_one, Complex.sub_re, Complex.one_re] at h
  have he : Matrix.trace (ρ.matrix*(V*Vᴴ)) = Matrix.trace (trueBlock V ρ) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    rfl
  rw [he] at h
  linarith

/-- A fixed finite reference measure, independent of the unknown state. -/
def projectionReference (μ : Measure (OneCopyObservation.PureFrame ι)) : Measure (Outcome ι) :=
  μ.map Sum.inl + Measure.dirac (Sum.inr ())

/-- Covariant success effects in the block, plus its actual orthogonal failure effect. -/
def projectionEffect (V : Matrix δ ι ℂ) : Outcome ι → Matrix δ δ ℂ
  | Sum.inl U => (Fintype.card ι : ℂ) • (V*projector U*Vᴴ)
  | Sum.inr _ => 1-V*Vᴴ

lemma projectionEffect_measurable (V : Matrix δ ι ℂ) (i j : δ) :
    Measurable (fun z => projectionEffect V z i j) := by
  apply measurable_fun_sum
  · change Measurable (fun U : OneCopyObservation.PureFrame ι =>
      (Fintype.card ι : ℂ)*((V*projector U*Vᴴ) i j))
    simp only [Matrix.mul_apply]
    apply Measurable.const_mul
    apply Finset.measurable_sum Finset.univ
    intro a _
    apply Measurable.mul_const
    apply Finset.measurable_sum Finset.univ
    intro b _
    exact (measurable_projector_entry b a).const_mul _
  · exact measurable_const

lemma projectionEffect_positive (V : Matrix δ ι ℂ) (hV : Vᴴ*V=1) (z : Outcome ι) :
    (projectionEffect V z).PosSemidef := by
  rcases z with U | u
  · exact (U.projector.positive.mul_mul_conjTranspose_same V).smul (α:=ℂ)
      (by exact_mod_cast Nat.zero_le (Fintype.card ι))
  · exact (PureMinimax.complement (blockProjection V hV)).positive

lemma projectionEffect_entry_bound (V : Matrix δ ι ℂ) (hV : Vᴴ*V=1) (i j : δ) (z : Outcome ι) :
    ‖projectionEffect V z i j‖ ≤ Fintype.card ι + ‖((1 : Matrix δ δ ℂ)-V*Vᴴ) i j‖ := by
  rcases z with U | u
  · have he : V*projector U*Vᴴ = (SupportCompression.embedDensity V hV U.density).matrix := by
      rw [projector_eq_density]
      rfl
    change ‖(Fintype.card ι : ℂ)*((V*projector U*Vᴴ) i j)‖ ≤ _
    rw [he, norm_mul, Complex.norm_natCast]
    calc
      _ ≤ (Fintype.card ι : ℝ) := mul_le_of_le_one_right (Nat.cast_nonneg _)
        (PureCovariant.density_entry_norm_le_one _ i j)
      _ ≤ _ := le_add_of_nonneg_right (norm_nonneg _)
  · change ‖((1 : Matrix δ δ ℂ)-V*Vᴴ) i j‖ ≤ _
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)

lemma projectionEffect_integrable (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (V : Matrix δ ι ℂ) (hV : Vᴴ*V=1) (i j : δ) :
    Integrable (fun z => projectionEffect V z i j) (projectionReference μ) := by
  letI : IsFiniteMeasure (projectionReference μ) := by unfold projectionReference; infer_instance
  apply Integrable.of_bound (projectionEffect_measurable V i j).aestronglyMeasurable
    (Fintype.card ι + ‖((1 : Matrix δ δ ℂ)-V*Vᴴ) i j‖)
  exact ae_of_all _ (projectionEffect_entry_bound V hV i j)

lemma projection_success_integral (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (V : Matrix δ ι ℂ) (i j : δ) :
    (∫ U, projectionEffect V (Sum.inl U) i j ∂μ) = (V*Vᴴ) i j := by
  have hk : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hin : ∀ a, Integrable (fun U : OneCopyObservation.PureFrame ι =>
      ∑ b, V i b * projector U b a) μ := fun a =>
    integrable_finset_sum Finset.univ (fun b _ => (projector_entry_integrable μ b a).const_mul (V i b))
  change (∫ U, (Fintype.card ι : ℂ) * (∑ a, (∑ b, V i b * projector U b a)*Vᴴ a j) ∂μ) = _
  rw [integral_const_mul, integral_finset_sum Finset.univ (fun a _ => (hin a).mul_const (Vᴴ a j))]
  simp_rw [integral_mul_const]
  have hint : ∀ a, (∫ U : OneCopyObservation.PureFrame ι, ∑ b, V i b*projector U b a ∂μ) =
      V i a / (Fintype.card ι : ℂ) := by
    intro a
    rw [integral_finset_sum Finset.univ (fun b _ => (projector_entry_integrable μ b a).const_mul (V i b))]
    simp_rw [integral_const_mul, H.first]
    rw [Finset.sum_eq_single a]
    · simp [Matrix.one_apply, div_eq_mul_inv]
    · intro b _ hba
      simp [Matrix.one_apply, hba]
    · simp
  simp_rw [hint]
  rw [Finset.mul_sum]
  change (∑ a, (Fintype.card ι : ℂ) * (V i a / (Fintype.card ι : ℂ) * Vᴴ a j)) =
    ∑ a, V i a * Vᴴ a j
  apply Finset.sum_congr rfl
  intro a _
  field_simp

lemma projectionEffect_total (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (V : Matrix δ ι ℂ) (hV : Vᴴ*V=1) (i j : δ) :
    (∫ z, projectionEffect V z i j ∂projectionReference μ) = (1 : Matrix δ δ ℂ) i j := by
  have hi := projectionEffect_integrable μ V hV i j
  rw [projectionReference, integrable_add_measure] at hi
  rw [projectionReference, integral_add_measure hi.1 hi.2,
    integral_map measurable_inl.aemeasurable (projectionEffect_measurable V i j).aestronglyMeasurable,
    integral_dirac' _ _ (projectionEffect_measurable V i j).stronglyMeasurable,
    projection_success_integral μ H V i j]
  change (V*Vᴴ) i j + ((1 : Matrix δ δ ℂ) i j - (V*Vᴴ) i j) = _
  ring

/-- A genuine ambient one-copy dominated POVM with a state-independent finite
reference measure. It includes both covariant success and projection failure. -/
def projectionPOVM (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (V : Matrix δ ι ℂ) (hV : Vᴴ*V=1) :
    ContinuousPOVM.DominatedPOVM δ (Outcome ι) where
  reference := projectionReference μ
  reference_finite := by unfold projectionReference; infer_instance
  effect := projectionEffect V
  entry_measurable := projectionEffect_measurable V
  positive_ae := ae_of_all _ (projectionEffect_positive V hV)
  entry_integrable := projectionEffect_integrable μ V hV
  total := projectionEffect_total μ H V hV

/-- Born's full ambient density gives exactly the unconditional covariant
likelihood of its actual block on success. -/
lemma projectionPOVM_born_success (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (V : Matrix δ ι ℂ) (hV : Vᴴ*V=1)
    (ρ : Density δ) (U : OneCopyObservation.PureFrame ι) :
    (projectionPOVM μ H V hV).born ρ (Sum.inl U) = likelihood (trueBlock V ρ) U := by
  have he : Matrix.trace (ρ.matrix*(V*projector U*Vᴴ)) = Matrix.trace (projector U*trueBlock V ρ) := by
    calc
      _ = Matrix.trace ((ρ.matrix*V)*projector U*Vᴴ) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Vᴴ*(ρ.matrix*V)*projector U) := Matrix.trace_mul_cycle _ _ _
      _ = _ := by rw [Matrix.trace_mul_comm]; simp only [trueBlock, Matrix.mul_assoc]
  change (Matrix.trace (ρ.matrix*((Fintype.card ι : ℂ) • (V*projector U*Vᴴ)))).re = _
  rw [Matrix.mul_smul, Matrix.trace_smul]
  change ((Fintype.card ι : ℂ)*Matrix.trace (ρ.matrix*(V*projector U*Vᴴ))).re = _
  rw [he]
  simp [likelihood]

lemma projectionPOVM_born_failure (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (V : Matrix δ ι ℂ) (hV : Vᴴ*V=1) (ρ : Density δ) :
    (projectionPOVM μ H V hV).born ρ (Sum.inr ()) = 1-(Matrix.trace (trueBlock V ρ)).re := by
  have he : Matrix.trace (ρ.matrix*(V*Vᴴ)) = Matrix.trace (trueBlock V ρ) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    rfl
  change (Matrix.trace (ρ.matrix*(1-V*Vᴴ))).re = _
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, ρ.trace_one, he, Complex.sub_re, Complex.one_re]

/-- Equality of the genuine ambient Born outcome measure and the statistical
law used above. Thus failed projections are actual outcomes consuming full copies. -/
theorem projectionPOVM_outcomeMeasure (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (V : Matrix δ ι ℂ) (hV : Vᴴ*V=1) (ρ : Density δ) :
    (projectionPOVM μ H V hV).outcomeMeasure ρ = outcomeMeasure μ (trueBlock V ρ) := by
  let M := projectionPOVM μ H V hV
  have hb : Measurable (fun z => ENNReal.ofReal (M.born ρ z)) := (M.born_measurable ρ).ennreal_ofReal
  ext s hs
  rw [M.outcomeMeasure_apply ρ hs]
  change (∫⁻ z in s, ENNReal.ofReal (M.born ρ z) ∂(μ.map Sum.inl+Measure.dirac (Sum.inr ()))) = _
  rw [Measure.restrict_add, lintegral_add_measure]
  have hl : (∫⁻ z in s, ENNReal.ofReal (M.born ρ z) ∂μ.map Sum.inl) =
      successMeasure μ (trueBlock V ρ) (Sum.inl ⁻¹' s) := by
    rw [setLIntegral_map hs hb measurable_inl, successMeasure, withDensity_apply _ (measurable_inl hs)]
    simp only [M, projectionPOVM_born_success μ H V hV ρ]
  have hf : (∫⁻ z in s, ENNReal.ofReal (M.born ρ z) ∂Measure.dirac (Sum.inr ())) =
      ENNReal.ofReal (1-(Matrix.trace (trueBlock V ρ)).re)*Measure.dirac (Sum.inr ()) s := by
    rw [← lintegral_indicator hs, lintegral_dirac' _ (hb.indicator hs), Measure.dirac_apply' _ hs]
    by_cases hm : Sum.inr () ∈ s
    · simp only [Set.indicator_of_mem hm, Pi.one_apply, mul_one, M,
        projectionPOVM_born_failure μ H V hV ρ]
    · simp only [Set.indicator_of_notMem hm, mul_zero]
  rw [hl, hf, outcomeMeasure, Measure.add_apply, Measure.map_apply measurable_inl hs]
  rfl

end FullCopyProjection

/-- A genuine Borel reconstruction using the separately constructed ordered
Borel basis. It is not identified with mathlib's arbitrary eigenvector choice. -/
def borelEstimate (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (N r : ℕ) : (Fin N → Outcome ι) → Matrix ι ι ℂ :=
  estimateUsing (MeasurableSpectralSelection.basis S) N r

lemma borelEstimate_measurable (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (N r : ℕ) : Measurable (borelEstimate (ι:=ι) S N r) := by
  change Measurable (fun z : Fin N → Outcome ι =>
    MeasurableSpectralSelection.rankTruncation S r ⟨sampleAverage N z, sampleAverage_hermitian N z⟩)
  exact (MeasurableSpectralSelection.measurable_rankTruncation S r).comp
    (sampleAverage_subtype_measurable N)

lemma borelEstimate_posSemidef (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (N r : ℕ) (z : Fin N → Outcome ι) : (borelEstimate S N r z).PosSemidef :=
  rankTruncationWith_posSemidef _ _ _ _

lemma borelEstimate_rank (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (N r : ℕ) (z : Fin N → Outcome ι) : (borelEstimate S N r z).rank ≤ r :=
  rankTruncationWith_rank _ _ _ _

/-- Actual measurable error event, including at repeated eigenvalues. -/
lemma borelEstimate_success_measurable (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (N r : ℕ) (R : Matrix ι ι ℂ) (η : ℝ) :
    MeasurableSet {z | ShellAccounting.frobeniusSq (borelEstimate S N r z-R) ≤ η} :=
  measurableSet_le (frobenius_error_measurable _ (borelEstimate_measurable S N r) R) measurable_const

/-- The native measurable PSD routine with the explicit integer copy choice. -/
theorem borelEstimate_success (B : MatrixBernsteinInput ι) (Weyl : WeylEigenvalueInput ι)
    (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (hw : (Matrix.trace R).re ≤ 1) (r : ℕ) (hr : 0 < r) (hrank : R.rank ≤ r)
    (W η β : ℝ) (hW : (Matrix.trace R).re ≤ W) (hη : 0 < η)
    (hβ : 0 < β) (hβ₁ : β < 1/2) :
    ENNReal.ofReal (1-β) ≤ sampleMeasure μ R (copies (ι:=ι) r W η β)
      {z | ShellAccounting.frobeniusSq (borelEstimate S (copies (ι:=ι) r W η β) r z-R) ≤ η} := by
  letI : IsProbabilityMeasure (outcomeMeasure μ R) := ⟨outcomeMeasure_univ μ H R hR hw⟩
  letI : IsProbabilityMeasure (sampleMeasure μ R (copies (ι:=ι) r W η β)) := by
    unfold sampleMeasure
    infer_instance
  apply success_lower_from_failure _ _ η β (le_of_lt hβ)
  exact estimateUsing_failure_le_beta B Weyl (MeasurableSpectralSelection.basis S)
    (MeasurableSpectralSelection.basis_reconstruct S) μ H R hR hw r hr hrank W η β hW hη hβ hβ₁

/-- Lemma 5.3 in the nontrivial branch: an actual Borel PSD matrix estimator,
actual measurable success event, min(r,k) rank promise, full-copy product law,
and an explicit integer version of the source sample bound. -/
theorem lemma_5_3_nontrivial (B : MatrixBernsteinInput ι) (Weyl : WeylEigenvalueInput ι)
    (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (r : ℕ) (hr : 0 < r) (hrank : R.rank ≤ r) (W η β : ℝ)
    (hW : (Matrix.trace R).re ≤ W) (hW₁ : W ≤ 1) (hη : 0 < η) (hηW : η < W^2)
    (hβ : 0 < β) (hβ₁ : β < 1/2) :
    let r' := min r (Fintype.card ι)
    let N := copies (ι:=ι) r' W η β
    let T := borelEstimate (ι:=ι) S N r'
    0 < N ∧ Measurable T ∧ (∀ z, (T z).PosSemidef ∧ (T z).rank ≤ r') ∧
      MeasurableSet {z | ShellAccounting.frobeniusSq (T z-R) ≤ η} ∧
      ENNReal.ofReal (1-β) ≤ sampleMeasure μ R N {z | ShellAccounting.frobeniusSq (T z-R) ≤ η} ∧
      (N:ℝ) < 72*((r':ℝ)*Fintype.card ι*W/η + Fintype.card ι*Real.sqrt ((r':ℝ)/η)) *
        Real.log (2*(Fintype.card ι:ℝ)/β) := by
  dsimp only
  have hr' : 0 < min r (Fintype.card ι) := lt_min hr Fintype.card_pos
  have hW₀ : 0 ≤ W := ((hR.trace_nonneg).1).trans hW
  refine ⟨copies_pos _ hr' W η β hW₀ hη hβ hβ₁, borelEstimate_measurable S _ _,
    (fun z => ⟨borelEstimate_posSemidef S _ _ z, borelEstimate_rank S _ _ z⟩),
    borelEstimate_success_measurable S _ _ R η, ?_, ?_⟩
  · exact borelEstimate_success B Weyl S μ H R hR (hW.trans hW₁) _ hr' (rank_promise_min R r hrank)
      W η β hW hη hβ hβ₁
  · exact copies_source_bound _ hr' W η β hW₀ hW₁ hη hηW hβ hβ₁

/-- Full PSD form of Lemma 5.3, with the zero-copy branch and a measurable
reconstruction of the actual full-copy observation data. The trace-one
water-filling extension in the following source paragraph is a separate claim. -/
theorem lemma_5_3 (B : MatrixBernsteinInput ι) (Weyl : WeylEigenvalueInput ι)
    (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (R : Matrix ι ι ℂ) (hR : R.PosSemidef)
    (r : ℕ) (hr : 0 < r) (hrank : R.rank ≤ r) (W η β : ℝ)
    (hW : (Matrix.trace R).re ≤ W) (hW₁ : W ≤ 1) (hη : 0 < η)
    (hβ : 0 < β) (hβ₁ : β < 1/2) :
    ∃ (N : ℕ) (T : (Fin N → Outcome ι) → Matrix ι ι ℂ),
      Measurable T ∧ (∀ z, (T z).PosSemidef ∧ (T z).rank ≤ min r (Fintype.card ι)) ∧
      MeasurableSet {z | ShellAccounting.frobeniusSq (T z-R) ≤ η} ∧
      ENNReal.ofReal (1-β) ≤ sampleMeasure μ R N {z | ShellAccounting.frobeniusSq (T z-R) ≤ η} ∧
      (if W^2 ≤ η then N=0 else (N:ℝ) <
        72*((min r (Fintype.card ι):ℝ)*Fintype.card ι*W/η +
          Fintype.card ι*Real.sqrt ((min r (Fintype.card ι):ℝ)/η))*
            Real.log (2*(Fintype.card ι:ℝ)/β)) := by
  by_cases hz : W^2 ≤ η
  · letI : IsProbabilityMeasure (outcomeMeasure μ R) := ⟨outcomeMeasure_univ μ H R hR (hW.trans hW₁)⟩
    letI : IsProbabilityMeasure (sampleMeasure μ R 0) := by unfold sampleMeasure; infer_instance
    have he := (zero_branch R hR W η hW hz).2
    refine ⟨0, (fun _ => 0), measurable_const, (fun _ => ⟨Matrix.PosSemidef.zero, ?_⟩), ?_, ?_, ?_⟩
    · simp only [Matrix.rank_zero]
      exact Nat.zero_le _
    · have hu : {z : Fin 0 → Outcome ι | ShellAccounting.frobeniusSq (0-R) ≤ η} = Set.univ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact he
      rw [hu]
      exact MeasurableSet.univ
    · have hu : {z : Fin 0 → Outcome ι | ShellAccounting.frobeniusSq (0-R) ≤ η} = Set.univ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact he
      rw [hu, measure_univ]
      have h := ENNReal.ofReal_le_ofReal (show 1-β ≤ 1 by linarith)
      simpa only [ENNReal.ofReal_one] using h
    · simp only [hz, ↓reduceIte]
  · have hn := lemma_5_3_nontrivial B Weyl S μ H R hR r hr hrank W η β hW hW₁ hη (lt_of_not_ge hz) hβ hβ₁
    refine ⟨copies (ι:=ι) (min r (Fintype.card ι)) W η β,
      borelEstimate S _ _, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1, ?_⟩
    simpa only [hz, ↓reduceIte, Nat.cast_min] using hn.2.2.2.2.2

end Paper26.OneCopySubmatrix
