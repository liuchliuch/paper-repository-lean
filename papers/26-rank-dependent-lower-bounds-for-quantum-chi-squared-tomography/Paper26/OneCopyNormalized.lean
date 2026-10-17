import Paper26.OneCopySubmatrix
import Mathlib.Topology.Order.IntermediateValue

/-!
# Trace-one water-filling for the one-copy routine

This is the actual normalized spectral clipping in S5.SS2.p5. Scalar threshold
existence, uniqueness, matrix positivity/trace/rank, and the approximation
bounds are proved here. The only selection input is the same general Borel
compact-fiber theorem already used for the ordered spectral basis.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory
namespace Paper26.OneCopyNormalized
open QuantumModel OneCopyObservation OneCopySubmatrix

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))
local instance matrixBorelSpace (m n : Type*) [Fintype m] [Fintype n] :
    BorelSpace (Matrix m n ℂ) := inferInstanceAs (BorelSpace (m → n → ℂ))
local instance : CStarAlgebra (Matrix ι ι ℂ) where

/-- Keep the first r spectral entries and shift their positive parts. -/
def clippedSpectrum (a : ι → ℝ) (r : ℕ) (h : ℝ) (i : ι) : ℝ :=
  if (orderedIndex i).val < r then max (a i-h) 0 else 0

def clippedMass (a : ι → ℝ) (r : ℕ) (h : ℝ) : ℝ := ∑ i, clippedSpectrum a r h i

lemma clippedSpectrum_nonneg (a : ι → ℝ) (r : ℕ) (h : ℝ) (i : ι) :
    0 ≤ clippedSpectrum a r h i := by
  unfold clippedSpectrum
  split_ifs
  · exact le_max_right _ _
  · exact le_rfl

lemma clippedMass_continuous (a : ι → ℝ) (r : ℕ) : Continuous (clippedMass a r) := by
  apply continuous_finset_sum
  intro i _
  unfold clippedSpectrum
  split_ifs
  · exact (continuous_const.sub continuous_id).max continuous_const
  · exact continuous_const

lemma clippedSpectrum_antitone (a : ι → ℝ) (r : ℕ) (i : ι) :
    Antitone (fun h => clippedSpectrum a r h i) := by
  intro h g hhg
  unfold clippedSpectrum
  split_ifs
  · exact max_le_max (by linarith) le_rfl
  · exact le_rfl

lemma clippedMass_strict (a : ι → ℝ) (r : ℕ) (h g : ℝ) (hhg : h < g)
    (hpos : 0 < clippedMass a r g) : clippedMass a r g < clippedMass a r h := by
  have hex : ∃ i, 0 < clippedSpectrum a r g i := by
    by_contra hn
    push_neg at hn
    have hz := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => hn i)
    exact not_lt_of_ge hz hpos
  obtain ⟨i, hi⟩ := hex
  have hkeep : (orderedIndex i).val < r := by
    by_contra hn
    simp only [clippedSpectrum, hn, ↓reduceIte] at hi
    exact lt_irrefl _ hi
  have hgi : 0 < a i-g := by
    by_contra hn
    have he := max_eq_right (le_of_not_gt hn)
    simp only [clippedSpectrum, hkeep, ↓reduceIte, he] at hi
    exact lt_irrefl _ hi
  have hhi : 0 ≤ a i-h := by linarith
  have hstrict : clippedSpectrum a r g i < clippedSpectrum a r h i := by
    simp only [clippedSpectrum, hkeep, ↓reduceIte, max_eq_left (le_of_lt hgi), max_eq_left hhi]
    linarith
  apply Finset.sum_lt_sum (fun j _ => clippedSpectrum_antitone a r j (le_of_lt hhg))
  exact ⟨i, Finset.mem_univ i, hstrict⟩

lemma threshold_unique (a : ι → ℝ) (r : ℕ) (h g : ℝ)
    (hh : clippedMass a r h=1) (hg : clippedMass a r g=1) : h=g := by
  rcases lt_trichotomy h g with hlt | heq | hgt
  · have hs := clippedMass_strict a r h g hlt (by rw [hg]; norm_num)
    rw [hh, hg] at hs
    exact (lt_irrefl _ hs).elim
  · exact heq
  · have hs := clippedMass_strict a r g h hgt (by rw [hh]; norm_num)
    rw [hh, hg] at hs
    exact (lt_irrefl _ hs).elim

/-- Every nonempty retained prefix has a unique scalar water-filling threshold. -/
theorem threshold_exists (a : ι → ℝ) (r : ℕ) (hr : 0 < r) :
    ∃ h, clippedMass a r h=1 := by
  let b := 1 + ∑ i, |a i|
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have ha : ∀ i, |a i| ≤ ∑ j, |a j| := fun i =>
    Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
  have hu : clippedMass a r b = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    unfold clippedSpectrum
    split_ifs
    · have hle : a i-b ≤ 0 := by dsimp [b]; linarith [le_abs_self (a i), ha i]
      exact max_eq_right hle
    · rfl
  let i₀ : ι := orderedIndex.symm ⟨0, Fintype.card_pos⟩
  have hi₀ : (orderedIndex i₀).val < r := by simpa only [i₀, Equiv.apply_symm_apply] using hr
  have hl₀ : 1 ≤ clippedSpectrum a r (-b) i₀ := by
    have ht : 1 ≤ a i₀+b := by dsimp [b]; linarith [neg_abs_le (a i₀), ha i₀]
    unfold clippedSpectrum
    rw [if_pos hi₀]
    have hm := le_max_left (a i₀-(-b)) 0
    linarith
  have hl : 1 ≤ clippedMass a r (-b) := by
    exact hl₀.trans (Finset.single_le_sum (fun j _ => clippedSpectrum_nonneg a r (-b) j) (Finset.mem_univ i₀))
  have hv := intermediate_value_Icc' (show -b ≤ b by linarith)
    (clippedMass_continuous a r).continuousOn
  have hmem : (1:ℝ) ∈ Set.Icc (clippedMass a r b) (clippedMass a r (-b)) := by rw [hu]; exact ⟨by norm_num, hl⟩
  obtain ⟨h, _, hh⟩ := hv hmem
  exact ⟨h, hh⟩

/-- The graph of the actual scalar water-filling equation. ULift only aligns
universes so the same general selection input as the basis can be reused. -/
def ThresholdRelation (r : ℕ) :
    Set (MeasurableSpectralSelection.HermitianMatrix ι × ULift.{u} ℝ) :=
  {p | clippedMass p.1.property.eigenvalues r p.2.down = 1}

lemma thresholdRelation_measurable (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (r : ℕ) : MeasurableSet (ThresholdRelation (ι:=ι) r) := by
  apply measurableSet_eq_fun _ measurable_const
  apply Finset.measurable_sum Finset.univ
  intro i _
  unfold clippedSpectrum
  split_ifs
  · exact (((MeasurableSpectralSelection.measurable_eigenvalue S i).comp measurable_fst).sub
      (measurable_down.comp measurable_snd)).max measurable_const
  · exact measurable_const

lemma thresholdRelation_nonempty (r : ℕ) (hr : 0 < r)
    (A : MeasurableSpectralSelection.HermitianMatrix ι) :
    {h : ULift.{u} ℝ | (A,h) ∈ ThresholdRelation r}.Nonempty := by
  obtain ⟨h, hh⟩ := threshold_exists A.property.eigenvalues r hr
  exact ⟨ULift.up h, hh⟩

lemma thresholdRelation_compact (r : ℕ) (hr : 0 < r)
    (A : MeasurableSpectralSelection.HermitianMatrix ι) :
    IsCompact {h : ULift.{u} ℝ | (A,h) ∈ ThresholdRelation r} := by
  obtain ⟨h, hh⟩ := threshold_exists A.property.eigenvalues r hr
  have he : {g : ULift.{u} ℝ | (A,g) ∈ ThresholdRelation r} = {ULift.up h} := by
    ext g
    constructor
    · intro hg
      apply Set.mem_singleton_iff.mpr
      apply ULift.ext
      exact threshold_unique A.property.eigenvalues r g.down h hg hh
    · intro hg
      rw [Set.mem_singleton_iff] at hg
      subst g
      exact hh
  rw [he]
  exact isCompact_singleton

/-- Existence of a measurable threshold uses only the generic compact-section
Borel selection theorem. The actual equation and every hypothesis are internal. -/
theorem exists_measurable_threshold
    (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u}) (r : ℕ) (hr : 0 < r) :
    ∃ f : MeasurableSpectralSelection.HermitianMatrix ι → ULift.{u} ℝ,
      Measurable f ∧ ∀ A, clippedMass A.property.eigenvalues r (f A).down = 1 := by
  exact S.selection _ _ (ThresholdRelation r) (thresholdRelation_measurable S r)
    (thresholdRelation_nonempty r hr) (thresholdRelation_compact r hr)

def liftedThreshold (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (r : ℕ) (hr : 0 < r) : MeasurableSpectralSelection.HermitianMatrix ι → ULift.{u} ℝ :=
  Classical.choose (exists_measurable_threshold S r hr)

def threshold (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (r : ℕ) (hr : 0 < r) (A : MeasurableSpectralSelection.HermitianMatrix ι) : ℝ :=
  (liftedThreshold S r hr A).down

lemma threshold_measurable (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (r : ℕ) (hr : 0 < r) : Measurable (threshold (ι:=ι) S r hr) :=
  measurable_down.comp (Classical.choose_spec (exists_measurable_threshold S r hr)).1

lemma threshold_mass (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (r : ℕ) (hr : 0 < r) (A : MeasurableSpectralSelection.HermitianMatrix ι) :
    clippedMass A.property.eigenvalues r (threshold S r hr A) = 1 :=
  (Classical.choose_spec (exists_measurable_threshold S r hr)).2 A

def normalizedSpectrum (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (r : ℕ) (hr : 0 < r) (A : MeasurableSpectralSelection.HermitianMatrix ι) (i : ι) : ℝ :=
  clippedSpectrum A.property.eigenvalues r (threshold S r hr A) i

def normalizedMatrix (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (r : ℕ) (hr : 0 < r) (A : MeasurableSpectralSelection.HermitianMatrix ι) : Matrix ι ι ℂ :=
  Normalization.conjugate (MeasurableSpectralSelection.basis S A : Matrix ι ι ℂ)
    (Normalization.diagonalMatrix (normalizedSpectrum S r hr A))

lemma normalizedSpectrum_measurable (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (r : ℕ) (hr : 0 < r) : Measurable (normalizedSpectrum (ι:=ι) S r hr) := by
  apply measurable_pi_lambda
  intro i
  unfold normalizedSpectrum clippedSpectrum
  split_ifs
  · exact ((MeasurableSpectralSelection.measurable_eigenvalue S i).sub (threshold_measurable S r hr)).max measurable_const
  · exact measurable_const

lemma normalizedMatrix_measurable (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (r : ℕ) (hr : 0 < r) : Measurable (normalizedMatrix (ι:=ι) S r hr) :=
  MeasurableSpectralSelection.measurable_conjugate_diagonal _ _
    (MeasurableSpectralSelection.measurable_basis_matrix S) (normalizedSpectrum_measurable S r hr)

lemma normalizedMatrix_posSemidef (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (r : ℕ) (hr : 0 < r) (A : MeasurableSpectralSelection.HermitianMatrix ι) :
    (normalizedMatrix S r hr A).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0:ℂ) ≤ (normalizedSpectrum S r hr A i : ℂ)
  exact_mod_cast clippedSpectrum_nonneg A.property.eigenvalues r (threshold S r hr A) i

lemma normalizedMatrix_trace_one (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (r : ℕ) (hr : 0 < r) (A : MeasurableSpectralSelection.HermitianMatrix ι) :
    Matrix.trace (normalizedMatrix S r hr A) = 1 := by
  rw [normalizedMatrix, Normalization.trace_conjugate _ _ (PositiveLossBridge.unitary_left _)]
  simp only [Normalization.diagonalMatrix, Matrix.trace_diagonal, ← Complex.ofReal_sum]
  change ((clippedMass A.property.eigenvalues r (threshold S r hr A) : ℝ) : ℂ) = 1
  rw [threshold_mass]
  norm_num

def normalizedDensity (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (r : ℕ) (hr : 0 < r) (A : MeasurableSpectralSelection.HermitianMatrix ι) : Density ι where
  matrix := normalizedMatrix S r hr A
  positive := normalizedMatrix_posSemidef S r hr A
  trace_one := normalizedMatrix_trace_one S r hr A

lemma normalizedDensity_measurable (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (r : ℕ) (hr : 0 < r) : Measurable (normalizedDensity (ι:=ι) S r hr) := by
  intro s hs
  rcases hs with ⟨t, ht, rfl⟩
  exact normalizedMatrix_measurable S r hr ht

lemma normalizedMatrix_rank (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (r : ℕ) (hr : 0 < r) (A : MeasurableSpectralSelection.HermitianMatrix ι) :
    (normalizedMatrix S r hr A).rank ≤ r := by
  let d : ι → ℂ := fun i => (normalizedSpectrum S r hr A i : ℂ)
  have hs : ∀ i, d i ≠ 0 → (orderedIndex i).val < r := by
    intro i hi
    by_contra hn
    exact hi (by simp [d, normalizedSpectrum, clippedSpectrum, hn])
  let f : {i // d i ≠ 0} → Fin r := fun i => ⟨(orderedIndex i.val).val, hs i.val i.property⟩
  have hf : Function.Injective f := by
    intro i j h
    apply Subtype.ext
    apply orderedIndex.injective
    apply Fin.ext
    exact congrArg (fun z : Fin r => z.val) h
  calc
    (normalizedMatrix S r hr A).rank ≤ (Matrix.diagonal d).rank :=
      (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    _ = Fintype.card {i // d i ≠ 0} := Matrix.rank_diagonal d
    _ ≤ r := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

lemma retained_true_mass (ρ : Density ι) (r : ℕ) (hrank : ρ.matrix.rank ≤ r) :
    (∑ i, if (orderedIndex i).val < r then ρ.hermitian.eigenvalues i else 0) = 1 := by
  have hp : ∀ i, (if (orderedIndex i).val < r then ρ.hermitian.eigenvalues i else 0) =
      ρ.hermitian.eigenvalues i := by
    intro i
    split_ifs with hi
    · rfl
    · rw [eigenvalues_ordered]
      exact (ordered_eigenvalue_zero_of_rank_le ρ.matrix ρ.positive r hrank (orderedIndex i) (by omega)).symm
  simp_rw [hp]
  exact ρ.spectrum_sum

/-- On the operator-error event the genuine selected water-filling threshold
lies in [-u,u]. The argument proves the source's two retained-sum inequalities. -/
theorem threshold_between (Weyl : WeylEigenvalueInput ι)
    (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (r : ℕ) (hr : 0 < r) (A : MeasurableSpectralSelection.HermitianMatrix ι)
    (ρ : Density ι) (hrank : ρ.matrix.rank ≤ r) (u : ℝ) (hu : 0 ≤ u)
    (herr : operatorNorm (A.val-ρ.matrix) ≤ u) :
    -u ≤ threshold S r hr A ∧ threshold S r hr A ≤ u := by
  have hpert : ∀ i, |A.property.eigenvalues i-ρ.hermitian.eigenvalues i| ≤ u := by
    intro i
    have h := (Weyl.perturbation A.val ρ.matrix A.property ρ.hermitian (orderedIndex i)).trans herr
    simpa only [← eigenvalues_ordered] using h
  have hupp : clippedMass A.property.eigenvalues r u ≤ 1 := by
    rw [← ρ.spectrum_sum]
    apply Finset.sum_le_sum
    intro i _
    have hnn := ρ.positive.eigenvalues_nonneg i
    unfold clippedSpectrum
    split_ifs
    · change max (A.property.eigenvalues i-u) 0 ≤ ρ.hermitian.eigenvalues i
      apply max_le
      · linarith [(abs_le.mp (hpert i)).2]
      · exact hnn
    · exact hnn
  have hlow : 1 ≤ clippedMass A.property.eigenvalues r (-u) := by
    rw [← retained_true_mass ρ r hrank]
    apply Finset.sum_le_sum
    intro i _
    unfold clippedSpectrum
    split_ifs
    · have hh := le_max_left (A.property.eigenvalues i-(-u)) 0
      linarith [(abs_le.mp (hpert i)).1]
    · exact le_rfl
  have hm := threshold_mass S r hr A
  constructor
  · by_contra hn
    have hs := clippedMass_strict A.property.eigenvalues r (threshold S r hr A) (-u)
      (lt_of_not_ge hn) (by linarith)
    rw [hm] at hs
    linarith
  · by_contra hn
    have hs := clippedMass_strict A.property.eigenvalues r u (threshold S r hr A)
      (lt_of_not_ge hn) (by rw [hm]; norm_num)
    rw [hm] at hs
    linarith

lemma normalized_spectrum_error (Weyl : WeylEigenvalueInput ι)
    (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (r : ℕ) (hr : 0 < r) (A : MeasurableSpectralSelection.HermitianMatrix ι)
    (ρ : Density ι) (hrank : ρ.matrix.rank ≤ r) (u : ℝ) (hu : 0 ≤ u)
    (herr : operatorNorm (A.val-ρ.matrix) ≤ u) (i : ι) :
    |normalizedSpectrum S r hr A i - A.property.eigenvalues i| ≤ u := by
  have hpert := (Weyl.perturbation A.val ρ.matrix A.property ρ.hermitian (orderedIndex i)).trans herr
  simp only [← eigenvalues_ordered] at hpert
  have hbetween := threshold_between Weyl S r hr A ρ hrank u hu herr
  unfold normalizedSpectrum clippedSpectrum
  split_ifs with hkeep
  · by_cases hμ : 0 ≤ A.property.eigenvalues i-threshold S r hr A
    · rw [max_eq_left hμ]
      have he : A.property.eigenvalues i-threshold S r hr A-A.property.eigenvalues i = -threshold S r hr A := by ring
      rw [he, abs_neg]
      exact abs_le.mpr hbetween
    · rw [max_eq_right (le_of_not_ge hμ), zero_sub, abs_neg]
      apply abs_le.mpr
      constructor
      · have hnn := ρ.positive.eigenvalues_nonneg i
        linarith [(abs_le.mp hpert).1]
      · linarith [le_of_not_ge hμ, hbetween.2]
  · have hz : ρ.hermitian.eigenvalues i = 0 := by
      rw [eigenvalues_ordered]
      exact ordered_eigenvalue_zero_of_rank_le ρ.matrix ρ.positive r hrank (orderedIndex i) (by omega)
    rw [hz, sub_zero] at hpert
    simpa only [zero_sub, abs_neg] using hpert

/-- The normalized matrix stays within u of the unnormalized Hermitian input,
using the actual Borel basis and its actual water-filling threshold. -/
theorem normalizedMatrix_distance_to_input (Weyl : WeylEigenvalueInput ι)
    (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (r : ℕ) (hr : 0 < r) (A : MeasurableSpectralSelection.HermitianMatrix ι)
    (ρ : Density ι) (hrank : ρ.matrix.rank ≤ r) (u : ℝ) (hu : 0 ≤ u)
    (herr : operatorNorm (A.val-ρ.matrix) ≤ u) :
    operatorNorm (normalizedMatrix S r hr A-A.val) ≤ u := by
  have hd : Normalization.diagonalMatrix (fun i => normalizedSpectrum S r hr A i-A.property.eigenvalues i) =
      Normalization.diagonalMatrix (normalizedSpectrum S r hr A)-Normalization.diagonalMatrix A.property.eigenvalues := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp [Normalization.diagonalMatrix]
    · simp [Normalization.diagonalMatrix, Matrix.diagonal, hij]
  have he : normalizedMatrix S r hr A-A.val =
      Normalization.conjugate (MeasurableSpectralSelection.basis S A : Matrix ι ι ℂ)
        (Normalization.diagonalMatrix (fun i => normalizedSpectrum S r hr A i-A.property.eigenvalues i)) := by
    rw [hd, Normalization.conjugate_sub, ← MeasurableSpectralSelection.basis_reconstruct S A]
    rfl
  rw [he]
  exact conjugate_diagonal_operatorNorm_le _ _ u hu
    (normalized_spectrum_error Weyl S r hr A ρ hrank u hu herr)

/-- The source's genuine trace-one clipping bound, on actual matrices. -/
theorem normalizedMatrix_error (Weyl : WeylEigenvalueInput ι)
    (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (r : ℕ) (hr : 0 < r) (A : MeasurableSpectralSelection.HermitianMatrix ι)
    (ρ : Density ι) (hrank : ρ.matrix.rank ≤ r) (u : ℝ) (hu : 0 ≤ u)
    (herr : operatorNorm (A.val-ρ.matrix) ≤ u) :
    operatorNorm (normalizedMatrix S r hr A-ρ.matrix) ≤ 2*u ∧
      ShellAccounting.frobeniusSq (normalizedMatrix S r hr A-ρ.matrix) ≤ 8*r*u^2 := by
  have hp := normalizedMatrix_posSemidef S r hr A
  have hrn := normalizedMatrix_rank S r hr A
  have ht := normalizedMatrix_distance_to_input Weyl S r hr A ρ hrank u hu herr
  have hn : operatorNorm (normalizedMatrix S r hr A-ρ.matrix) ≤ 2*u := by
    calc
      _ = operatorNorm ((normalizedMatrix S r hr A-A.val)+(A.val-ρ.matrix)) := by congr 1; abel
      _ ≤ operatorNorm (normalizedMatrix S r hr A-A.val)+operatorNorm (A.val-ρ.matrix) := by
        change ‖(normalizedMatrix S r hr A-A.val)+(A.val-ρ.matrix)‖ ≤
          ‖normalizedMatrix S r hr A-A.val‖+‖A.val-ρ.matrix‖
        exact norm_add_le _ _
      _ ≤ 2*u := by linarith
  have hdRank : (normalizedMatrix S r hr A-ρ.matrix).rank ≤ 2*r := by
    have ha := matrix_rank_add_le (normalizedMatrix S r hr A) (-ρ.matrix)
    have he : (-ρ.matrix).rank = ρ.matrix.rank := by
      change Module.finrank ℂ (LinearMap.range (-ρ.matrix).mulVecLin) = _
      have hl : (-ρ.matrix).mulVecLin = -ρ.matrix.mulVecLin := by ext x i; simp
      rw [hl, LinearMap.range_neg]
      rfl
    rw [he] at ha
    change (normalizedMatrix S r hr A-ρ.matrix).rank ≤ _ at ha
    omega
  refine ⟨hn, ?_⟩
  have hF := frobeniusSq_le_rank_mul_operatorNorm_sq _ (hp.1.sub ρ.hermitian)
  have hRℝ : ((normalizedMatrix S r hr A-ρ.matrix).rank : ℝ) ≤ 2*r := by exact_mod_cast hdRank
  have hn₀ : 0 ≤ operatorNorm (normalizedMatrix S r hr A-ρ.matrix) := norm_nonneg _
  calc
    _ ≤ (normalizedMatrix S r hr A-ρ.matrix).rank*operatorNorm (normalizedMatrix S r hr A-ρ.matrix)^2 := hF
    _ ≤ (2*r)*(2*u)^2 := by
      apply mul_le_mul hRℝ _ (sq_nonneg _) (by positivity)
      nlinarith
    _ = 8*r*u^2 := by ring

/-- A single measurable density reconstruction for all true input states. -/
def estimateDensity (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (N r : ℕ) (hr : 0 < r) (z : Fin N → Outcome ι) : Density ι :=
  normalizedDensity S r hr ⟨sampleAverage N z, sampleAverage_hermitian N z⟩

lemma estimateDensity_measurable (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (N r : ℕ) (hr : 0 < r) : Measurable (estimateDensity (ι:=ι) S N r hr) :=
  (normalizedDensity_measurable S r hr).comp (sampleAverage_subtype_measurable N)

def estimator (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (N r : ℕ) (hr : 0 < r) : ContinuousPOVM.Estimator ι (Fin N → Outcome ι) where
  estimate := estimateDensity S N r hr
  measurable_estimate := estimateDensity_measurable S N r hr

lemma estimateDensity_rank (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (N r : ℕ) (hr : 0 < r) (z : Fin N → Outcome ι) :
    (estimateDensity S N r hr z).matrix.rank ≤ r := normalizedMatrix_rank _ _ _ _

theorem normalized_error_tail (B : MatrixBernsteinInput ι) (Weyl : WeylEigenvalueInput ι)
    (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (ρ : Density ι) (r : ℕ) (hr : 0 < r) (hrank : ρ.matrix.rank ≤ r)
    (N : ℕ) (hN : 0 < N) (u : ℝ) (hu : 0 < u) (η : ℝ) (hη : 8*(r:ℝ)*u^2 ≤ η) :
    sampleMeasure μ ρ.matrix N {z | η < ShellAccounting.frobeniusSq ((estimateDensity S N r hr z).matrix-ρ.matrix)} ≤
      ENNReal.ofReal (2*(Fintype.card ι:ℝ)*Real.exp
        (-(N:ℝ)*u^2/(4*Fintype.card ι*1+(4/3:ℝ)*Fintype.card ι*u))) := by
  have hw : (Matrix.trace ρ.matrix).re ≤ 1 := by rw [ρ.trace_one]; norm_num
  apply le_trans (measure_mono (t := {z | u < operatorNorm (sampleAverage N z-ρ.matrix)}) _)
    (sampleAverage_operatorNorm_tail B μ H ρ.matrix ρ.positive hw N hN 1 hw u hu)
  intro z hz
  by_contra hn
  have he := normalizedMatrix_error Weyl S r hr ⟨sampleAverage N z, sampleAverage_hermitian N z⟩ ρ hrank u
    (le_of_lt hu) (le_of_not_gt hn)
  exact not_lt_of_ge (he.2.trans hη) hz

theorem normalized_failure_le_beta (B : MatrixBernsteinInput ι) (Weyl : WeylEigenvalueInput ι)
    (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (ρ : Density ι) (r : ℕ) (hr : 0 < r) (hrank : ρ.matrix.rank ≤ r)
    (η β : ℝ) (hη : 0 < η) (hβ : 0 < β) (hβ₁ : β < 1/2) :
    sampleMeasure μ ρ.matrix (copies (ι:=ι) r 1 η β)
      {z | η < ShellAccounting.frobeniusSq ((estimateDensity S (copies (ι:=ι) r 1 η β) r hr z).matrix-ρ.matrix)} ≤
      ENNReal.ofReal β := by
  have hn := copies_pos (ι:=ι) r hr 1 η β (by norm_num) hη hβ hβ₁
  have hu := deviation_pos r hr η hη
  apply (normalized_error_tail B Weyl S μ H ρ r hr hrank _ hn _ hu η (deviation_error r hr η hη)).trans
  apply ENNReal.ofReal_le_ofReal
  apply bernstein_factor_le _ _ 1 β hu (by norm_num) hβ
  rw [← copyBudget_eq_bernstein (ι:=ι) r hr 1 η β hη]
  exact Nat.le_ceil _

/-- The actual full-space covariant one-copy POVM, with its zero-Born-weight
failure atom retained. It is fixed independently of the true density. -/
def fullMeasurement (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) : ContinuousPOVM.DominatedPOVM ι (Outcome ι) :=
  projectionPOVM μ H (1 : Matrix ι ι ℂ) (by simp)

lemma fullMeasurement_outcomeMeasure (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (ρ : Density ι) :
    (fullMeasurement μ H).outcomeMeasure ρ = outcomeMeasure μ ρ.matrix := by
  simpa only [fullMeasurement, trueBlock, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] using
    projectionPOVM_outcomeMeasure μ H (1 : Matrix ι ι ℂ) (by simp) ρ

lemma fullSampleMeasure_eq (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (ρ : Density ι) (N : ℕ) :
    Measure.pi (fun _ : Fin N => (fullMeasurement μ H).outcomeMeasure ρ) = sampleMeasure μ ρ.matrix N := by
  unfold sampleMeasure
  congr 1
  funext i
  exact fullMeasurement_outcomeMeasure μ H ρ

/-- The normalized success event for the same fixed reconstruction, on the
actual product Born law of the same fixed full-space one-copy POVM. -/
theorem normalized_success (B : MatrixBernsteinInput ι) (Weyl : WeylEigenvalueInput ι)
    (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (ρ : Density ι) (r : ℕ) (hr : 0 < r) (hrank : ρ.matrix.rank ≤ r)
    (η β : ℝ) (hη : 0 < η) (hβ : 0 < β) (hβ₁ : β < 1/2) :
    ENNReal.ofReal (1-β) ≤
      (Measure.pi (fun _ : Fin (copies (ι:=ι) r 1 η β) => (fullMeasurement μ H).outcomeMeasure ρ))
      {z | ShellAccounting.frobeniusSq ((estimateDensity S (copies (ι:=ι) r 1 η β) r hr z).matrix-ρ.matrix) ≤ η} := by
  have hw : (Matrix.trace ρ.matrix).re ≤ 1 := by rw [ρ.trace_one]; norm_num
  letI : IsProbabilityMeasure (outcomeMeasure μ ρ.matrix) := ⟨outcomeMeasure_univ μ H ρ.matrix ρ.positive hw⟩
  letI : IsProbabilityMeasure (sampleMeasure μ ρ.matrix (copies (ι:=ι) r 1 η β)) := by unfold sampleMeasure; infer_instance
  rw [fullSampleMeasure_eq]
  apply success_lower_from_failure _ _ η β (le_of_lt hβ)
  exact normalized_failure_le_beta B Weyl S μ H ρ r hr hrank η β hη hβ hβ₁

/-- Uniform trace-one version: N and the actual measurable density estimator
are chosen before quantifying over the true rank-r density. This is the
normalized one-copy endpoint used for Eq. (12), in its nontrivial accuracy range. -/
theorem uniform_normalized_routine (B : MatrixBernsteinInput ι) (Weyl : WeylEigenvalueInput ι)
    (S : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (μ : Measure (OneCopyObservation.PureFrame ι)) [IsProbabilityMeasure μ]
    (H : HaarCoordinateMoments μ) (r : ℕ) (hr : 0 < r) (η β : ℝ)
    (hη : 0 < η) (hη₁ : η < 1) (hβ : 0 < β) (hβ₁ : β < 1/2) :
    ∃ (N : ℕ) (T : ContinuousPOVM.Estimator ι (Fin N → Outcome ι)),
      0 < N ∧ (∀ z, (T.estimate z).matrix.rank ≤ min r (Fintype.card ι)) ∧
      (N:ℝ) < 72*((min r (Fintype.card ι):ℝ)*Fintype.card ι/η +
          Fintype.card ι*Real.sqrt ((min r (Fintype.card ι):ℝ)/η))*
        Real.log (2*(Fintype.card ι:ℝ)/β) ∧
      ∀ ρ : Density ι, ρ.matrix.rank ≤ r →
        MeasurableSet {z | ShellAccounting.frobeniusSq ((T.estimate z).matrix-ρ.matrix) ≤ η} ∧
        ENNReal.ofReal (1-β) ≤
          (Measure.pi (fun _ : Fin N => (fullMeasurement μ H).outcomeMeasure ρ))
            {z | ShellAccounting.frobeniusSq ((T.estimate z).matrix-ρ.matrix) ≤ η} := by
  let r' := min r (Fintype.card ι)
  have hr' : 0 < r' := lt_min hr Fintype.card_pos
  let N := copies (ι:=ι) r' 1 η β
  let T := estimator (ι:=ι) S N r' hr'
  refine ⟨N, T, copies_pos (ι:=ι) r' hr' 1 η β (by norm_num) hη hβ hβ₁,
    (fun z => estimateDensity_rank S N r' hr' z), ?_, ?_⟩
  · have hb := copies_source_bound (ι:=ι) r' hr' 1 η β (by norm_num) (by norm_num) hη
      (by simpa only [one_pow] using hη₁) hβ hβ₁
    simpa only [mul_one, r', Nat.cast_min] using hb
  · intro ρ hρ
    constructor
    · exact measurableSet_le
        (frobenius_error_measurable (fun z => (T.estimate z).matrix) T.measurable_matrix ρ.matrix) measurable_const
    · exact normalized_success B Weyl S μ H ρ r' hr' (rank_promise_min ρ.matrix r hρ) η β hη hβ hβ₁

end Paper26.OneCopyNormalized
