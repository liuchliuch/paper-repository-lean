import Paper26.Normalization
import Paper26.ContinuousPOVM
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Borel ordered spectral selection

The sole classical input is the general compact-section Borel uniformization
theorem, a special case of Arsenin--Kunugui (Kechris, *Classical Descriptive Set
Theory*, Theorem 18.18; also Kechris--Wolman, *Invariant uniformization*,
Theorem 1.3, https://arxiv.org/abs/2405.15111). Its interface concerns arbitrary Polish spaces and
Borel relations, with no spectral, truncation, estimator, or learning conclusion.
The actual Hermitian/unitary relation and all its hypotheses are proved below.

The selected basis is a new Borel basis.  No measurability claim is made about
mathlib's pre-existing arbitrary classical choice of eigenvectors.
-/
noncomputable section
set_option maxHeartbeats 500000
open scoped BigOperators Matrix ComplexOrder
open MeasureTheory

namespace Paper26.MeasurableSpectralSelection

universe u v

/-- Generic compact-section uniformization.  Every relation and every
section remains quantified; there is no spectral or algorithmic field. -/
structure CompactFiberSelectionInput : Prop where
  selection : ∀ (X : Type u) (Y : Type v)
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (R : Set (X × Y)), MeasurableSet R →
    (∀ x, {y | (x, y) ∈ R}.Nonempty) →
    (∀ x, IsCompact {y | (x, y) ∈ R}) →
    ∃ f : X → Y, Measurable f ∧ ∀ x, (x, f x) ∈ R

local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))
local instance matrixBorelSpace (m n : Type*) [Fintype m] [Fintype n] :
    BorelSpace (Matrix m n ℂ) := inferInstanceAs (BorelSpace (m → n → ℂ))
local instance matrixPolishSpace (m n : Type*) [Fintype m] [Fintype n] :
    PolishSpace (Matrix m n ℂ) := inferInstanceAs (PolishSpace (m → n → ℂ))

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

abbrev HermitianMatrix (ι : Type*) [Fintype ι] := {A : Matrix ι ι ℂ // A.IsHermitian}

omit [Fintype ι] [DecidableEq ι] in
theorem hermitian_closed : IsClosed {A : Matrix ι ι ℂ | A.IsHermitian} :=
  isClosed_eq continuous_id.matrix_conjTranspose continuous_id

instance hermitianPolishSpace : PolishSpace (HermitianMatrix ι) :=
  (hermitian_closed (ι := ι)).polishSpace

theorem unitary_closed : IsClosed (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) := by
  have he : (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) =
      {U : Matrix ι ι ℂ | U * Uᴴ = 1} := by
    ext U
    exact Matrix.mem_unitaryGroup_iff
  rw [he]
  exact isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose) continuous_const

theorem unitary_compact : IsCompact (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) := by
  apply (isCompact_closedBall (0 : ℂ) 1).matrix.of_isClosed_subset unitary_closed
  intro U hU
  rw [Set.mem_matrix]
  intro i j
  simpa only [Metric.mem_closedBall, dist_zero_right] using entry_norm_bound_of_unitary hU i j

instance unitaryCompactSpace : CompactSpace (Matrix.unitaryGroup ι ℂ) :=
  isCompact_iff_compactSpace.1 unitary_compact

instance unitaryPolishSpace : PolishSpace (Matrix.unitaryGroup ι ℂ) :=
  (unitary_closed (ι := ι)).polishSpace

/-- The exact ordering map used in mathlib's Hermitian spectral theorem. -/
def orderedIndex : ι ≃ Fin (Fintype.card ι) :=
  (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm

def coordinates (A : HermitianMatrix ι) (U : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ :=
  (U : Matrix ι ι ℂ)ᴴ * A.val * (U : Matrix ι ι ℂ)

def diagonalValues (A : HermitianMatrix ι) (U : Matrix.unitaryGroup ι ℂ) (i : ι) : ℝ :=
  (coordinates A U i i).re

theorem continuous_coordinates :
    Continuous (fun p : HermitianMatrix ι × Matrix.unitaryGroup ι ℂ => coordinates p.1 p.2) := by
  exact ((continuous_subtype_val.comp continuous_snd).matrix_conjTranspose.matrix_mul
    (continuous_subtype_val.comp continuous_fst)).matrix_mul
      (continuous_subtype_val.comp continuous_snd)

theorem continuous_diagonalValues (i : ι) :
    Continuous (fun p : HermitianMatrix ι × Matrix.unitaryGroup ι ℂ => diagonalValues p.1 p.2 i) :=
  Complex.continuous_re.comp (continuous_coordinates.matrix_elem i i)

/-- Actual ordered diagonalization: the conjugated matrix is real diagonal,
and its diagonal decreases according to the fixed native ordering. -/
def OrderedRelation : Set (HermitianMatrix ι × Matrix.unitaryGroup ι ℂ) :=
  {p | coordinates p.1 p.2 = Normalization.diagonalMatrix (diagonalValues p.1 p.2) ∧
    ∀ i j, orderedIndex i ≤ orderedIndex j → diagonalValues p.1 p.2 j ≤ diagonalValues p.1 p.2 i}

theorem orderedRelation_closed : IsClosed (OrderedRelation (ι := ι)) := by
  have hd : Continuous (fun p : HermitianMatrix ι × Matrix.unitaryGroup ι ℂ =>
      Normalization.diagonalMatrix (diagonalValues p.1 p.2)) := by
    apply Continuous.matrix_diagonal
    exact continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_diagonalValues i)
  have hs (i j : ι) : IsClosed {p : HermitianMatrix ι × Matrix.unitaryGroup ι ℂ |
      orderedIndex i ≤ orderedIndex j → diagonalValues p.1 p.2 j ≤ diagonalValues p.1 p.2 i} := by
    by_cases hij : orderedIndex i ≤ orderedIndex j
    · simpa only [hij, true_implies] using
        isClosed_le (continuous_diagonalValues j) (continuous_diagonalValues i)
    · simp only [hij, false_implies, Set.setOf_true]
      exact isClosed_univ
  have hall : IsClosed {p : HermitianMatrix ι × Matrix.unitaryGroup ι ℂ |
      ∀ i j, orderedIndex i ≤ orderedIndex j → diagonalValues p.1 p.2 j ≤ diagonalValues p.1 p.2 i} := by
    simpa only [Set.setOf_forall] using
      (isClosed_iInter fun i => isClosed_iInter fun j => hs i j)
  exact (isClosed_eq continuous_coordinates hd).inter hall

theorem native_diagonalValues (A : HermitianMatrix ι) (i : ι) :
    diagonalValues A A.property.eigenvectorUnitary i = A.property.eigenvalues i := by
  have h := A.property.star_mul_self_mul_eq_diagonal
  change ((coordinates A A.property.eigenvectorUnitary) i i).re = _
  have heq : coordinates A A.property.eigenvectorUnitary =
      Normalization.diagonalMatrix A.property.eigenvalues := h
  rw [heq]
  simp [Normalization.diagonalMatrix]

theorem orderedRelation_nonempty (A : HermitianMatrix ι) :
    {U | (A, U) ∈ OrderedRelation}.Nonempty := by
  refine ⟨A.property.eigenvectorUnitary, ?_, ?_⟩
  · change coordinates A A.property.eigenvectorUnitary = _
    rw [show diagonalValues A A.property.eigenvectorUnitary = A.property.eigenvalues from
      funext (native_diagonalValues A)]
    exact A.property.star_mul_self_mul_eq_diagonal
  · intro i j hij
    simp_rw [native_diagonalValues]
    exact A.property.eigenvalues₀_antitone hij

theorem orderedRelation_compact (A : HermitianMatrix ι) :
    IsCompact {U | (A, U) ∈ OrderedRelation} :=
  (orderedRelation_closed.preimage (continuous_const.prodMk continuous_id)).isCompact

/-- Applying only generic compact-section uniformization gives an actual
Borel ordered unitary diagonalizer for every finite Hermitian matrix. -/
theorem exists_measurable_basis (S : CompactFiberSelectionInput.{u, u})
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    ∃ f : HermitianMatrix ι → Matrix.unitaryGroup ι ℂ,
      Measurable f ∧ ∀ A, (A, f A) ∈ OrderedRelation :=
  S.selection _ _ OrderedRelation orderedRelation_closed.measurableSet
    orderedRelation_nonempty orderedRelation_compact

theorem orderedRelation_reconstruct (A : HermitianMatrix ι) (U : Matrix.unitaryGroup ι ℂ)
    (hU : (A, U) ∈ OrderedRelation) :
    A.val = Normalization.conjugate (U : Matrix ι ι ℂ)
      (Normalization.diagonalMatrix (diagonalValues A U)) := by
  have hUR : (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)ᴴ = 1 := U.property.2
  rw [← hU.1]
  unfold Normalization.conjugate coordinates
  simp only [← Matrix.mul_assoc, hUR, Matrix.one_mul]
  simp only [Matrix.mul_assoc, hUR, Matrix.mul_one]

theorem diagonal_roots (a : ι → ℝ) :
    (Normalization.diagonalMatrix a).charpoly.roots =
      Finset.univ.val.map (fun i => (a i : ℂ)) := by
  rw [Normalization.diagonalMatrix, Matrix.charpoly_diagonal]
  change (Finset.univ.val.map (fun i => Polynomial.X - Polynomial.C (a i : ℂ))).prod.roots = _
  simpa only [Multiset.map_map, Function.comp_def] using
    Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map (fun i => (a i : ℂ)))

/-- An ordered real diagonalization has the genuine native ordered spectrum.
This identifies the selected basis with the same eigenvalues used by the
deterministic truncation bounds, without identifying eigenvector choices. -/
theorem ordered_diagonal_values (A : HermitianMatrix ι) (U : Matrix.unitaryGroup ι ℂ)
    (hU : (A, U) ∈ OrderedRelation) : diagonalValues A U = A.property.eigenvalues := by
  let a := diagonalValues A U
  have hUL : (U : Matrix ι ι ℂ)ᴴ * (U : Matrix ι ι ℂ) = 1 := U.property.1
  have hchar : A.val.charpoly = (Normalization.diagonalMatrix a).charpoly := by
    rw [orderedRelation_reconstruct A U hU]
    unfold Normalization.conjugate
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hUL, Matrix.one_mul]
  have hm : A.val.charpoly.roots.map Complex.re = Finset.univ.val.map a := by
    rw [hchar, diagonal_roots, Multiset.map_map]
    simp only [Function.comp_def, Complex.ofReal_re]
  have hlist : Finset.univ.val.map a =
      (List.ofFn (fun k => a (orderedIndex.symm k)) : Multiset ℝ) := by
    rw [← Fin.univ_val_map]
    change Finset.univ.val.map a =
      Finset.univ.val.map (a ∘ orderedIndex.symm)
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
  have hs : Antitone (fun k => a (orderedIndex.symm k)) := by
    intro i j hij
    exact hU.2 _ _ (by simpa only [Equiv.apply_symm_apply] using hij)
  have hsort : (A.val.charpoly.roots.map Complex.re).sort (· ≥ ·) =
      List.ofFn (fun k => a (orderedIndex.symm k)) := by
    rw [hm, hlist, Multiset.coe_sort, List.mergeSort_of_sorted]
    simpa [List.Sorted] using hs.ofFn_sorted
  have he : A.property.eigenvalues₀ = (fun k => a (orderedIndex.symm k)) := by
    apply List.ofFn_inj.1
    have hn := A.property.sort_roots_charpoly_eq_eigenvalues₀
    simp only [RCLike.re_eq_complex_re] at hn
    exact hn.symm.trans hsort
  funext i
  have hv := congrFun he (orderedIndex i)
  simpa only [Equiv.symm_apply_apply] using hv.symm

def basis (S : CompactFiberSelectionInput.{u, u}) : HermitianMatrix ι → Matrix.unitaryGroup ι ℂ :=
  Classical.choose (exists_measurable_basis S ι)

theorem measurable_basis (S : CompactFiberSelectionInput.{u, u}) : Measurable (basis (ι := ι) S) :=
  (Classical.choose_spec (exists_measurable_basis S ι)).1

theorem basis_relation (S : CompactFiberSelectionInput.{u, u}) (A : HermitianMatrix ι) :
    (A, basis S A) ∈ OrderedRelation :=
  (Classical.choose_spec (exists_measurable_basis S ι)).2 A

theorem basis_reconstruct (S : CompactFiberSelectionInput.{u, u}) (A : HermitianMatrix ι) :
    A.val = Normalization.conjugate (basis S A : Matrix ι ι ℂ)
      (Normalization.diagonalMatrix A.property.eigenvalues) := by
  have h := orderedRelation_reconstruct A (basis S A) (basis_relation S A)
  rwa [ordered_diagonal_values A (basis S A) (basis_relation S A)] at h

theorem measurable_basis_matrix (S : CompactFiberSelectionInput.{u, u}) :
    Measurable (fun A : HermitianMatrix ι => (basis S A : Matrix ι ι ℂ)) :=
  measurable_subtype_coe.comp (measurable_basis S)

theorem measurable_eigenvalue (S : CompactFiberSelectionInput.{u, u}) (i : ι) :
    Measurable (fun A : HermitianMatrix ι => A.property.eigenvalues i) := by
  have hm := (continuous_diagonalValues i).measurable.comp
    (measurable_id.prodMk (measurable_basis S))
  have he : (fun A : HermitianMatrix ι => diagonalValues A (basis S A) i) =
      (fun A => A.property.eigenvalues i) := by
    funext A
    exact congrFun (ordered_diagonal_values A (basis S A) (basis_relation S A)) i
  exact he ▸ hm

theorem measurable_eigenvalues (S : CompactFiberSelectionInput.{u, u}) :
    Measurable (fun A : HermitianMatrix ι => A.property.eigenvalues) :=
  measurable_pi_lambda _ (measurable_eigenvalue S)

theorem continuous_spectralConjugate :
    Continuous (fun p : Matrix ι ι ℂ × (ι → ℝ) =>
      Normalization.conjugate p.1 (Normalization.diagonalMatrix p.2)) := by
  have hd : Continuous (fun p : Matrix ι ι ℂ × (ι → ℝ) =>
      Normalization.diagonalMatrix p.2) := by
    apply Continuous.matrix_diagonal
    exact continuous_pi fun i => Complex.continuous_ofReal.comp
      ((continuous_apply i).comp continuous_snd)
  exact (continuous_fst.matrix_mul hd).matrix_mul continuous_fst.matrix_conjTranspose

theorem measurable_conjugate_diagonal {α : Type*} [MeasurableSpace α]
    (U : α → Matrix ι ι ℂ) (a : α → ι → ℝ) (hU : Measurable U) (ha : Measurable a) :
    Measurable (fun x => Normalization.conjugate (U x) (Normalization.diagonalMatrix (a x))) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have he (x : α) : Normalization.conjugate (U x) (Normalization.diagonalMatrix (a x)) i j =
      ∑ k, U x i k * (a x k : ℂ) * star (U x j k) := by
    simp [Normalization.conjugate, Normalization.diagonalMatrix,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  simp_rw [he]
  apply Finset.measurable_sum Finset.univ
  intro k _
  exact (((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hU)).mul
    (Complex.continuous_ofReal.measurable.comp ((measurable_pi_apply k).comp ha))).mul
      (Complex.continuous_conj.measurable.comp
        ((measurable_pi_apply k).comp ((measurable_pi_apply j).comp hU)))

def truncatedSpectrum (r : ℕ) (A : HermitianMatrix ι) (i : ι) : ℝ :=
  if (orderedIndex i).val < r then max (A.property.eigenvalues i) 0 else 0

def rankTruncation (S : CompactFiberSelectionInput.{u, u}) (r : ℕ) (A : HermitianMatrix ι) :
    Matrix ι ι ℂ :=
  Normalization.conjugate (basis S A : Matrix ι ι ℂ)
    (Normalization.diagonalMatrix (truncatedSpectrum r A))

theorem truncatedSpectrum_nonneg (r : ℕ) (A : HermitianMatrix ι) (i : ι) :
    0 ≤ truncatedSpectrum r A i := by
  unfold truncatedSpectrum
  split_ifs
  · exact le_max_right _ _
  · exact le_rfl

theorem measurable_truncatedSpectrum (S : CompactFiberSelectionInput.{u, u}) (r : ℕ) :
    Measurable (truncatedSpectrum (ι := ι) r) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : (orderedIndex i).val < r
  · simpa only [truncatedSpectrum, hi, ↓reduceIte] using (measurable_eigenvalue S i).max measurable_const
  · simpa only [truncatedSpectrum, hi, ↓reduceIte] using (measurable_const : Measurable (fun _ : HermitianMatrix ι => (0 : ℝ)))

/-- A genuine positive rank truncation with a Borel eigenbasis, including
degenerate eigenvalues at the cut. -/
theorem measurable_rankTruncation (S : CompactFiberSelectionInput.{u, u}) (r : ℕ) :
    Measurable (rankTruncation (ι := ι) S r) := by
  exact measurable_conjugate_diagonal _ _ (measurable_basis_matrix S) (measurable_truncatedSpectrum S r)

def thresholdSpectrum (t : ℝ) (A : HermitianMatrix ι) (i : ι) : ℝ :=
  if t < A.property.eigenvalues i then A.property.eigenvalues i else 0

def thresholdOutput (S : CompactFiberSelectionInput.{u, u}) (p : HermitianMatrix ι × ℝ) :
    Matrix ι ι ℂ := Normalization.conjugate (basis S p.1 : Matrix ι ι ℂ)
      (Normalization.diagonalMatrix (thresholdSpectrum p.2 p.1))

theorem measurable_thresholdSpectrum (S : CompactFiberSelectionInput.{u, u}) :
    Measurable (fun p : HermitianMatrix ι × ℝ => thresholdSpectrum p.2 p.1) := by
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite (measurableSet_lt measurable_snd ((measurable_eigenvalue S i).comp measurable_fst))
    ((measurable_eigenvalue S i).comp measurable_fst) measurable_const

/-- Thresholds may themselves vary measurably with the data/history. -/
theorem measurable_thresholdOutput (S : CompactFiberSelectionInput.{u, u}) :
    Measurable (thresholdOutput (ι := ι) S) := by
  exact measurable_conjugate_diagonal _ _ ((measurable_basis_matrix S).comp measurable_fst)
    (measurable_thresholdSpectrum S)

theorem rankTruncation_positive (S : CompactFiberSelectionInput.{u, u}) (r : ℕ)
    (A : HermitianMatrix ι) : (rankTruncation S r A).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℂ) ≤ (truncatedSpectrum r A i : ℂ)
  exact_mod_cast truncatedSpectrum_nonneg r A i

theorem rankTruncation_rank (S : CompactFiberSelectionInput.{u, u}) (r : ℕ)
    (A : HermitianMatrix ι) : (rankTruncation S r A).rank ≤ r := by
  let d : ι → ℂ := fun i => (truncatedSpectrum r A i : ℂ)
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
    (rankTruncation S r A).rank ≤ (Matrix.diagonal d).rank :=
      (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    _ = Fintype.card {i // d i ≠ 0} := Matrix.rank_diagonal d
    _ ≤ r := hc

def thresholdMask (t : ℝ) (A : HermitianMatrix ι) (i : ι) : ℝ :=
  if t < A.property.eigenvalues i then 1 else 0

def thresholdProjectorMatrix (S : CompactFiberSelectionInput.{u, u})
    (p : HermitianMatrix ι × ℝ) : Matrix ι ι ℂ :=
  Normalization.conjugate (basis S p.1 : Matrix ι ι ℂ)
    (Normalization.diagonalMatrix (thresholdMask p.2 p.1))

theorem measurable_thresholdMask (S : CompactFiberSelectionInput.{u, u}) :
    Measurable (fun p : HermitianMatrix ι × ℝ => thresholdMask p.2 p.1) := by
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite (measurableSet_lt measurable_snd ((measurable_eigenvalue S i).comp measurable_fst))
    measurable_const measurable_const

theorem measurable_thresholdProjectorMatrix (S : CompactFiberSelectionInput.{u, u}) :
    Measurable (thresholdProjectorMatrix (ι := ι) S) := by
  exact measurable_conjugate_diagonal _ _ ((measurable_basis_matrix S).comp measurable_fst)
    (measurable_thresholdMask S)

/-- The threshold mask is a genuine orthogonal projector, including when
eigenvalues coincide with the threshold or with each other. -/
def thresholdProjector (S : CompactFiberSelectionInput.{u, u})
    (p : HermitianMatrix ι × ℝ) : QuantumModel.OrthogonalProjector ι where
  matrix := thresholdProjectorMatrix S p
  hermitian := Matrix.isHermitian_mul_mul_conjTranspose _
    (Normalization.diagonalMatrix_conjTranspose _)
  idempotent := by
    unfold thresholdProjectorMatrix
    rw [← Normalization.conjugate_mul _ _ _ (basis S p.1).property.1]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Normalization.diagonalMatrix, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_apply_eq]
      unfold thresholdMask
      split_ifs <;> norm_num
    · simp [Normalization.diagonalMatrix, hij]

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_hermitian_mk {α : Type*} [MeasurableSpace α]
    (A : α → Matrix ι ι ℂ) (hA : ∀ x, (A x).IsHermitian) (hm : Measurable A) :
    Measurable (fun x => (⟨A x, hA x⟩ : HermitianMatrix ι)) := hm.subtype_mk

end Paper26.MeasurableSpectralSelection
