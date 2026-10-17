import P31.LowerBound
import P31.Schatten
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Fin.SuccPred

/-!
# Conditional vector-to-Schatten lower transfer (Section 5.3)

Only the two classical spectral facts about a rectangular diagonal and its
extraction map are external inputs.  The literal maps, trace-pairing adjoint,
derivative chain rule, Hölder/radius preservation, and one-for-one adaptive
query simulation are proved here.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
namespace P31.DiagonalLowerBound
open Set QueryProgram LowerBound Schatten

variable {m n : ℕ}

def rowIndex (i : Fin (min m n)) : Fin m := Fin.castLE (Nat.min_le_left m n) i
def colIndex (i : Fin (min m n)) : Fin n := Fin.castLE (Nat.min_le_right m n) i

/-- Extract the actual first `min(m,n)` diagonal coordinates. -/
def extractCoordinates (X : Mat m n) : Fin (min m n) → ℝ :=
  fun i => X (rowIndex i) (colIndex i)

/-- The literal rectangular diagonal embedding, as a continuous linear map
in the ordinary finite-dimensional matrix topology. -/
def diagonalCLM : (Fin (min m n) → ℝ) →L[ℝ] Mat m n :=
  ∑ i : Fin (min m n),
    (ContinuousLinearMap.proj i : (Fin (min m n) → ℝ) →L[ℝ] ℝ).smulRight
      (Matrix.single (rowIndex i) (colIndex i) 1)

def diagonal (v : Fin (min m n) → ℝ) : Mat m n := diagonalCLM v

lemma diagonal_apply (v : Fin (min m n) → ℝ) :
    diagonal v = ∑ i, v i • Matrix.single (rowIndex i) (colIndex i) 1 := by
  simp only [diagonal, diagonalCLM, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]

lemma extract_diagonal (v : Fin (min m n) → ℝ) : extractCoordinates (diagonal v) = v := by
  funext i
  rw [diagonal_apply]
  simp [extractCoordinates, Matrix.sum_apply, Matrix.single, rowIndex, colIndex,
    Fin.castLE_inj]

/-- Coordinate extraction as a continuous linear map to the genuine ℓₚ
space.  No finite-dimensional norm comparison is charged to the oracle. -/
def projection (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] : Mat m n →L[ℝ] Point p (min m n) :=
  (PiLp.continuousLinearEquiv (ENNReal.ofReal p) ℝ
    (fun _ : Fin (min m n) => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin (min m n) =>
      (ContinuousLinearMap.proj (colIndex i) : (Fin n → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj (rowIndex i) : Mat m n →L[ℝ] (Fin n → ℝ))))

@[simp] lemma projection_apply (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (X : Mat m n) :
    projection p X = WithLp.toLp (ENNReal.ofReal p) (extractCoordinates X) := rfl

lemma projection_diagonal (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (v : Point p (min m n)) :
    projection p (diagonal (fun i => v i)) = v := by
  rw [projection_apply, extract_diagonal]
  rfl

/-- The diagonal embedding is the true trace-pairing adjoint of extraction. -/
lemma diagonal_trace (v : Fin (min m n) → ℝ) (X : Mat m n) :
    tracePair (diagonal v) X = ∑ i, v i * extractCoordinates X i := by
  rw [diagonal_apply]
  have hsym (A B : Mat m n) : tracePair A B = tracePair B A := by
    simp only [tracePair, mul_comm]
  rw [hsym, ← traceFunctional_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, traceFunctional_apply]
  simp [tracePair, Matrix.single, ite_and, smul_eq_mul, extractCoordinates]

lemma trace_adjoint (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (v : Fin (min m n) → ℝ) :
    (coordinateFunctionalLp p v).comp (projection p) = traceFunctional (diagonal v) := by
  ext X
  simp only [ContinuousLinearMap.comp_apply, coordinateFunctionalLp_apply,
    projection_apply, PiLp.toLp_apply, traceFunctional_apply, diagonal_trace]

/-- The exact two external spectral norm facts used by the transfer.
They concern literal diagonal matrices and literal extraction, not an oracle
or optimization conclusion. -/
structure DiagonalNormInput (S : SpectralInput m n) where
  diagonal_norm : ∀ r : ℝ, 1 ≤ r → ∀ v : Fin (min m n) → ℝ,
    S.snorm r (diagonal v) = lpNorm r v
  extraction_contract : ∀ r : ℝ, 1 ≤ r → ∀ X : Mat m n,
    lpNorm r (extractCoordinates X) ≤ S.snorm r X

lemma dual_ge_one {p : ℝ} (hp : 1 < p) : 1 ≤ dualExponent p := by
  unfold dualExponent
  apply (le_div_iff₀ (by linarith : 0 < p - 1)).mpr
  linarith

structure MatrixInstance (p κ : ℝ) (m n : ℕ) where
  value : Mat m n → ℝ
  gradient : Mat m n → Mat m n
  derivative : ∀ X, HasFDerivAt value (traceFunctional (gradient X)) X
  convex : ConvexOn ℝ univ value

namespace MatrixInstance
variable {p κ : ℝ}

def oracle (I : MatrixInstance p κ m n) (X : Mat m n) : ℝ × Mat m n :=
  (I.value X, I.gradient X)

def InClass (I : MatrixInstance p κ m n) (S : SpectralInput m n) (L R : ℝ) : Prop :=
  (∀ X Y, S.snorm (dualExponent p) (I.gradient X - I.gradient Y) ≤
    L * S.snorm p (X - Y) ^ (κ - 1)) ∧
  ∃ Y, (∀ X, I.value Y ≤ I.value X) ∧ S.snorm p Y ≤ R

end MatrixInstance

/-- Lift a genuine vector objective by diagonal extraction.  Its matrix
gradient is a literal rectangular diagonal matrix, as the chain rule proves. -/
def lift {p κ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (I : VectorInstance p κ (min m n)) : MatrixInstance p κ m n where
  value := fun X => I.value (projection p X)
  gradient := fun X => diagonal (I.gradient (projection p X))
  derivative := by
    intro X
    have hd := (I.derivative (projection p X)).comp X (projection p).hasFDerivAt
    rw [trace_adjoint] at hd
    exact hd
  convex := by
    simpa only [preimage_univ, Function.comp_def] using
      I.convex.comp_linearMap (projection p).toLinearMap

/-- The lift preserves the source Hölder constant and initial radius,
without a dimensional factor. -/
theorem lift_inClass {p κ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 < p) (hκ : 1 ≤ κ) (S : SpectralInput m n) (D : DiagonalNormInput S)
    (I : VectorInstance p κ (min m n)) (L R : ℝ) (hL : 0 ≤ L) (hI : I.InClass L R) :
    (lift I).InClass S L R := by
  constructor
  · intro X Y
    change S.snorm (dualExponent p)
      (diagonal (I.gradient (projection p X)) - diagonal (I.gradient (projection p Y))) ≤ _
    have hdiag : diagonal (I.gradient (projection p X)) - diagonal (I.gradient (projection p Y)) =
        diagonal (I.gradient (projection p X) - I.gradient (projection p Y)) :=
      (map_sub diagonalCLM _ _).symm
    rw [hdiag, D.diagonal_norm _ (dual_ge_one hp)]
    have hnorm : ‖projection p X - projection p Y‖ ≤ S.snorm p (X - Y) := by
      rw [← map_sub, projection_apply,
        ← lpNorm_eq_piLp_norm p (by linarith) (extractCoordinates (X - Y))]
      exact D.extraction_contract p hp.le _
    exact (hI.1 _ _).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hnorm (by linarith)) hL)
  · obtain ⟨y, hy, hyr⟩ := hI.2
    refine ⟨diagonal (fun i => y i), ?_, ?_⟩
    · intro X
      change I.value (projection p (diagonal (fun i => y i))) ≤ I.value (projection p X)
      rw [projection_diagonal]
      exact hy _
    · rw [D.diagonal_norm p hp.le, lpNorm_eq_piLp_norm p (by linarith)]
      exact hyr

abbrev MatrixMethod (m n : ℕ) := Program (Mat m n) (ℝ × Mat m n) (Mat m n)

/-- Every matrix query is answered from one query to its extracted diagonal;
the final output is extracted by uncharged exact computation. -/
def vectorSimulation {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (P : MatrixMethod m n) : Method p (min m n) :=
  (Program.simulate (projection p) (fun (_ : Mat m n) (reply : Reply (min m n)) =>
    (reply.1, diagonal reply.2)) P).map (projection p)

/-- Full execution identity: adaptive queries and returned gradients are
preserved, and the number of local oracle calls is unchanged. -/
theorem vectorSimulation_run {p κ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (P : MatrixMethod m n) (I : VectorInstance p κ (min m n)) :
    (vectorSimulation (p := p) P).run I.oracle =
      let r := P.run (lift I).oracle
      ⟨projection p r.value, r.queries.map (projection p), r.calls⟩ := by
  unfold vectorSimulation
  rw [LowerBound.run_map, Program.run_simulate]
  rfl

/-- Uniform matrix correctness for the Schatten source class. -/
def MatrixCorrect {p κ : ℝ} (P : MatrixMethod m n) (S : SpectralInput m n) (L R ε : ℝ) : Prop :=
  ∀ I : MatrixInstance p κ m n, I.InClass S L R →
    S.snorm (dualExponent p) (I.gradient (P.run I.oracle).value) ≤ ε

/-- A correct matrix method would provide a correct vector method at exactly
the same number of calls.  This closes the diagonal oracle reduction. -/
theorem vectorSimulation_correct {p κ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 < p) (hκ : 1 ≤ κ) (S : SpectralInput m n) (D : DiagonalNormInput S)
    (L R ε : ℝ) (hL : 0 ≤ L) (P : MatrixMethod m n)
    (hP : MatrixCorrect (p := p) (κ := κ) P S L R ε) :
    Correct (κ := κ) (vectorSimulation (p := p) P) L R ε := by
  intro I hI
  have hh := hP (lift I) (lift_inClass hp hκ S D I L R hL hI)
  rw [vectorSimulation_run]
  change lpNorm (dualExponent p) (I.gradient (projection p (P.run (lift I).oracle).value)) ≤ ε
  change S.snorm (dualExponent p)
    (diagonal (I.gradient (projection p (P.run (lift I).oracle).value))) ≤ ε at hh
  rw [D.diagonal_norm _ (dual_ge_one hp)] at hh
  exact hh

/-- Section 5.3: diagonal instances transfer the conditional matching
lower exponent to rectangular Schatten geometry, with dimension `min(m,n)`.
The only spectral inputs are the two norm facts above. -/
theorem diagonal_conditional_gradient_lower_bound {p κ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (H : SimultaneousHardFamily p κ) (hp : 2 ≤ p) (hκ : 1 < κ)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (S : SpectralInput m n) (D : DiagonalNormInput S)
    (L R ε : ℝ) (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε)
    (hsmall : ε ≤ accuracyConstant H * (L * R ^ (κ - 1)))
    (hlog : p ≤ Real.log (min m n : ℕ))
    (hdim : dimensionConstant H * (L * R ^ (κ - 1) / ε) ^ exponent p κ ≤ min m n)
    (P : MatrixMethod m n) (hP : MatrixCorrect (p := p) (κ := κ) P S L R ε) :
    ∃ I : MatrixInstance p κ m n, I.InClass S L R ∧
      queryConstant H * (L * R ^ (κ - 1) / ε) ^ exponent p κ ≤ (P.run I.oracle).calls := by
  have hp1 : 1 < p := by linarith
  have hcorrect := vectorSimulation_correct hp1 hκ.le S D L R ε hL.le P hP
  obtain ⟨I, hI, hcost⟩ := conditional_gradient_lower_bound H hp hκ (min m n)
    (le_min hm hn) L R ε hL hR hε hsmall hlog hdim (vectorSimulation (p := p) P) hcorrect
  refine ⟨lift I, lift_inClass hp1 hκ.le S D I L R hL.le hI, ?_⟩
  rw [vectorSimulation_run] at hcost
  exact hcost

/-- The literal sharpness matrix in Remark 5.3 is the scalar multiple of
the rectangular diagonal of ones displayed in the paper. -/
theorem normalized_diagonal_formula (q : ℝ) :
    diagonal (normalizedFlatVector (min m n) q) =
      ((min m n : ℕ) : ℝ) ^ (-(1 / q)) • diagonal (fun _ => 1) := by
  unfold diagonal
  rw [← map_smul]
  congr 1
  funext i
  simp only [normalizedFlatVector, Pi.smul_apply, smul_eq_mul, mul_one]

/-- Remark 5.3: the source matrix has unit Schatten-q norm and attains
exactly the dimension factor in the stronger Schatten-s norm. -/
theorem rectangular_diagonal_flat_norms (S : SpectralInput m n) (D : DiagonalNormInput S)
    (hm : 1 ≤ m) (hn : 1 ≤ n) {s q : ℝ} (hs : 1 ≤ s) (hq : 1 ≤ q) :
    S.snorm q (diagonal (normalizedFlatVector (min m n) q)) = 1 ∧
    S.snorm s (diagonal (normalizedFlatVector (min m n) q)) =
      ((min m n : ℕ) : ℝ) ^ (1 / s - 1 / q) := by
  have hd : 0 < min m n := lt_of_lt_of_le Nat.zero_lt_one (le_min hm hn)
  rw [D.diagonal_norm q hq, D.diagonal_norm s hs]
  exact ⟨normalizedFlatVector_unit_norm (min m n) hd (by linarith),
    normalizedFlatVector_norm (min m n) hd (by linarith)⟩

/-- Any claimed uniform norm-conversion constant for this matrix shape is
at least the source dimension factor. -/
theorem rectangular_diagonal_sharp_factor (S : SpectralInput m n) (D : DiagonalNormInput S)
    (hm : 1 ≤ m) (hn : 1 ≤ n) {s q C : ℝ} (hs : 1 ≤ s) (hq : 1 ≤ q)
    (hbound : ∀ G : Mat m n, S.snorm s G ≤ C * S.snorm q G) :
    ((min m n : ℕ) : ℝ) ^ (1 / s - 1 / q) ≤ C := by
  obtain ⟨hqn, hsn⟩ := rectangular_diagonal_flat_norms S D hm hn hs hq
  have hh := hbound (diagonal (normalizedFlatVector (min m n) q))
  simpa only [hqn, hsn, mul_one] using hh

end P31.DiagonalLowerBound
