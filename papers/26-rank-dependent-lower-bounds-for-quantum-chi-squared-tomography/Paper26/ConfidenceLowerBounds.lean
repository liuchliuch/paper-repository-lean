import Paper26.MainLowerBounds
import Paper26.ComparisonInequalities
import Paper26.OperatorMeasureConstruction
import Paper26.SourceCopyComplexity

/-!
# Native two-point confidence lower bounds (Appendix B)

The only additional known theorem is generic pure-state binary discrimination.
Its field quantifies over arbitrary actual finite complex density matrices
that are projections, and arbitrary two PSD effects summing to the identity.
It contains no learner, loss, confidence, copy number, or P26 conclusion.
It is the equal-prior pure-state corollary of Watrous, *The Theory of Quantum
Information* (2018), Theorem 3.4 and Equations (1.184)--(1.186), together with
the standard pure-state characterization (Equation (2.12)).
https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf

All learning-to-testing, tensor-power, ball-separation and logarithmic
sample-count steps below are native deductions.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory
namespace Paper26.ConfidenceLowerBounds
open QuantumModel CollectiveModel OperatorPOVMTransport CommonCenter SupportCompression
open TailConvexity WeightedTraceCS ComparisonInequalities JordanLossMeasurability

/-- Exact generic known pure binary discrimination theorem. The idempotence
hypotheses on positive trace-one matrices mean that the states are pure. -/
structure PureBinaryTestingInput : Prop where
  error_lower : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (ρ σ : Density κ),
    ρ.matrix * ρ.matrix = ρ.matrix → σ.matrix * σ.matrix = σ.matrix →
    ∀ E F : Matrix κ κ ℂ, E.PosSemidef → F.PosSemidef → E + F = 1 →
      (1 - Real.sqrt (1 - (Matrix.trace (ρ.matrix * σ.matrix)).re)) / 2 ≤
        ((Matrix.trace (ρ.matrix * F)).re + (Matrix.trace (σ.matrix * E)).re) / 2
  attains : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (ρ σ : Density κ),
    ρ.matrix * ρ.matrix = ρ.matrix → σ.matrix * σ.matrix = σ.matrix →
    ∃ E F : Matrix κ κ ℂ, E.PosSemidef ∧ F.PosSemidef ∧ E + F = 1 ∧
      ((Matrix.trace (ρ.matrix * F)).re + (Matrix.trace (σ.matrix * E)).re) / 2 =
        (1 - Real.sqrt (1 - (Matrix.trace (ρ.matrix * σ.matrix)).re)) / 2

variable {ι Ω : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

/-- Finite additivity is derived from the actual POVM's countable additivity. -/
theorem operator_union (M : OperatorPOVM ι Ω) {S T : Set Ω}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hd : Disjoint S T) :
    M.operator (S ∪ T) = M.operator S + M.operator T := by
  let V : ℕ → Set Ω := fun k => if k = 0 then S else if k = 1 then T else ∅
  have hm : ∀ k, MeasurableSet (V k) := by intro k; dsimp [V]; split_ifs <;> first | assumption | exact MeasurableSet.empty
  have hv : Pairwise (fun k l => Disjoint (V k) (V l)) := by
    intro k l hkl
    dsimp [V]
    split_ifs with hk0 hk1 hl0 hl1 <;> simp_all
    exact hd.symm
  have hu : (⋃ k, V k) = S ∪ T := by
    ext x
    simp only [Set.mem_iUnion,Set.mem_union]
    constructor
    · rintro ⟨k,hk⟩
      dsimp [V] at hk
      split_ifs at hk <;> simp_all
    · rintro (hx | hx)
      · exact ⟨0,by simpa [V] using hx⟩
      · exact ⟨1,by simpa [V] using hx⟩
  ext i j
  have hs := M.countable_additivity V hm hv i j
  rw [hu] at hs
  have ht : HasSum (fun k : ℕ => M.operator (V k) i j)
      (M.operator S i j + M.operator T i j) := by
    convert (hasSum_ite_eq (0 : ℕ) (M.operator S i j)).add
      (hasSum_ite_eq (1 : ℕ) (M.operator T i j)) using 1
    funext k
    dsimp [V]
    split_ifs <;> simp_all [M.empty]
  exact hs.unique ht

theorem operator_compl (M : OperatorPOVM ι Ω) {S : Set Ω} (hS : MeasurableSet S) :
    M.operator S + M.operator Sᶜ = 1 := by
  rw [← operator_union M hS hS.compl disjoint_compl_right,Set.union_compl_self,M.total]

theorem operator_mono_trace (M : OperatorPOVM ι Ω) (ρ : Density ι)
    {S T : Set Ω} (hS : MeasurableSet S) (hT : MeasurableSet T) (hST : S ⊆ T) :
    (Matrix.trace (ρ.matrix * M.operator S)).re ≤
      (Matrix.trace (ρ.matrix * M.operator T)).re := by
  have hu : S ∪ (T \ S) = T := Set.union_diff_cancel hST
  have ha := operator_union M hS (hT.diff hS) Set.disjoint_sdiff_right
  rw [hu] at ha
  have hn := QuantumModel.trace_mul_effect_nonneg ρ (M.positive (T \ S) (hT.diff hS))
  rw [ha,Matrix.mul_add,Matrix.trace_add,Complex.add_re]
  linarith

/-- Any two disjoint actual success events give a genuine binary test with
average error at most δ; no representation/RN theorem is needed. -/
theorem learner_testing_error {n : ℕ} (A : OperatorLearner ι Ω n)
    (loss : Density ι → Density ι → ℝ≥0∞) (ρ σ : Density ι) (ε : ℝ≥0∞)
    {δ : ℝ}
    (hρ : MeasurableSet (A.successSet loss ρ ε))
    (hσ : MeasurableSet (A.successSet loss σ ε))
    (hp : ENNReal.ofReal (1-δ) ≤ A.successProbability loss ρ ε)
    (hq : ENNReal.ofReal (1-δ) ≤ A.successProbability loss σ ε)
    (hd : Disjoint (A.successSet loss ρ ε) (A.successSet loss σ ε)) :
    (A.eventBorn ρ (A.successSet loss ρ ε)ᶜ +
      A.eventBorn σ (A.successSet loss ρ ε)) / 2 ≤ δ := by
  let S := A.successSet loss ρ ε
  let T := A.successSet loss σ ε
  have hpR : 1-δ ≤ A.eventBorn ρ S := by
    change ENNReal.ofReal (1-δ) ≤ ENNReal.ofReal (A.eventBorn ρ S) at hp
    exact (ENNReal.ofReal_le_ofReal_iff (A.eventBorn_nonneg ρ S hρ)).mp hp
  have hqR : 1-δ ≤ A.eventBorn σ T := by
    change ENNReal.ofReal (1-δ) ≤ ENNReal.ofReal (A.eventBorn σ T) at hq
    exact (ENNReal.ofReal_le_ofReal_iff (A.eventBorn_nonneg σ T hσ)).mp hq
  have hcomp (τ : Density ι) : A.eventBorn τ S + A.eventBorn τ Sᶜ = 1 := by
    unfold OperatorLearner.eventBorn
    rw [← Complex.add_re,← Matrix.trace_add,← Matrix.mul_add,operator_compl A.measurement hρ,
      Matrix.mul_one,(TensorCopies.density τ n).trace_one,Complex.one_re]
  have hTS : T ⊆ Sᶜ := Set.disjoint_left.mp hd.symm
  have hm := operator_mono_trace A.measurement (TensorCopies.density σ n) hσ hρ.compl hTS
  change A.eventBorn σ T ≤ A.eventBorn σ Sᶜ at hm
  linarith [hcomp ρ,hcomp σ]

/-- The actual tensor overlap is the nth power; the complex equality keeps
all reality obligations explicit. -/
theorem tensor_overlap (ρ σ : Density ι) (v : ℝ)
    (hv : Matrix.trace (ρ.matrix * σ.matrix) = (v : ℂ)) (n : ℕ) :
    (Matrix.trace ((TensorCopies.density ρ n).matrix *
      (TensorCopies.density σ n).matrix)).re = v ^ n := by
  change (Matrix.trace (TensorCopies.matrix ρ.matrix n * TensorCopies.matrix σ.matrix n)).re = _
  rw [← TensorCopies.matrix_mul,TensorCopies.matrix_trace,hv]
  simp [← Complex.ofReal_pow]

/-- Exact Eq. (53) arithmetic, derived from the pure testing error. -/
theorem equation_53_arithmetic {u δ : ℝ} {n : ℕ}
    (hu : 0 < u) (hu1 : u < 1) (hδ : 0 < δ) (hδhalf : δ < 1/2)
    (he : (1 - Real.sqrt (1-(1-u^2)^n))/2 ≤ δ) :
    Real.log (1/(4*δ*(1-δ))) / (-Real.log (1-u^2)) ≤ (n : ℝ) := by
  have hb : 0 < 1-u^2 := by nlinarith
  have hb1 : 1-u^2 < 1 := by nlinarith
  have hp : (1-u^2)^n ≤ 1 := pow_le_one₀ hb.le hb1.le
  have hs := Real.sq_sqrt (sub_nonneg.mpr hp)
  have hr := Real.sqrt_nonneg (1-(1-u^2)^n)
  have hpow : (1-u^2)^n ≤ 4*δ*(1-δ) := by nlinarith
  have hd1 : 0 < 1-δ := by linarith
  have ha : 0 < 4*δ*(1-δ) := by positivity
  have hl := Real.log_le_log (pow_pos hb n) hpow
  rw [Real.log_pow] at hl
  have hden : 0 < -Real.log (1-u^2) := neg_pos.mpr (Real.log_neg hb hb1)
  rw [Real.log_div one_ne_zero ha.ne',Real.log_one,zero_sub]
  apply (div_le_iff₀ hden).mpr
  nlinarith

/-- Native learner-to-testing and tensor algebra specialize the generic
pure binary theorem to the actual two input states. -/
theorem equation_53 {n : ℕ} (H : PureBinaryTestingInput) (A : OperatorLearner ι Ω n)
    (loss : Density ι → Density ι → ℝ≥0∞) (ρ σ : Density ι) (ε : ℝ≥0∞)
    {u δ : ℝ} (hu : 0 < u) (hu1 : u < 1) (hδ : 0 < δ) (hδhalf : δ < 1/2)
    (hρpure : ρ.matrix * ρ.matrix = ρ.matrix) (hσpure : σ.matrix * σ.matrix = σ.matrix)
    (hov : Matrix.trace (ρ.matrix * σ.matrix) = ((1-u^2 : ℝ) : ℂ))
    (hρ : MeasurableSet (A.successSet loss ρ ε))
    (hσ : MeasurableSet (A.successSet loss σ ε))
    (hp : ENNReal.ofReal (1-δ) ≤ A.successProbability loss ρ ε)
    (hq : ENNReal.ofReal (1-δ) ≤ A.successProbability loss σ ε)
    (hd : Disjoint (A.successSet loss ρ ε) (A.successSet loss σ ε)) :
    Real.log (1/(4*δ*(1-δ))) / (-Real.log (1-u^2)) ≤ (n : ℝ) := by
  have htρ : (TensorCopies.density ρ n).matrix * (TensorCopies.density ρ n).matrix =
      (TensorCopies.density ρ n).matrix := by
    change TensorCopies.matrix ρ.matrix n * TensorCopies.matrix ρ.matrix n = _
    rw [← TensorCopies.matrix_mul,hρpure]
    rfl
  have htσ : (TensorCopies.density σ n).matrix * (TensorCopies.density σ n).matrix =
      (TensorCopies.density σ n).matrix := by
    change TensorCopies.matrix σ.matrix n * TensorCopies.matrix σ.matrix n = _
    rw [← TensorCopies.matrix_mul,hσpure]
    rfl
  have he := H.error_lower (Fin n → ι) (TensorCopies.density ρ n) (TensorCopies.density σ n)
    htρ htσ (A.measurement.operator (A.successSet loss ρ ε))
    (A.measurement.operator (A.successSet loss ρ ε)ᶜ)
    (A.measurement.positive _ hρ) (A.measurement.positive _ hρ.compl)
    (operator_compl A.measurement hρ)
  rw [tensor_overlap ρ σ _ hov n] at he
  exact equation_53_arithmetic hu hu1 hδ hδhalf
    (he.trans (learner_testing_error A loss ρ σ ε hρ hσ hp hq hd))

/-- A fixed positive log coefficient valid all the way to δ=1/3. -/
def logCoefficient : ℝ := min (1/2) (Real.log (9/8) / Real.log 16)

theorem logCoefficient_pos : 0 < logCoefficient := by
  apply lt_min (by norm_num)
  exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))

theorem confidence_log_lower {δ : ℝ} (hδ : 0 < δ) (hδ3 : δ ≤ 1/3) :
    logCoefficient * Real.log (1/δ) ≤ Real.log (1/(4*δ*(1-δ))) := by
  have hd1 : 0 < 1-δ := by linarith
  have ha : 0 < 4*δ*(1-δ) := by positivity
  have hlogδ : 0 ≤ -Real.log δ := by
    exact neg_nonneg.mpr (Real.log_nonpos hδ.le (by linarith))
  rw [Real.log_div one_ne_zero hδ.ne',Real.log_div one_ne_zero ha.ne',Real.log_one,
    zero_sub,zero_sub]
  by_cases hsmall : δ ≤ 1/16
  · have hsq : (4*δ*(1-δ))^2 ≤ δ := by
      have h1 : 4*δ*(1-δ) ≤ 4*δ := by nlinarith
      have h2 : 16*δ^2 ≤ δ := by nlinarith
      nlinarith [sq_nonneg (4*δ-4*δ*(1-δ))]
    have hl := Real.log_le_log (sq_pos_of_pos ha) hsq
    rw [Real.log_pow] at hl
    have hc : logCoefficient ≤ 1/2 := min_le_left _ _
    have hm := mul_le_mul_of_nonneg_right hc hlogδ
    norm_num at hl
    nlinarith
  · have hd16 : 1/16 ≤ δ := (lt_of_not_ge hsmall).le
    have ha8 : 4*δ*(1-δ) ≤ 8/9 := by nlinarith
    have hl := Real.log_le_log ha ha8
    have hdlog := Real.log_le_log (by norm_num : (0:ℝ)<1/16) hd16
    have hl16 : -Real.log δ ≤ Real.log 16 := by
      rw [Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub] at hdlog
      linarith
    have hc : logCoefficient ≤ Real.log (9/8)/Real.log 16 := min_le_right _ _
    have hcl : logCoefficient * Real.log 16 ≤ Real.log (9/8) :=
      (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<16))).mp hc
    have hm := mul_le_mul_of_nonneg_left hl16 logCoefficient_pos.le
    have he : Real.log (9/8) = -Real.log (8/9) := by
      rw [← Real.log_inv]
      norm_num
    rw [he] at hcl
    linarith

theorem neg_log_one_sub_sq_le {u : ℝ} (hu2 : u^2 ≤ 1/2) :
    -Real.log (1-u^2) ≤ 2*u^2 := by
  have hb : 0 < 1-u^2 := by nlinarith
  have hi : (1-u^2)⁻¹ ≤ 1+2*u^2 := by
    apply (inv_le_iff_one_le_mul₀ hb).mpr
    nlinarith [sq_nonneg u]
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hb)
  rw [Real.log_inv] at hl
  linarith

/-- A fixed confidence constant, independent of dimension and rank. -/
def confidenceConstant : ℝ := logCoefficient / 8

theorem confidenceConstant_pos : 0 < confidenceConstant := div_pos logCoefficient_pos (by norm_num)

/-- Native small-angle consequence of Eq. (53). -/
theorem confidence_rate_arithmetic {u δ : ℝ} {n : ℕ}
    (hu : 0 < u) (hu2 : u^2 ≤ 1/2) (hδ : 0 < δ) (hδ3 : δ ≤ 1/3)
    (h53 : Real.log (1/(4*δ*(1-δ))) / (-Real.log (1-u^2)) ≤ (n : ℝ)) :
    logCoefficient * Real.log (1/δ) ≤ (n : ℝ) * (2*u^2) := by
  have hb : 0 < 1-u^2 := by nlinarith
  have hb1 : 1-u^2 < 1 := by nlinarith
  have hden : 0 < -Real.log (1-u^2) := neg_pos.mpr (Real.log_neg hb hb1)
  have hl := (div_le_iff₀ hden).mp h53
  exact (confidence_log_lower hδ hδ3).trans
    (hl.trans (mul_le_mul_of_nonneg_left (neg_log_one_sub_sq_le hu2) (Nat.cast_nonneg n)))

/-- The same native weighted-CS argument as Lemma 1.4 applies to any actual
Hermitian contraction witness, including singular output densities. -/
theorem witness_sq_le_chiB (ρ σ : Density ι) (K : Matrix ι ι ℂ)
    (hK : K.IsHermitian) (hKK : (1-K*K).PosSemidef) :
    ENNReal.ofReal (pairing (ρ.matrix-σ.matrix) K ^ 2) ≤ chiB ρ σ := by
  by_cases h : SupportContained ρ σ
  · letI : Nonempty ι := by
      by_contra hn
      haveI : IsEmpty ι := not_nonempty_iff.mp hn
      simpa [Matrix.trace] using ρ.trace_one
    have hcs := weighted_bilinear_cs σ.matrix (supportedSLD ρ σ) K σ.positive
      (supportedSLD_hermitian ρ σ) hK
    have hx : pairing (ρ.matrix-σ.matrix) K = pairing σ.matrix (K*supportedSLD ρ σ) := by
      rw [← supportedSLD_tangent ρ σ h]
      exact sldTangent_pairing _ _ _ σ.hermitian hK (supportedSLD_hermitian ρ σ)
    rw [← hx,supportedSLD_energy ρ σ h] at hcs
    have ht : pairing σ.matrix (1 : Matrix ι ι ℂ) = 1 := by
      simp [pairing,σ.trace_one]
    have hk := pairing_nonneg_psd _ _ σ.positive hKK
    rw [pairing_sub_right,ht] at hk
    have hH : (supportedSLD ρ σ * supportedSLD ρ σ).PosSemidef := by
      simpa only [(supportedSLD_hermitian ρ σ).eq] using
        Matrix.posSemidef_conjTranspose_mul_self (supportedSLD ρ σ)
    have he := pairing_nonneg_psd _ _ σ.positive hH
    rw [supportedSLD_energy ρ σ h] at he
    rw [chiB_eq_jordan_energy ρ σ h]
    exact ENNReal.ofReal_le_ofReal (hcs.trans (by nlinarith))
  · rw [chiB_eq_top_of_not_supportContained ρ σ h]
    exact le_top

/-- The actual two-dimensional principal-angle index. -/
abbrev PairIndex := Fin 2 × Fin 1

/-- Native isometric embedding from any two-coordinate injection. -/
def inclusionMatrix (e : PairIndex ↪ ι) : Matrix ι PairIndex ℂ :=
  fun i j => if i = e j then 1 else 0

theorem inclusionMatrix_isometry (e : PairIndex ↪ ι) :
    (inclusionMatrix e)ᴴ * inclusionMatrix e = 1 := by
  ext a b
  classical
  rw [Matrix.mul_apply,Finset.sum_eq_single (e a)]
  · by_cases hab : a=b
    · subst b; simp [inclusionMatrix]
    · simp [inclusionMatrix,Matrix.conjTranspose_apply,hab,e.injective.ne hab]
  · intro i _ hi
    simp [inclusionMatrix,Matrix.conjTranspose_apply,hi]
  · simp

/-- Conjugation by a rectangular isometry preserves actual projectors. -/
def embedProjector (V : Matrix ι PairIndex ℂ) (hV : Vᴴ*V=1)
    (P : OrthogonalProjector PairIndex) : OrthogonalProjector ι where
  matrix := embedMatrix V P.matrix
  hermitian := Matrix.isHermitian_mul_mul_conjTranspose _ P.hermitian
  idempotent := by rw [← embedMatrix_mul V hV,P.idempotent]

def pairCosine (u : ℝ) : ℝ := Real.sqrt (1-u^2)

lemma pair_circle {u : ℝ} (hu : 0 < u) (hu1 : u < 1) : pairCosine u ^2 + u^2=1 := by
  rw [pairCosine,Real.sq_sqrt (by nlinarith)]
  ring

def firstProjector (V : Matrix ι PairIndex ℂ) (hV : Vᴴ*V=1)
    (u : ℝ) (hu : 0<u) (hu1 : u<1) : OrthogonalProjector ι :=
  embedProjector V hV (canonicalP (fun _ => pairCosine u) (fun _ : Fin 1 => u)
    (fun _ => pair_circle hu hu1))

def secondProjector (V : Matrix ι PairIndex ℂ) (hV : Vᴴ*V=1)
    (u : ℝ) (hu : 0<u) (hu1 : u<1) : OrthogonalProjector ι :=
  embedProjector V hV (canonicalQ (fun _ => pairCosine u) (fun _ : Fin 1 => u)
    (fun _ => pair_circle hu hu1))

/-- All principal-angle data for the pair are constructed, not assumed. -/
def pairForm (V : Matrix ι PairIndex ℂ) (hV : Vᴴ*V=1)
    (u : ℝ) (hu : 0<u) (hu1 : u<1) :
    PrincipalAngleForm (κ := Fin 1) (firstProjector V hV u hu hu1)
      (secondProjector V hV u hu hu1) where
  c := fun _ => pairCosine u
  s := fun _ => u
  circle := fun _ => pair_circle hu hu1
  cosine_nonneg := fun _ => Real.sqrt_nonneg _
  cosine_le_one := fun _ => by
    have h := pair_circle hu hu1
    have hn := Real.sqrt_nonneg (1-u^2)
    change pairCosine u ≤ 1
    nlinarith [sq_nonneg u]
  sine_nonneg := fun _ => hu.le
  isometry := V
  orthonormal := hV
  first := rfl
  second := rfl

def firstState (V : Matrix ι PairIndex ℂ) (hV : Vᴴ*V=1)
    (u : ℝ) (hu : 0<u) (hu1 : u<1) : Density ι :=
  (firstProjector V hV u hu hu1).flat (pairForm V hV u hu hu1).rankP_pos

def secondState (V : Matrix ι PairIndex ℂ) (hV : Vᴴ*V=1)
    (u : ℝ) (hu : 0<u) (hu1 : u<1) : Density ι :=
  (secondProjector V hV u hu hu1).flat (pairForm V hV u hu hu1).rankQ_pos

@[simp] theorem firstState_matrix (V : Matrix ι PairIndex ℂ) (hV : Vᴴ*V=1)
    (u : ℝ) (hu : 0<u) (hu1 : u<1) :
    (firstState V hV u hu hu1).matrix = (firstProjector V hV u hu hu1).matrix := by
  simp [firstState,OrthogonalProjector.flat,(pairForm V hV u hu hu1).rankP]

@[simp] theorem secondState_matrix (V : Matrix ι PairIndex ℂ) (hV : Vᴴ*V=1)
    (u : ℝ) (hu : 0<u) (hu1 : u<1) :
    (secondState V hV u hu hu1).matrix = (secondProjector V hV u hu hu1).matrix := by
  simp [secondState,OrthogonalProjector.flat,(pairForm V hV u hu hu1).rankQ]

theorem pair_ranks (V : Matrix ι PairIndex ℂ) (hV : Vᴴ*V=1)
    (u : ℝ) (hu : 0<u) (hu1 : u<1) :
    (firstState V hV u hu hu1).matrix.rank = 1 ∧
      (secondState V hV u hu hu1).matrix.rank = 1 := by
  simp only [firstState_matrix,secondState_matrix]
  exact ⟨by simpa using (pairForm V hV u hu hu1).rankP,
    by simpa using (pairForm V hV u hu hu1).rankQ⟩

lemma canonical_overlap {u : ℝ} (hu : 0<u) (hu1 : u<1) :
    Matrix.trace ((canonicalP (fun _ => pairCosine u) (fun _ : Fin 1 => u)
        (fun _ => pair_circle hu hu1)).matrix *
      (canonicalQ (fun _ => pairCosine u) (fun _ : Fin 1 => u)
        (fun _ => pair_circle hu hu1)).matrix) = ((1-u^2 : ℝ) : ℂ) := by
  have hc : ((1-u^2 : ℝ) : ℂ) = 1-(u : ℂ)*(u : ℂ) := by push_cast; ring
  rw [hc]
  apply Complex.ext
  · simp [canonicalP,canonicalQ,Matrix.trace,Matrix.mul_apply,Matrix.blockDiagonal_apply,
      Fintype.sum_prod_type,Fin.sum_univ_two,angleBlock,Complex.mul_re]
    nlinarith [pair_circle hu hu1]
  · simp [canonicalP,canonicalQ,Matrix.trace,Matrix.mul_apply,Matrix.blockDiagonal_apply,
      Fintype.sum_prod_type,Fin.sum_univ_two,angleBlock,Complex.mul_im]

theorem pair_overlap (V : Matrix ι PairIndex ℂ) (hV : Vᴴ*V=1)
    (u : ℝ) (hu : 0<u) (hu1 : u<1) :
    Matrix.trace ((firstState V hV u hu hu1).matrix *
      (secondState V hV u hu hu1).matrix) = ((1-u^2 : ℝ) : ℂ) := by
  rw [firstState_matrix,secondState_matrix]
  change Matrix.trace (embedMatrix V _ * embedMatrix V _) = _
  rw [← embedMatrix_mul V hV,embedMatrix_trace V hV]
  exact canonical_overlap hu hu1

/-- The exact rank-one common-center radius is u for every ambient output,
including singular outputs and unused ambient coordinates. -/
theorem right_pair_radius (V : Matrix ι PairIndex ℂ) (hV : Vᴴ*V=1)
    (u : ℝ) (hu : 0<u) (hu1 : u<1) (τ : Density ι) :
    ENNReal.ofReal u ≤ max (chiR (firstState V hV u hu hu1) τ)
      (chiR (secondState V hV u hu hu1) τ) := by
  have h := (pairForm V hV u hu hu1).max_lower τ
  have he : principalRadius (fun _ : Fin 1 => u) = u := by
    simp [principalRadius,Real.sq_sqrt (by linarith : 0 ≤ 1+u)]
  simpa only [pairForm,firstState,secondState,he] using h

/-- Consequently the actual right-inverse loss balls are disjoint. -/
theorem right_balls_disjoint (V : Matrix ι PairIndex ℂ) (hV : Vᴴ*V=1)
    (u : ℝ) (hu : 0<u) (hu1 : u<1) {ε : ℝ} (hε : 0 ≤ ε) (hεu : ε<u) :
    Disjoint {τ | chiR (firstState V hV u hu hu1) τ ≤ ENNReal.ofReal ε}
      {τ | chiR (secondState V hV u hu hu1) τ ≤ ENNReal.ofReal ε} := by
  apply Set.disjoint_left.mpr
  intro τ hp hq
  have h := (right_pair_radius V hV u hu hu1 τ).trans (max_le hp hq)
  exact (not_le_of_gt hεu) ((ENNReal.ofReal_le_ofReal_iff hε).mp h)

def swapWitness : Matrix PairIndex PairIndex ℂ :=
  Matrix.blockDiagonal (fun _ : Fin 1 => differenceBlock 1)

lemma swapWitness_hermitian : swapWitness.IsHermitian := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [swapWitness,Matrix.blockDiagonal_apply,differenceBlock,Matrix.conjTranspose_apply]

lemma swapWitness_square : swapWitness * swapWitness = 1 := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [swapWitness,Matrix.blockDiagonal_apply,differenceBlock,Matrix.mul_apply,
      Fintype.sum_prod_type,Fin.sum_univ_two]

/-- The embedded fixed sign witness is a genuine Hermitian contraction. -/
theorem pair_witness_contraction (V : Matrix ι PairIndex ℂ) (hV : Vᴴ*V=1) :
    (embedMatrix V swapWitness).IsHermitian ∧
      (1-embedMatrix V swapWitness * embedMatrix V swapWitness).PosSemidef := by
  have hK : (embedMatrix V swapWitness).IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose _ swapWitness_hermitian
  have hs : embedMatrix V swapWitness * embedMatrix V swapWitness =
      embedMatrix V (1 : Matrix PairIndex PairIndex ℂ) := by
    rw [← embedMatrix_mul V hV,swapWitness_square]
  let R := embedMatrix V (1 : Matrix PairIndex PairIndex ℂ)
  have hR : R.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose _ Matrix.isHermitian_one
  have hRR : R*R=R := by dsimp [R]; rw [← embedMatrix_mul V hV,Matrix.one_mul]
  have he : (1-R)ᴴ*(1-R)=1-R := by
    rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hR.eq]
    simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,hRR]
    abel
  refine ⟨hK,?_⟩
  rw [hs,← he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem pair_witness_separation (V : Matrix ι PairIndex ℂ) (hV : Vᴴ*V=1)
    (u : ℝ) (hu : 0<u) (hu1 : u<1) :
    pairing ((firstState V hV u hu hu1).matrix-(secondState V hV u hu hu1).matrix)
      (embedMatrix V swapWitness) = 2*u := by
  rw [firstState_matrix,secondState_matrix]
  change (Matrix.trace ((embedMatrix V _-embedMatrix V _) * embedMatrix V swapWitness)).re = _
  rw [← embedMatrix_sub,← embedMatrix_mul V hV,embedMatrix_trace V hV,
    canonical_difference_block]
  simp [swapWitness,Matrix.blockDiagonal_apply,differenceBlock,Matrix.trace,Matrix.mul_apply,
    Fintype.sum_prod_type,Fin.sum_univ_two]
  ring

/-- Native Bures ball separation, from the supported SLD CS bound. -/
theorem bures_balls_disjoint (V : Matrix ι PairIndex ℂ) (hV : Vᴴ*V=1)
    (u : ℝ) (hu : 0<u) (hu1 : u<1) {ε : ℝ} (hε : 0 ≤ ε) (hεu : ε<u^2) :
    Disjoint {τ | chiB (firstState V hV u hu hu1) τ ≤ ENNReal.ofReal ε}
      {τ | chiB (secondState V hV u hu hu1) τ ≤ ENNReal.ofReal ε} := by
  apply Set.disjoint_left.mpr
  intro τ hp hq
  let K := embedMatrix V swapWitness
  obtain ⟨hK,hKK⟩ := pair_witness_contraction V hV
  have h0 := (witness_sq_le_chiB (firstState V hV u hu hu1) τ K hK hKK).trans hp
  have h1 := (witness_sq_le_chiB (secondState V hV u hu hu1) τ K hK hKK).trans hq
  have h0R := (ENNReal.ofReal_le_ofReal_iff hε).mp h0
  have h1R := (ENNReal.ofReal_le_ofReal_iff hε).mp h1
  have hx : pairing ((firstState V hV u hu hu1).matrix-τ.matrix) K -
      pairing ((secondState V hV u hu hu1).matrix-τ.matrix) K = 2*u := by
    rw [← pair_witness_separation V hV u hu hu1]
    simp only [pairing,Matrix.sub_mul,Matrix.trace_sub,Complex.sub_re]
    ring
  nlinarith [sq_nonneg (pairing ((firstState V hV u hu hu1).matrix-τ.matrix) K +
    pairing ((secondState V hV u hu hu1).matrix-τ.matrix) K)]

/-- Actual learner specialization for the constructed rank-one pair. -/
theorem pair_equation_53 {n r : ℕ} (H : PureBinaryTestingInput) (A : OperatorLearner ι Ω n)
    (loss : Density ι → Density ι → ℝ≥0∞)
    (V : Matrix ι PairIndex ℂ) (hV : Vᴴ*V=1)
    {u δ : ℝ} (hu : 0<u) (hu1 : u<1) (hδ : 0<δ) (hδhalf : δ<1/2)
    (hr : 1≤r) {ε : ℝ≥0∞}
    (hA : A.LearnsRank loss r ε (ENNReal.ofReal (1-δ)))
    (hd : Disjoint {τ | loss (firstState V hV u hu hu1) τ ≤ ε}
      {τ | loss (secondState V hV u hu hu1) τ ≤ ε}) :
    Real.log (1/(4*δ*(1-δ))) / (-Real.log (1-u^2)) ≤ (n : ℝ) := by
  obtain ⟨hr0,hr1⟩ := pair_ranks V hV u hu hu1
  obtain ⟨hm0,hp0⟩ := hA (firstState V hV u hu hu1) (hr0.le.trans hr)
  obtain ⟨hm1,hp1⟩ := hA (secondState V hV u hu hu1) (hr1.le.trans hr)
  apply equation_53 H A loss _ _ ε hu hu1 hδ hδhalf
    (by rw [firstState_matrix]; exact (firstProjector V hV u hu hu1).idempotent)
    (by rw [secondState_matrix]; exact (secondProjector V hV u hu hu1).idempotent)
    (pair_overlap V hV u hu hu1) hm0 hm1 hp0 hp1
  exact hd.preimage A.estimator.estimate

/-- Two actual orthonormal ambient coordinates exist in every dimension≥2. -/
def ambientEmbedding (hd : 2 ≤ Fintype.card ι) : PairIndex ↪ ι :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa [PairIndex] using hd))

/-- Appendix B's Bures confidence rate, for every actual collective operator
learner and every rank class containing pure states. -/
theorem bures_confidence {n r : ℕ} (H : PureBinaryTestingInput) (A : OperatorLearner ι Ω n)
    (hd : 2≤Fintype.card ι) (hr : 1≤r) {ε δ : ℝ}
    (hε : 0<ε) (hεsmall : ε≤1/16) (hδ : 0<δ) (hδ3 : δ≤1/3)
    (hA : A.LearnsRank chiB r (ENNReal.ofReal ε) (ENNReal.ofReal (1-δ))) :
    confidenceConstant * Real.log (1/δ) / ε ≤ (n : ℝ) := by
  let V := inclusionMatrix (ambientEmbedding hd)
  have hV : Vᴴ*V=1 := inclusionMatrix_isometry _
  let u := 2*Real.sqrt ε
  have husq : u^2=4*ε := by dsimp [u]; nlinarith [Real.sq_sqrt hε.le]
  have hu : 0<u := by dsimp [u]; positivity
  have hu1 : u<1 := by nlinarith [Real.sqrt_nonneg ε]
  have hu2 : u^2≤1/2 := by rw [husq]; linarith
  have h53 := pair_equation_53 H A chiB V hV hu hu1 hδ (by linarith) hr hA
    (bures_balls_disjoint V hV u hu hu1 hε.le (by rw [husq]; linarith))
  have h := confidence_rate_arithmetic hu hu2 hδ hδ3 h53
  rw [husq] at h
  apply (div_le_iff₀ hε).mpr
  dsimp [confidenceConstant]
  nlinarith

/-- Appendix B's right-inverse confidence rate, including singular outputs. -/
theorem right_confidence {n r : ℕ} (H : PureBinaryTestingInput) (A : OperatorLearner ι Ω n)
    (hd : 2≤Fintype.card ι) (hr : 1≤r) {ε δ : ℝ}
    (hε : 0<ε) (hεsmall : ε≤1/16) (hδ : 0<δ) (hδ3 : δ≤1/3)
    (hA : A.LearnsRank chiR r (ENNReal.ofReal ε) (ENNReal.ofReal (1-δ))) :
    confidenceConstant * Real.log (1/δ) / ε^2 ≤ (n : ℝ) := by
  let V := inclusionMatrix (ambientEmbedding hd)
  have hV : Vᴴ*V=1 := inclusionMatrix_isometry _
  let u := 2*ε
  have hu : 0<u := by dsimp [u]; positivity
  have hu1 : u<1 := by dsimp [u]; linarith
  have hu2 : u^2≤1/2 := by dsimp [u]; nlinarith
  have h53 := pair_equation_53 H A chiR V hV hu hu1 hδ (by linarith) hr hA
    (right_balls_disjoint V hV u hu hu1 hε.le (by dsimp [u]; linarith))
  have h := confidence_rate_arithmetic hu hu2 hδ hδ3 h53
  dsimp [u] at h
  apply (div_le_iff₀ (sq_pos_of_pos hε)).mpr
  dsimp [confidenceConstant]
  nlinarith

/-- The confidence convention `1-ofReal δ` agrees with `ofReal(1-δ)` in
its actual probability range. -/
theorem confidence_probability {δ : ℝ} (hδ : 0≤δ) :
    1-ENNReal.ofReal δ = ENNReal.ofReal (1-δ) := by
  rw [ENNReal.ofReal_sub 1 hδ,ENNReal.ofReal_one]

/-- A smaller failure probability implies the source's standard2/3 promise. -/
theorem learnsRank_two_thirds {n r : ℕ} (A : OperatorLearner ι Ω n)
    (loss : Density ι → Density ι → ℝ≥0∞) {ε : ℝ≥0∞} {δ : ℝ} (hδ3 : δ≤1/3)
    (hA : A.LearnsRank loss r ε (ENNReal.ofReal (1-δ))) :
    A.LearnsRank loss r ε ((2 : ℝ≥0∞)/3) := by
  have hq : ((2 : ℝ≥0∞)/3) ≤ ENNReal.ofReal (1-δ) := by
    have he : ((2 : ℝ≥0∞)/3) = ENNReal.ofReal (2/3 : ℝ) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    rw [he]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  intro ρ hr
  obtain ⟨hS,hp⟩ := hA ρ hr
  exact ⟨hS,hq.trans hp⟩

/-- Combining independent necessary bounds adds their numerators, up to a
single universal constant. No sample bound is assumed by the final wrappers. -/
lemma add_rates {a b x y N : ℝ} (hx : 0≤x) (hy : 0≤y)
    (ha : a*x≤N) (hb : b*y≤N) : min a b / 2 * (x+y) ≤ N := by
  have hax := (mul_le_mul_of_nonneg_right (min_le_left a b) hx).trans ha
  have hby := (mul_le_mul_of_nonneg_right (min_le_right a b) hy).trans hb
  nlinarith

open CollectiveMainLowerBounds SymmetricSupport

/-- A positive universal constant for the dimension plus confidence terms. -/
def combinedConstant (C : ℝ) : ℝ := min (sampleConstant C) confidenceConstant / 2

theorem combinedConstant_pos {C : ℝ} (hC : 0<C) : 0<combinedConstant C :=
  div_pos (lt_min (sampleConstant_pos hC) confidenceConstant_pos) (by norm_num)

/-- Actual collective Bures lower bound with dimension and confidence in the
same numerator. Only the original raw dimension inputs and the generic
pure binary testing theorem are parameters. -/
theorem bures_dimension_confidence {d r n : ℕ} (hcard : Fintype.card ι=d)
    (hd : 2≤d) (hr : 1≤r) (hrd : r≤d)
    (V : RawVolumeInputs (RankReduction.reducedRank d r) (d-RankReduction.reducedRank d r))
    (An : 2≤RankReduction.reducedRank d r*(d-RankReduction.reducedRank d r) →
      AnalysisInputs (2*RankReduction.reducedRank d r*(d-RankReduction.reducedRank d r)))
    (P : SymmetricProjectorInput (AmbientIndex d r) n)
    (R : OperatorRadonNikodymInput (Fin n → ι) Ω) (A : OperatorLearner ι Ω n)
    (G : GraphFisherBudget.GraphTangentInput) {C ε δ : ℝ} (hC : 0<C)
    (Nz : GraphPrior.NZSmoothLocalPriorInput C) (H : PureBinaryTestingInput)
    (hε : 0<ε) (hsmall : ε≤min (accuracyThreshold C) (1/16))
    (hδ : 0<δ) (hδ3 : δ≤1/3)
    (hA : A.LearnsRank chiB r (ENNReal.ofReal ε) (ENNReal.ofReal (1-δ))) :
    combinedConstant C *
      (Real.sqrt (r : ℝ)*d*Real.sqrt (d : ℝ)+Real.log (1/δ))/ε ≤ (n : ℝ) := by
  have hdim := MainLowerBounds.bures_collective hcard hd hr hrd V An P R A G hC Nz hε
    (hsmall.trans (min_le_left _ _)) (learnsRank_two_thirds A chiB hδ3 hA)
  have hconf := bures_confidence H A (hcard ▸ hd) hr hε
    (hsmall.trans (min_le_right _ _)) hδ hδ3 hA
  have hx : 0≤Real.sqrt (r : ℝ)*d*Real.sqrt (d : ℝ)/ε := by positivity
  have hy : 0≤Real.log (1/δ)/ε := by
    apply div_nonneg _ hε.le
    apply Real.log_nonneg
    apply (le_div_iff₀ hδ).mpr
    linarith
  have hb := add_rates hx hy hdim (by simpa only [mul_div_assoc] using hconf)
  calc
    _ = min (sampleConstant C) confidenceConstant / 2 *
        (Real.sqrt (r : ℝ)*d*Real.sqrt (d : ℝ)/ε+Real.log (1/δ)/ε) := by
      dsimp [combinedConstant]
      ring
    _ ≤ _ := hb

/-- Actual collective right-inverse lower bound with both necessary terms. -/
theorem right_dimension_confidence {d r n : ℕ} (hcard : Fintype.card ι=d)
    (hd : 2≤d) (hr : 1≤r) (hrd : r≤d)
    (V : RawVolumeInputs (RankReduction.reducedRank d r) (d-RankReduction.reducedRank d r))
    (An : 2≤RankReduction.reducedRank d r*(d-RankReduction.reducedRank d r) →
      AnalysisInputs (2*RankReduction.reducedRank d r*(d-RankReduction.reducedRank d r)))
    (P : SymmetricProjectorInput (AmbientIndex d r) n)
    (R : OperatorRadonNikodymInput (Fin n → ι) Ω) (A : OperatorLearner ι Ω n)
    (G : GraphFisherBudget.GraphTangentInput) {C ε δ : ℝ} (hC : 0<C)
    (Nz : GraphPrior.NZSmoothLocalPriorInput C) (H : PureBinaryTestingInput)
    (hε : 0<ε) (hsmall : ε≤min (accuracyThreshold C) (1/16))
    (hδ : 0<δ) (hδ3 : δ≤1/3)
    (hA : A.LearnsRank chiR r (ENNReal.ofReal ε) (ENNReal.ofReal (1-δ))) :
    combinedConstant C * ((d : ℝ)^2+Real.log (1/δ))/ε^2 ≤ (n : ℝ) := by
  have hdim := MainLowerBounds.right_collective hcard hd hr hrd V An P R A G hC Nz hε
    (hsmall.trans (min_le_left _ _)) (learnsRank_two_thirds A chiR hδ3 hA)
  have hconf := right_confidence H A (hcard ▸ hd) hr hε
    (hsmall.trans (min_le_right _ _)) hδ hδ3 hA
  have hx : 0≤(d : ℝ)^2/ε^2 := by positivity
  have hy : 0≤Real.log (1/δ)/ε^2 := by
    apply div_nonneg _ (sq_nonneg ε)
    apply Real.log_nonneg
    apply (le_div_iff₀ hδ).mpr
    linarith
  have hb := add_rates hx hy hdim (by simpa only [mul_div_assoc] using hconf)
  calc
    _ = min (sampleConstant C) confidenceConstant / 2 *
        ((d : ℝ)^2/ε^2+Real.log (1/δ)/ε^2) := by
      dsimp [combinedConstant]
      ring
    _ ≤ _ := hb

/-- The confidence rates also apply to actual dominated learners, by native
operator-POVM construction, without a new representation input. -/
theorem dominated_bures_confidence {n r : ℕ} (H : PureBinaryTestingInput)
    (A : Learner ι Ω n) (hd : 2≤Fintype.card ι) (hr : 1≤r) {ε δ : ℝ}
    (hε : 0<ε) (hεsmall : ε≤1/16) (hδ : 0<δ) (hδ3 : δ≤1/3)
    (hA : A.LearnsRank chiB r (ENNReal.ofReal ε) (ENNReal.ofReal (1-δ))) :
    confidenceConstant * Real.log (1/δ) / ε ≤ (n : ℝ) :=
  bures_confidence H (OperatorMeasureConstruction.toOperatorLearner A) hd hr hε hεsmall hδ hδ3
    ((OperatorMeasureConstruction.toOperatorLearner_learnsRank_iff A chiB r _ _).mpr hA)

theorem dominated_right_confidence {n r : ℕ} (H : PureBinaryTestingInput)
    (A : Learner ι Ω n) (hd : 2≤Fintype.card ι) (hr : 1≤r) {ε δ : ℝ}
    (hε : 0<ε) (hεsmall : ε≤1/16) (hδ : 0<δ) (hδ3 : δ≤1/3)
    (hA : A.LearnsRank chiR r (ENNReal.ofReal ε) (ENNReal.ofReal (1-δ))) :
    confidenceConstant * Real.log (1/δ) / ε^2 ≤ (n : ℝ) :=
  right_confidence H (OperatorMeasureConstruction.toOperatorLearner A) hd hr hε hεsmall hδ hδ3
    ((OperatorMeasureConstruction.toOperatorLearner_learnsRank_iff A chiR r _ _).mpr hA)

section RawAdaptive
variable {Seed : Type} [MeasurableSpace Seed]

/-- The native adaptive-to-collective measurement construction transfers the
confidence bound with the exact same fresh-copy count. -/
theorem raw_adaptive_bures_confidence {n r : ℕ} (H : PureBinaryTestingInput)
    (RF : SourceCopyComplexity.AllFixedOperatorRN ι)
    (A : AdaptiveOperatorModelTransport.OperatorLearner ι Seed Ω n)
    (hd : 2≤Fintype.card ι) (hr : 1≤r) {ε δ : ℝ}
    (hε : 0<ε) (hεsmall : ε≤1/16) (hδ : 0<δ) (hδ3 : δ≤1/3)
    (hA : A.LearnsRank (RF Ω inferInstance) chiB r (ENNReal.ofReal ε)
      (ENNReal.ofReal (1-δ))) :
    confidenceConstant * Real.log (1/δ) / ε ≤ (n : ℝ) := by
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let D := A.toDominated (RF Ω inferInstance)
    (fun k => RF (AdaptiveModel.History Seed Ω k.val × Ω) inferInstance)
  have hD : D.LearnsRank chiB r (ENNReal.ofReal ε) (ENNReal.ofReal (1-δ)) :=
    (A.toDominated_learnsRank_iff _ _ chiB r _ _).mpr hA
  exact dominated_bures_confidence H (AdaptiveCollectiveEmbedding.collectiveLearner D)
    hd hr hε hεsmall hδ hδ3
      ((AdaptiveCollectiveEmbedding.collectiveLearner_learnsRank_iff D chiB r _ _).mpr hD)

theorem raw_adaptive_right_confidence {n r : ℕ} (H : PureBinaryTestingInput)
    (RF : SourceCopyComplexity.AllFixedOperatorRN ι)
    (A : AdaptiveOperatorModelTransport.OperatorLearner ι Seed Ω n)
    (hd : 2≤Fintype.card ι) (hr : 1≤r) {ε δ : ℝ}
    (hε : 0<ε) (hεsmall : ε≤1/16) (hδ : 0<δ) (hδ3 : δ≤1/3)
    (hA : A.LearnsRank (RF Ω inferInstance) chiR r (ENNReal.ofReal ε)
      (ENNReal.ofReal (1-δ))) :
    confidenceConstant * Real.log (1/δ) / ε^2 ≤ (n : ℝ) := by
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let D := A.toDominated (RF Ω inferInstance)
    (fun k => RF (AdaptiveModel.History Seed Ω k.val × Ω) inferInstance)
  have hD : D.LearnsRank chiR r (ENNReal.ofReal ε) (ENNReal.ofReal (1-δ)) :=
    (A.toDominated_learnsRank_iff _ _ chiR r _ _).mpr hA
  exact dominated_right_confidence H (AdaptiveCollectiveEmbedding.collectiveLearner D)
    hd hr hε hεsmall hδ hδ3
      ((AdaptiveCollectiveEmbedding.collectiveLearner_learnsRank_iff D chiR r _ _).mpr hD)

/-- A confidence lower bound for the original raw adaptive learner, with the
stronger adaptive dimension numerator retained. -/
theorem raw_adaptive_bures_dimension_confidence {d r n : ℕ} (hcard : Fintype.card ι=d)
    (hd : 2≤d) (hr : 1≤r) (hrd : r≤d) {C ε δ : ℝ} (hC : 0<C)
    (I : MainCopyLowerBounds.ClassicalInputs d r C) (H : PureBinaryTestingInput)
    (RF : SourceCopyComplexity.AllFixedOperatorRN ι)
    (A : AdaptiveOperatorModelTransport.OperatorLearner ι Seed Ω n)
    (hε : 0<ε) (hsmall : ε≤min (accuracyThreshold C) (1/16))
    (hδ : 0<δ) (hδ3 : δ≤1/3)
    (hA : A.LearnsRank (RF Ω inferInstance) chiB r (ENNReal.ofReal ε)
      (ENNReal.ofReal (1-δ))) :
    combinedConstant C *
      ((r : ℝ)*Real.sqrt (r : ℝ)*d*Real.sqrt (d : ℝ)+Real.log (1/δ))/ε ≤ (n : ℝ) := by
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let R := RF Ω inferInstance
  let RJ := fun k : Fin n => RF (AdaptiveModel.History Seed Ω k.val × Ω) inferInstance
  have hA2 : A.BuresSuccess R r (ENNReal.ofReal ε) := by
    intro ρ hρ
    have he : ENNReal.ofReal (2/3 : ℝ) = (2 : ℝ≥0∞)/3 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
    refine ⟨(hA ρ hρ).1,?_⟩
    rw [← he]
    exact (ENNReal.ofReal_le_ofReal (by linarith : (2:ℝ)/3≤1-δ)).trans (hA ρ hρ).2
  have hdim := A.bures_adaptive R RJ hcard hd hr hrd I.volume I.analysis (I.symmetric n)
    I.graph hC I.prior hε (hsmall.trans (min_le_left _ _)) hA2
  have hconf := raw_adaptive_bures_confidence H RF A (hcard ▸ hd) hr hε
    (hsmall.trans (min_le_right _ _)) hδ hδ3 hA
  have hx : 0≤(r : ℝ)*Real.sqrt (r : ℝ)*d*Real.sqrt (d : ℝ)/ε := by positivity
  have hy : 0≤Real.log (1/δ)/ε := by
    apply div_nonneg _ hε.le
    exact Real.log_nonneg ((le_div_iff₀ hδ).mpr (by linarith))
  have hb := add_rates hx hy hdim (by simpa only [mul_div_assoc] using hconf)
  calc
    _ = min (sampleConstant C) confidenceConstant / 2 *
        ((r : ℝ)*Real.sqrt (r : ℝ)*d*Real.sqrt (d : ℝ)/ε+Real.log (1/δ)/ε) := by
      dsimp [combinedConstant]; ring
    _ ≤ _ := hb

theorem raw_adaptive_right_dimension_confidence {d r n : ℕ} (hcard : Fintype.card ι=d)
    (hd : 2≤d) (hr : 1≤r) (hrd : r≤d) {C ε δ : ℝ} (hC : 0<C)
    (I : MainCopyLowerBounds.ClassicalInputs d r C) (H : PureBinaryTestingInput)
    (RF : SourceCopyComplexity.AllFixedOperatorRN ι)
    (A : AdaptiveOperatorModelTransport.OperatorLearner ι Seed Ω n)
    (hε : 0<ε) (hsmall : ε≤min (accuracyThreshold C) (1/16))
    (hδ : 0<δ) (hδ3 : δ≤1/3)
    (hA : A.LearnsRank (RF Ω inferInstance) chiR r (ENNReal.ofReal ε)
      (ENNReal.ofReal (1-δ))) :
    combinedConstant C * ((r : ℝ)*(d : ℝ)^2+Real.log (1/δ))/ε^2 ≤ (n : ℝ) := by
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let R := RF Ω inferInstance
  let RJ := fun k : Fin n => RF (AdaptiveModel.History Seed Ω k.val × Ω) inferInstance
  have hA2 : A.RightSuccess R r (ENNReal.ofReal ε) := by
    intro ρ hρ
    have he : ENNReal.ofReal (2/3 : ℝ) = (2 : ℝ≥0∞)/3 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
    refine ⟨(hA ρ hρ).1,?_⟩
    rw [← he]
    exact (ENNReal.ofReal_le_ofReal (by linarith : (2:ℝ)/3≤1-δ)).trans (hA ρ hρ).2
  have hdim := A.right_adaptive R RJ hcard hd hr hrd I.volume I.analysis (I.symmetric n)
    I.graph hC I.prior hε (hsmall.trans (min_le_left _ _)) hA2
  have hconf := raw_adaptive_right_confidence H RF A (hcard ▸ hd) hr hε
    (hsmall.trans (min_le_right _ _)) hδ hδ3 hA
  have hx : 0≤(r : ℝ)*(d : ℝ)^2/ε^2 := by positivity
  have hy : 0≤Real.log (1/δ)/ε^2 := by
    apply div_nonneg _ (sq_nonneg ε)
    exact Real.log_nonneg ((le_div_iff₀ hδ).mpr (by linarith))
  have hb := add_rates hx hy hdim (by simpa only [mul_div_assoc] using hconf)
  calc
    _ = min (sampleConstant C) confidenceConstant / 2 *
        ((r : ℝ)*(d : ℝ)^2/ε^2+Real.log (1/δ)/ε^2) := by
      dsimp [combinedConstant]; ring
    _ ≤ _ := hb

end RawAdaptive

/-- Confidence extension of the original collective minimum: the actual
operator-learner collection is unchanged; only its promised probability varies. -/
def collectiveConfidenceAchievable (loss : Density ι → Density ι → ℝ≥0∞)
    (r : ℕ) (ε : ℝ≥0∞) (δ : ℝ) (n : ℕ) : Prop :=
  ∃ (Ω : Type) (mΩ : MeasurableSpace Ω), letI := mΩ
    ∃ A : OperatorLearner ι Ω n, A.LearnsRank loss r ε (ENNReal.ofReal (1-δ))

def NcollConfidence (loss : Density ι → Density ι → ℝ≥0∞)
    (r : ℕ) (ε : ℝ≥0∞) (δ : ℝ) : ℝ≥0∞ :=
  CopyComplexity.minimumCopies (collectiveConfidenceAchievable loss r ε δ)

/-- The adaptive extension still ranges over original raw operator policies. -/
def adaptiveConfidenceAchievable (RF : SourceCopyComplexity.AllFixedOperatorRN ι)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε : ℝ≥0∞) (δ : ℝ) (n : ℕ) : Prop :=
  ∃ (Seed Ω : Type) (mSeed : MeasurableSpace Seed) (mΩ : MeasurableSpace Ω),
    letI := mSeed; letI := mΩ
    ∃ A : AdaptiveOperatorModelTransport.OperatorLearner ι Seed Ω n,
      A.LearnsRank (RF Ω mΩ) loss r ε (ENNReal.ofReal (1-δ))

def NonecopyConfidence (RF : SourceCopyComplexity.AllFixedOperatorRN ι)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε : ℝ≥0∞) (δ : ℝ) : ℝ≥0∞ :=
  CopyComplexity.minimumCopies (adaptiveConfidenceAchievable RF loss r ε δ)

lemma standard_confidence : ENNReal.ofReal (1-(1/3 : ℝ)) = (2 : ℝ≥0∞)/3 := by
  have he : (1-(1/3 : ℝ)) = 2/3 := by ring
  rw [he,ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- At the source's standard confidence, this is exactly its original Ncoll. -/
theorem NcollConfidence_standard (loss : Density ι → Density ι → ℝ≥0∞)
    (r : ℕ) (ε : ℝ≥0∞) :
    NcollConfidence loss r ε (1/3) = CopyComplexity.Ncoll loss r ε := by
  unfold NcollConfidence collectiveConfidenceAchievable CopyComplexity.Ncoll
    CopyComplexity.collectiveAchievable
  rw [standard_confidence]

/-- And the adaptive version is exactly the original raw-operator minimum. -/
theorem NonecopyConfidence_standard (RF : SourceCopyComplexity.AllFixedOperatorRN ι)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε : ℝ≥0∞) :
    NonecopyConfidence RF loss r ε (1/3) = SourceCopyComplexity.Nonecopy RF loss r ε := by
  unfold NonecopyConfidence adaptiveConfidenceAchievable SourceCopyComplexity.Nonecopy
    SourceCopyComplexity.adaptiveAchievable
  rw [standard_confidence]

/-- All four original-model minima, at arbitrary confidence. Both adaptive
minima quantify original raw operator policies, with their stronger dimension
terms. The δ=1/3 identities above recover the literal original definitions. -/
theorem all_source_confidence_lower_bounds {d r : ℕ} (hcard : Fintype.card ι=d)
    (hd : 2≤d) (hr : 1≤r) (hrd : r≤d) {C ε δ : ℝ} (hC : 0<C)
    (I : MainCopyLowerBounds.ClassicalInputs d r C) (H : PureBinaryTestingInput)
    (RN : MainCopyLowerBounds.AllOperatorRN ι) (RF : SourceCopyComplexity.AllFixedOperatorRN ι)
    (hε : 0<ε) (hsmall : ε≤min (accuracyThreshold C) (1/16))
    (hδ : 0<δ) (hδ3 : δ≤1/3) :
    ENNReal.ofReal (combinedConstant C *
      (Real.sqrt (r : ℝ)*d*Real.sqrt (d : ℝ)+Real.log (1/δ))/ε) ≤
        NcollConfidence (ι:=ι) chiB r (ENNReal.ofReal ε) δ ∧
    ENNReal.ofReal (combinedConstant C *
      ((r : ℝ)*Real.sqrt (r : ℝ)*d*Real.sqrt (d : ℝ)+Real.log (1/δ))/ε) ≤
        NonecopyConfidence RF chiB r (ENNReal.ofReal ε) δ ∧
    ENNReal.ofReal (combinedConstant C * ((d : ℝ)^2+Real.log (1/δ))/ε^2) ≤
        NcollConfidence (ι:=ι) chiR r (ENNReal.ofReal ε) δ ∧
    ENNReal.ofReal (combinedConstant C * ((r : ℝ)*(d : ℝ)^2+Real.log (1/δ))/ε^2) ≤
        NonecopyConfidence RF chiR r (ENNReal.ofReal ε) δ := by
  refine ⟨?_,?_,?_,?_⟩
  · apply CopyComplexity.le_minimumCopies
    rintro n ⟨Ω,mΩ,A,hA⟩
    letI := mΩ
    have h := bures_dimension_confidence hcard hd hr hrd I.volume I.analysis (I.symmetric n)
      (RN n Ω mΩ) A I.graph hC I.prior H hε hsmall hδ hδ3 hA
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal h
  · apply CopyComplexity.le_minimumCopies
    rintro n ⟨Seed,Ω,mSeed,mΩ,A,hA⟩
    letI := mSeed
    letI := mΩ
    have h := raw_adaptive_bures_dimension_confidence hcard hd hr hrd hC I H RF A
      hε hsmall hδ hδ3 hA
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal h
  · apply CopyComplexity.le_minimumCopies
    rintro n ⟨Ω,mΩ,A,hA⟩
    letI := mΩ
    have h := right_dimension_confidence hcard hd hr hrd I.volume I.analysis (I.symmetric n)
      (RN n Ω mΩ) A I.graph hC I.prior H hε hsmall hδ hδ3 hA
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal h
  · apply CopyComplexity.le_minimumCopies
    rintro n ⟨Seed,Ω,mSeed,mΩ,A,hA⟩
    letI := mSeed
    letI := mΩ
    have h := raw_adaptive_right_dimension_confidence hcard hd hr hrd hC I H RF A
      hε hsmall hδ hδ3 hA
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal h

/-- Literal original source minima at2/3, with the same dimension-plus-log
numerators specialized to log3. The general confidence extensions are not
silently identified with the fixed-confidence original definitions. -/
theorem standard_source_minima {d r : ℕ} (hcard : Fintype.card ι=d)
    (hd : 2≤d) (hr : 1≤r) (hrd : r≤d) {C ε : ℝ} (hC : 0<C)
    (I : MainCopyLowerBounds.ClassicalInputs d r C) (H : PureBinaryTestingInput)
    (RN : MainCopyLowerBounds.AllOperatorRN ι) (RF : SourceCopyComplexity.AllFixedOperatorRN ι)
    (hε : 0<ε) (hsmall : ε≤min (accuracyThreshold C) (1/16)) :
    ENNReal.ofReal (combinedConstant C *
      (Real.sqrt (r : ℝ)*d*Real.sqrt (d : ℝ)+Real.log 3)/ε) ≤
        CopyComplexity.Ncoll (ι:=ι) chiB r (ENNReal.ofReal ε) ∧
    ENNReal.ofReal (combinedConstant C *
      ((r : ℝ)*Real.sqrt (r : ℝ)*d*Real.sqrt (d : ℝ)+Real.log 3)/ε) ≤
        SourceCopyComplexity.Nonecopy RF chiB r (ENNReal.ofReal ε) ∧
    ENNReal.ofReal (combinedConstant C * ((d : ℝ)^2+Real.log 3)/ε^2) ≤
        CopyComplexity.Ncoll (ι:=ι) chiR r (ENNReal.ofReal ε) ∧
    ENNReal.ofReal (combinedConstant C * ((r : ℝ)*(d : ℝ)^2+Real.log 3)/ε^2) ≤
        SourceCopyComplexity.Nonecopy RF chiR r (ENNReal.ofReal ε) := by
  have h := all_source_confidence_lower_bounds hcard hd hr hrd hC I H RN RF hε hsmall
    (by norm_num : (0:ℝ)<1/3) (le_refl (1/3 : ℝ))
  have hlog : Real.log (1/(1/3 : ℝ)) = Real.log 3 := by congr 1; norm_num
  simpa only [hlog,NcollConfidence_standard,NonecopyConfidence_standard] using h

/-- An actual two-outcome POVM, represented by its two PSD effects. -/
structure BinaryMeasurement (κ : Type) [Fintype κ] [DecidableEq κ] where
  first : Matrix κ κ ℂ
  second : Matrix κ κ ℂ
  first_positive : first.PosSemidef
  second_positive : second.PosSemidef
  total : first + second = 1

/-- Equal-prior error of this actual binary measurement. -/
def BinaryMeasurement.error (M : BinaryMeasurement ι) (ρ σ : Density ι) : ℝ≥0∞ :=
  ENNReal.ofReal (((Matrix.trace (ρ.matrix*M.second)).re+
    (Matrix.trace (σ.matrix*M.first)).re)/2)

/-- True optimum over all actual binary POVMs, without a prescribed test. -/
def optimalBinaryError (ρ σ : Density ι) : ℝ≥0∞ :=
  ⨅ M : BinaryMeasurement ι, M.error ρ σ

/-- The generic Helstrom lower bound and its generic attaining measurement
identify the actual optimum. This is not a P26 learning assumption. -/
theorem optimalBinaryError_eq (H : PureBinaryTestingInput) (ρ σ : Density ι)
    (hρ : ρ.matrix*ρ.matrix=ρ.matrix) (hσ : σ.matrix*σ.matrix=σ.matrix) :
    optimalBinaryError ρ σ =
      ENNReal.ofReal ((1-Real.sqrt (1-(Matrix.trace (ρ.matrix*σ.matrix)).re))/2) := by
  apply le_antisymm
  · obtain ⟨E,F,hE,hF,ht,he⟩ := H.attains ι ρ σ hρ hσ
    apply iInf_le_of_le (⟨E,F,hE,hF,ht⟩ : BinaryMeasurement ι)
    exact le_of_eq (congrArg ENNReal.ofReal he)
  · apply le_iInf
    intro M
    exact ENNReal.ofReal_le_ofReal
      (H.error_lower ι ρ σ hρ hσ M.first M.second M.first_positive M.second_positive M.total)

/-- The source's exact Ex62 formula is a native tensor-overlap specialization
of generic pure binary discrimination, including zero copies. -/
theorem tensor_optimalBinaryError (H : PureBinaryTestingInput) (ρ σ : Density ι)
    (hρ : ρ.matrix*ρ.matrix=ρ.matrix) (hσ : σ.matrix*σ.matrix=σ.matrix)
    {u : ℝ} (hov : Matrix.trace (ρ.matrix*σ.matrix)=((1-u^2 : ℝ) : ℂ)) (n : ℕ) :
    optimalBinaryError (TensorCopies.density ρ n) (TensorCopies.density σ n) =
      ENNReal.ofReal ((1-Real.sqrt (1-(1-u^2)^n))/2) := by
  have htρ : (TensorCopies.density ρ n).matrix*(TensorCopies.density ρ n).matrix =
      (TensorCopies.density ρ n).matrix := by
    change TensorCopies.matrix ρ.matrix n*TensorCopies.matrix ρ.matrix n=_
    rw [← TensorCopies.matrix_mul,hρ]
    rfl
  have htσ : (TensorCopies.density σ n).matrix*(TensorCopies.density σ n).matrix =
      (TensorCopies.density σ n).matrix := by
    change TensorCopies.matrix σ.matrix n*TensorCopies.matrix σ.matrix n=_
    rw [← TensorCopies.matrix_mul,hσ]
    rfl
  rw [optimalBinaryError_eq H _ _ htρ htσ,tensor_overlap ρ σ _ hov n]

/-- Ex62 for the same actually constructed two states used by every confidence
lower bound above, in every ambient dimension with two orthonormal columns. -/
theorem pair_optimalBinaryError (H : PureBinaryTestingInput)
    (V : Matrix ι PairIndex ℂ) (hV : Vᴴ*V=1)
    (u : ℝ) (hu : 0<u) (hu1 : u<1) (n : ℕ) :
    optimalBinaryError (TensorCopies.density (firstState V hV u hu hu1) n)
      (TensorCopies.density (secondState V hV u hu hu1) n) =
        ENNReal.ofReal ((1-Real.sqrt (1-(1-u^2)^n))/2) := by
  exact tensor_optimalBinaryError H _ _
    (by rw [firstState_matrix]; exact (firstProjector V hV u hu hu1).idempotent)
    (by rw [secondState_matrix]; exact (secondProjector V hV u hu hu1).idempotent)
    (pair_overlap V hV u hu hu1) n

end Paper26.ConfidenceLowerBounds
