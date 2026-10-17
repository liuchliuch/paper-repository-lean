import Paper15.Main
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Actual output laws and the sufficiency direction of Corollary 2

The witness below is a measurable classical model whose response probabilities
are `(1 + η F)/2`. These are the kernels obtained by independently flipping
the original deterministic outputs with sign noise of mean `η`. Equality is
proved for every outcome, rather than merely for the three aggregate moments.
-/

noncomputable section
namespace Paper15
open Finset BigOperators MeasureTheory

/-- A ternary source law as a probability mass function. -/
def Simplex2.toPMF (q : Simplex2) : PMF (Fin 3) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (q i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => q.nonneg i), q.sum_eq]
    simp)

@[simp] lemma Simplex2.toPMF_toReal (q : Simplex2) (i : Fin 3) :
    (q.toPMF i).toReal = q i := ENNReal.toReal_ofReal (q.nonneg i)

/-- Integration against the actual source measure equals the weighted sum. -/
lemma Simplex2.integral_toPMF (q : Simplex2) (f : Fin 3 → ℝ) :
    (∫ i, f i ∂q.toPMF.toMeasure) = ∑ i, q i * f i := by
  rw [PMF.integral_eq_sum]
  simp only [Simplex2.toPMF_toReal, smul_eq_mul]

/-- The expectation operator for three independent finite sources. -/
def sourceExp (qx qy qz : Simplex2) (f : Fin 3 → Fin 3 → Fin 3 → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, qx i * qy j * qz k * f i j k

lemma sourceExp_add (qx qy qz : Simplex2) (f g : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    sourceExp qx qy qz (fun i j k => f i j k + g i j k) =
      sourceExp qx qy qz f + sourceExp qx qy qz g := by
  simp [sourceExp, mul_add, sum_add_distrib]

lemma sourceExp_smul (qx qy qz : Simplex2) (r : ℝ)
    (f : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    sourceExp qx qy qz (fun i j k => r * f i j k) = r * sourceExp qx qy qz f := by
  simp only [sourceExp, mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  ring

lemma sourceExp_const (qx qy qz : Simplex2) (r : ℝ) :
    sourceExp qx qy qz (fun _ _ _ => r) = r := by
  unfold sourceExp
  simp_rw [mul_assoc, ← mul_sum, ← sum_mul]
  rw [qx.sum_eq, qy.sum_eq, qz.sum_eq]
  ring

/-- Conditional kernels from a table and independent sign noise of mean `η`. -/
def noisyModel (T : DetTriangle) (qx qy qz : Simplex2) (η : ℝ)
    (hη : η ∈ Set.Icc (0 : ℝ) 1) : TriangleModel where
  X := Fin 3
  Y := Fin 3
  Z := Fin 3
  mX := inferInstance
  mY := inferInstance
  mZ := inferInstance
  μX := qx.toPMF.toMeasure
  μY := qy.toPMF.toMeasure
  μZ := qz.toPMF.toMeasure
  isProbX := inferInstance
  isProbY := inferInstance
  isProbZ := inferInstance
  pA j k := (1 + η * T.A j k) / 2
  pB k i := (1 + η * T.B k i) / 2
  pC i j := (1 + η * T.C i j) / 2
  pA_mem j k := by rcases T.A.legal j k with h | h <;> rw [h] <;> constructor <;> nlinarith [hη.1, hη.2]
  pB_mem k i := by rcases T.B.legal k i with h | h <;> rw [h] <;> constructor <;> nlinarith [hη.1, hη.2]
  pC_mem i j := by rcases T.C.legal i j with h | h <;> rw [h] <;> constructor <;> nlinarith [hη.1, hη.2]
  pA_measurable := measurable_of_finite _
  pB_measurable := measurable_of_finite _
  pC_measurable := measurable_of_finite _

lemma noisyModel_output (T : DetTriangle) (qx qy qz : Simplex2)
    (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1) (a b c : ℝ) :
    (noisyModel T qx qy qz η hη).output a b c =
      sourceExp qx qy qz (fun i j k =>
        ((1 + a * η * T.A j k) * (1 + b * η * T.B k i) *
          (1 + c * η * T.C i j)) / 8) := by
  simp only [TriangleModel.output, TriangleModel.condA, TriangleModel.condB,
    TriangleModel.condC, noisyModel]
  simp_rw [Simplex2.integral_toPMF]
  simp only [sourceExp, mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  ring

/-- Binary Fourier inversion for a noisy deterministic model. -/
lemma noisyModel_fourier (T : DetTriangle) (qx qy qz : Simplex2)
    (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1) (a b c : ℝ) :
    (noisyModel T qx qy qz η hη).output a b c =
      (1 + a * η * sourceExp qx qy qz (fun _ j k => T.A j k)
        + b * η * sourceExp qx qy qz (fun i _ k => T.B k i)
        + c * η * sourceExp qx qy qz (fun i j _ => T.C i j)
        + a * b * η^2 * sourceExp qx qy qz (fun i j k => T.A j k * T.B k i)
        + b * c * η^2 * sourceExp qx qy qz (fun i j k => T.B k i * T.C i j)
        + c * a * η^2 * sourceExp qx qy qz (fun i j k => T.C i j * T.A j k)
        + a * b * c * η^3 * sourceExp qx qy qz (fun i j k => T.A j k * T.B k i * T.C i j)) / 8 := by
  rw [noisyModel_output]
  have hpoly : (fun i j k =>
        ((1 + a * η * T.A j k) * (1 + b * η * T.B k i) *
          (1 + c * η * T.C i j)) / 8) =
      (fun i j k => (1 / 8 : ℝ) *
        (1 + (a * η) * T.A j k + (b * η) * T.B k i + (c * η) * T.C i j
          + (a * b * η^2) * (T.A j k * T.B k i)
          + (b * c * η^2) * (T.B k i * T.C i j)
          + (c * a * η^2) * (T.C i j * T.A j k)
          + (a * b * c * η^3) * (T.A j k * T.B k i * T.C i j))) := by
    funext i j k
    ring
  rw [hpoly]
  simp only [sourceExp_smul, sourceExp_add, sourceExp_const]
  ring

/-- All three individual means in the attaining model vanish. -/
lemma attaining_individual_means :
    sourceExp attLaw attLaw attLaw (fun _ j k => DetTriangle.exceptional.A j k) = 0 ∧
    sourceExp attLaw attLaw attLaw (fun i _ k => DetTriangle.exceptional.B k i) = 0 ∧
    sourceExp attLaw attLaw attLaw (fun i j _ => DetTriangle.exceptional.C i j) = 0 := by
  have h := congrArg AggregateMoments.M1 attaining_moments_tStar
  have heq :
      sourceExp attLaw attLaw attLaw (fun _ j k => DetTriangle.exceptional.A j k) =
      sourceExp attLaw attLaw attLaw (fun i _ k => DetTriangle.exceptional.B k i) ∧
      sourceExp attLaw attLaw attLaw (fun i _ k => DetTriangle.exceptional.B k i) =
      sourceExp attLaw attLaw attLaw (fun i j _ => DetTriangle.exceptional.C i j) := by
    simp only [sourceExp, attLaw, eA_exceptional, eB_exceptional, eC_exceptional]
    trivial
  change (sourceExp attLaw attLaw attLaw (fun _ j k => DetTriangle.exceptional.A j k) +
    sourceExp attLaw attLaw attLaw (fun i _ k => DetTriangle.exceptional.B k i) +
    sourceExp attLaw attLaw attLaw (fun i j _ => DetTriangle.exceptional.C i j)) / 3 = 0 at h
  exact ⟨by linarith [heq.1, heq.2], by linarith [heq.1, heq.2], by linarith [heq.1, heq.2]⟩

lemma attaining_individual_pairs :
    sourceExp attLaw attLaw attLaw (fun i j k => DetTriangle.exceptional.A j k * DetTriangle.exceptional.B k i) = tStar ∧
    sourceExp attLaw attLaw attLaw (fun i j k => DetTriangle.exceptional.B k i * DetTriangle.exceptional.C i j) = tStar ∧
    sourceExp attLaw attLaw attLaw (fun i j k => DetTriangle.exceptional.C i j * DetTriangle.exceptional.A j k) = tStar := by
  have h := congrArg AggregateMoments.M2 attaining_moments_tStar
  have heq :
      sourceExp attLaw attLaw attLaw (fun i j k => DetTriangle.exceptional.A j k * DetTriangle.exceptional.B k i) =
      sourceExp attLaw attLaw attLaw (fun i j k => DetTriangle.exceptional.B k i * DetTriangle.exceptional.C i j) ∧
      sourceExp attLaw attLaw attLaw (fun i j k => DetTriangle.exceptional.B k i * DetTriangle.exceptional.C i j) =
      sourceExp attLaw attLaw attLaw (fun i j k => DetTriangle.exceptional.C i j * DetTriangle.exceptional.A j k) := by
    simp only [sourceExp, attLaw, eAB_exceptional, eBC_exceptional, eCA_exceptional]
    trivial
  change (sourceExp attLaw attLaw attLaw (fun i j k => DetTriangle.exceptional.A j k * DetTriangle.exceptional.B k i) +
    sourceExp attLaw attLaw attLaw (fun i j k => DetTriangle.exceptional.B k i * DetTriangle.exceptional.C i j) +
    sourceExp attLaw attLaw attLaw (fun i j k => DetTriangle.exceptional.C i j * DetTriangle.exceptional.A j k)) / 3 = tStar at h
  exact ⟨by linarith [heq.1, heq.2], by linarith [heq.1, heq.2], by linarith [heq.1, heq.2]⟩

/-- Section 2 as an equality of actual output distributions. -/
theorem noisy_attaining_output (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1) (a b c : ℝ) :
    (noisyModel DetTriangle.exceptional attLaw attLaw attLaw η hη).output a b c =
      p_t (η^2 * tStar) a b c := by
  rw [noisyModel_fourier]
  obtain ⟨hA, hB, hC⟩ := attaining_individual_means
  obtain ⟨hAB, hBC, hCA⟩ := attaining_individual_pairs
  have hABC : sourceExp attLaw attLaw attLaw
      (fun i j k => DetTriangle.exceptional.A j k * DetTriangle.exceptional.B k i * DetTriangle.exceptional.C i j) = 0 :=
    congrArg AggregateMoments.M3 attaining_moments_tStar
  rw [hA, hB, hC, hAB, hBC, hCA, hABC]
  dsimp [p_t]
  ring

/-- Corollary 2, sufficiency: actual measurable response kernels realize `p_t`
for every `t ∈ [0,t_*]`. -/
theorem corollary2_sufficiency (t : ℝ) (ht : 0 ≤ t) (hle : t ≤ tStar) :
    IsTriangleLocal t := by
  let η := Real.sqrt (t / tStar)
  have hη : η ∈ Set.Icc (0 : ℝ) 1 := eta_mem tStar_pos ht hle
  refine ⟨noisyModel DetTriangle.exceptional attLaw attLaw attLaw η hη,
    fun a b c _ _ _ => ?_⟩
  have hsq : η^2 * tStar = t := by
    dsimp [η]
    rw [Real.sq_sqrt (div_nonneg ht tStar_pos.le)]
    exact div_mul_cancel₀ t tStar_pos.ne'
  rw [noisy_attaining_output, hsq]

end Paper15
