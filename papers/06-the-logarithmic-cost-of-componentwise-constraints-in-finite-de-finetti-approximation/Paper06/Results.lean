import Paper06.Model
import Paper06.ConditioningFull
import Paper06.ResponseFull
import Paper06.FullLowerBound

open Real Set BigOperators MeasureTheory
open scoped Classical

namespace Paper06

/-- **Proposition 2.2**, with a genuine Borel probability measure on the
original affine slice and relative entropy retaining its infinite value. -/
theorem proposition_2_2 {α E : Type*} [Fintype α] [AddCommGroup E] [Module ℝ E]
    (Γ : (α → ℝ) →ₗ[ℝ] E) (η : E) {n k : ℕ}
    (P : FinProb (Fin n → α)) (hP : Posterior.Exchangeable P)
    (c : Fin n) (hCP : Posterior.LiftedCP Γ η P c)
    (hk : 1 ≤ k) (hn : k < n) :
    ∃ μ : ProbabilityMeasure (Posterior.AffineSlice Γ η),
      FinProb.kl (marginal P k hn.le)
        (FinProb.feasibleProductMixture (Posterior.AffineSlice Γ η)
          (μ : Measure (Posterior.AffineSlice Γ η)) k) ≤
        ((((k : ℝ) * (k - 1) / (2 * ((n : ℝ) - k + 1))) *
          log (Fintype.card α) : ℝ) : EReal) := by
  obtain ⟨m, _, w, q, hq, _, hbound⟩ :=
    ConditioningFull.prop_2_2_conditioning_upper_bound Γ η P hP c hCP hk hn
  let qF : (Fin m → α) → Posterior.AffineSlice Γ η := fun b => ⟨q b, hq b⟩
  let μ : ProbabilityMeasure (Posterior.AffineSlice Γ η) :=
    ⟨FinProb.atomicMixingMeasure (Posterior.AffineSlice Γ η) w qF, inferInstance⟩
  refine ⟨μ, ?_⟩
  change FinProb.kl (marginal P k hn.le)
    (FinProb.feasibleProductMixture (Posterior.AffineSlice Γ η)
      (FinProb.atomicMixingMeasure (Posterior.AffineSlice Γ η) w qF) k) ≤ _
  rw [FinProb.feasibleProductMixture_atomic]
  exact hbound

/-- The uniform conditioning bound for the optimum over all mixing measures. -/
theorem constrainedError_le_conditioning {α : Type*} [Fintype α] {n k : ℕ}
    (A : Admissible α n) (hk : 1 ≤ k) (hn : k < n) :
    constrainedError A.law A.slice k hn.le ≤
      ((((k : ℝ) * (k - 1) / (2 * ((n : ℝ) - k + 1))) *
        log (Fintype.card α) : ℝ) : EReal) := by
  let c : Fin n := ⟨0, by omega⟩
  obtain ⟨μ, hμ⟩ := proposition_2_2 A.Γ A.η A.law A.exchangeable c (A.cp c) hk hn
  exact (constrainedError_le A.law A.slice k hn.le μ).trans hμ

/-- Equation (2), taking the supremum over all original admissible data. -/
theorem worstConstrainedError_le_conditioning (d n k : ℕ) (hk : 1 ≤ k) (hn : k < n) :
    worstConstrainedError d n k hn.le ≤
      ((((k : ℝ) * (k - 1) / (2 * ((n : ℝ) - k + 1))) * log d : ℝ) : EReal) := by
  apply iSup_le
  intro alphabet
  letI := alphabet.finite
  apply iSup_le
  intro A
  simpa only [alphabet.card_eq] using constrainedError_le_conditioning A hk hn

/-- The slice of all one-site laws with the prescribed input marginal. -/
def inputFiberSlice {X A : Type*} [Fintype X] [Fintype A]
    (piLaw : FinProb X) (label : A → X) : Set (FinProb A) :=
  {q | FinProb.map q label = piLaw}

/-- **Proposition 4.1**, with a single Borel probability mixing measure,
all zero input masses, and arbitrary finite input-dependent outputs.
A section of `label` chooses one allowed output for each input. -/
theorem proposition_4_1 {X A : Type*} [Fintype X] [Fintype A]
    (piLaw : FinProb X) (label : A → X) (response : X → A)
    (hsection : ∀ x, label (response x) = x)
    (n : ℕ) (P : FinProb (Fin n → A)) (hP : Posterior.Exchangeable P)
    (c : Fin n) (hCP : Posterior.LiftedCP (Response.labelΓ label) piLaw.w P c)
    (hn : Fintype.card (SupportReduction.InputSupport piLaw) ≤ n) :
    ∃ μ : ProbabilityMeasure (inputFiberSlice piLaw label),
      ∀ k, 1 ≤ k → (hk : k ≤ n / Fintype.card (SupportReduction.InputSupport piLaw)) →
        FinProb.kl (marginal P k (hk.trans (Nat.div_le_self _ _)))
          (FinProb.feasibleProductMixture (inputFiberSlice piLaw label) (μ : Measure _) k) ≤
          (Sampling.cost (n / Fintype.card (SupportReduction.InputSupport piLaw)) k : EReal) ∧
        Sampling.cost (n / Fintype.card (SupportReduction.InputSupport piLaw)) k ≤
          (k * (k - 1) : ℝ) /
            (2 * (((n / Fintype.card (SupportReduction.InputSupport piLaw) : ℕ) : ℝ) - k + 1)) := by
  classical
  obtain ⟨ν, q, hq, hb⟩ := Response.prop_4_1_labelled piLaw label response hsection n P hP c hCP hn
  let qF : (Fin n → A) → inputFiberSlice piLaw label := fun u => ⟨q u, hq u⟩
  let μ : ProbabilityMeasure (inputFiberSlice piLaw label) :=
    ⟨FinProb.atomicMixingMeasure (inputFiberSlice piLaw label) ν qF, inferInstance⟩
  refine ⟨μ, ?_⟩
  intro k hk1 hkM
  obtain ⟨_, hkl, hcost⟩ := hb k hk1 hkM
  refine ⟨?_, hcost⟩
  change FinProb.kl (marginal P k _)
    (FinProb.feasibleProductMixture (inputFiberSlice piLaw label)
      (FinProb.atomicMixingMeasure (inputFiberSlice piLaw label) ν qF) k) ≤ _
  rw [FinProb.feasibleProductMixture_atomic]
  exact hkl

/-- The disjoint-union alphabet in the source is a direct specialization
of Proposition 4.1; every fiber may have its own finite output alphabet. -/
theorem proposition_4_1_dependent {X : Type*} [Fintype X]
    (A : X → Type*) [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]
    (piLaw : FinProb X) (n : ℕ) (P : FinProb (Fin n → Sigma A))
    (hP : Posterior.Exchangeable P) (c : Fin n)
    (hCP : Posterior.LiftedCP (Response.labelΓ (Sigma.fst : Sigma A → X)) piLaw.w P c)
    (hn : Fintype.card (SupportReduction.InputSupport piLaw) ≤ n) :
    ∃ μ : ProbabilityMeasure (inputFiberSlice piLaw (Sigma.fst : Sigma A → X)),
      ∀ k, 1 ≤ k → (hk : k ≤ n / Fintype.card (SupportReduction.InputSupport piLaw)) →
        FinProb.kl (marginal P k (hk.trans (Nat.div_le_self _ _)))
          (FinProb.feasibleProductMixture (inputFiberSlice piLaw (Sigma.fst : Sigma A → X))
            (μ : Measure _) k) ≤
          (Sampling.cost (n / Fintype.card (SupportReduction.InputSupport piLaw)) k : EReal) ∧
        Sampling.cost (n / Fintype.card (SupportReduction.InputSupport piLaw)) k ≤
          (k * (k - 1) : ℝ) /
            (2 * (((n / Fintype.card (SupportReduction.InputSupport piLaw) : ℕ) : ℝ) - k + 1)) := by
  exact proposition_4_1 piLaw Sigma.fst (fun x => ⟨x, Classical.choice (inferInstance : Nonempty (A x))⟩)
    (fun _ => rfl) n P hP c hCP hn

/-- Equation (18), for every admissible matching parameter and marginal
size, with the original optimum and worst-case error between the two bounds. -/
theorem matching_error_sandwich {F : Type} [Fintype F] [Field F]
    (n k : ℕ) (hEven : Even n) (hn : 6 ≤ n) (hk2 : 2 ≤ k)
    (hkk : k * k ≤ n) (θ : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2)
    (hparam : 2 * Real.exp 1 * ((n : ℝ) - 1) ≤
      (Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 - θ)) :
    let hk : k ≤ n := by nlinarith
    let t := (k : ℝ) * (k - 1) * log ((Fintype.card F : ℝ) ^ 2) / (n - k + 1)
    (((3 * θ / 32) * t : ℝ) : EReal) ≤
      constrainedError (Matching.matchingLawFin (R := F) n hEven)
        {q : FinProb (F × F) | UniformInput q} k hk ∧
    constrainedError (Matching.matchingLawFin (R := F) n hEven)
        {q : FinProb (F × F) | UniformInput q} k hk ≤
      worstConstrainedError (Fintype.card F ^ 2) n k hk ∧
    worstConstrainedError (Fintype.card F ^ 2) n k hk ≤ ((t / 2 : ℝ) : EReal) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · convert matching_constrainedError_lower n k hEven hn hk2 hkk θ hθ hθhalf hparam using 1 <;> ring
  · have h := constrainedError_le_worst (matchingAdmissible F n hEven) k (by nlinarith)
    simpa only [matchingAdmissible_slice, Fintype.card_prod,
      ← pow_two] using h
  · have h := worstConstrainedError_le_conditioning (Fintype.card F ^ 2) n k (by omega) (by nlinarith)
    rw [Nat.cast_pow] at h
    have hd : (n : ℝ) - k + 1 ≠ 0 := by
      have hkn : k ≤ n := by nlinarith
      have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
      linarith
    have heq : (k : ℝ) * (k - 1) / (2 * ((n : ℝ) - k + 1)) *
        log ((Fintype.card F : ℝ) ^ 2) =
        ((k : ℝ) * (k - 1) * log ((Fintype.card F : ℝ) ^ 2) / (n - k + 1)) / 2 := by
      field_simp [hd]
      <;> ring
    rw [heq] at h
    exact h

end Paper06
