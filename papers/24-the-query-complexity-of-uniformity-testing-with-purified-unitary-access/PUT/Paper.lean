import PUT.AdversaryConstruction
import PUT.TesterPromises
import PUT.PriorPromises
import PUT.FiniteRegisters
import PUT.CollisionTester
import PUT.AdaptiveModel
import PUT.AdaptiveTruncation

/-!
# The principal query lower bound of paper 24

The three external inputs are precisely the standard Dirichlet joint moment
law, standard independent-run error reduction, and Kutin's collision theorem.
Every paper-specific hard instance, operator bound, prior mass, progress
argument, simulation cost and parameter choice is supplied by proved modules.
-/
noncomputable section
namespace PUT.Paper
open MeasureTheory QueryModel SourceTargets FourierModel TesterPromises
open TestingLowerBound ParameterLowerBound

/-- Operational hard-prior lower bound at the one scale selected for this
accuracy. The actual tester is amplified once and then evaluated on the
proved continuous priors, with a legal integer garbage dimension for each A. -/
theorem small_scale_query_lower
    (hMom : External.DirichletJointMomentLaw)
    (hAmplify : External.NinefoldAmplificationLaw)
    {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 48)
    (C : TesterFamily d) (Q : ℕ) (hC : C.Tests ε Q) :
    AtScaleBound (dirichletScale ε) d Q := by
  let a := dirichletScale ε
  have ha1 : 1 ≤ a := dirichletScale_ge_one hε hsmall
  have ha : 0 < a := by linarith
  have hd0 : 0 < d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨D, hAmp⟩ := amplification_exists hAmplify C Q
  intro A hA
  let M := FiniteRegisters.garbageSize A
  have hM : 0 < M := FiniteRegisters.garbageSize_pos hA
  have hparam : 16 * A ^ 2 * LA A ≤ (M : ℝ) :=
    FiniteRegisters.garbageSize_sufficient hA
  letI := alternative_probability d M ha
  obtain ⟨Γ, hΓ⟩ := AdversaryConstruction.exists_tester_adversary
    hMom hd ha hM A hA hparam D
  have hB : 0 < lemma1RHS A a d := lemma1RHS_pos A a d hA ha1 hdR
  exact prior_query_lower_ninefold_tv (fun x : (Fin d → ℝ) × Torus d M => x.1)
    measurable_fst hε (D.circuit M) (nullField D hd0 hM)
    (alternativeField D hd0 ha hM) Γ A (lemma1RHS A a d) q0 ninefoldError Q
    (by linarith) hB (by norm_num [q0]) (by norm_num [q0])
    ninefoldError_nonneg (by simpa only [q0] using paper_ninefold_error.le) hΓ
    (PriorPromises.good_event_mass hMom hd hε hsmall)
    (null_success hC hAmp hd0 hM) (alternative_success hC hAmp hd0 ha hM)

/-- Source Theorem 1, with actual query count and universal success over all
valid full preparation unitaries, including controlled inverse access. -/
theorem theorem1 (hMom : External.DirichletJointMomentLaw)
    (hAmplify : External.NinefoldAmplificationLaw)
    (hKutin : External.KutinCollisionLaw) : SourceTargets.Theorem1 := by
  obtain ⟨k, hk, hcollision⟩ := CollisionTester.constant_accuracy_lower hKutin
  refine ⟨finalConstant k, finalConstant_pos hk, ?_⟩
  intro d ε hd hε hεmax C Q hC
  apply full_accuracy_query_lower d ε Q k (by exact_mod_cast hd) hε hεmax hk
  · intro hsmall
    exact small_scale_query_lower hMom hAmplify hd hε hsmall C Q hC
  · intro _
    exact hcollision d ε hd hεmax C Q hC

/-- Source Lemma 2, retaining the sole standard analytic input explicitly. -/
theorem lemma2 (hMom : External.DirichletJointMomentLaw) : SourceTargets.Lemma2 :=
  lemma2_from_joint_moments hMom

/-- The same source bound for genuinely adaptive finite protocols, with
measurements, branch-dependent directions and early stopping. The published
standard normalization law is visible, and its two-query scheduling loss is
absorbed into the absolute constant by a proved transfer theorem. -/
theorem theorem1_adaptive (hMom : External.DirichletJointMomentLaw)
    (hAmplify : External.NinefoldAmplificationLaw)
    (hKutin : External.KutinCollisionLaw)
    (hNormal : External.AdaptiveNormalizationLaw) : AdaptiveModel.AdaptiveTheorem1 :=
  AdaptiveModel.adaptive_lower_of_normalized hNormal (theorem1 hMom hAmplify hKutin)

/-- Full source Theorem 1 with promise-only worst-case query count.
The internal truncation proof permits arbitrary behavior away from the promise. -/
theorem theorem1_promised (hMom : External.DirichletJointMomentLaw)
    (hAmplify : External.NinefoldAmplificationLaw)
    (hKutin : External.KutinCollisionLaw)
    (hNormal : External.AdaptiveNormalizationLaw) : AdaptiveModel.PromiseAdaptiveTheorem1 :=
  AdaptiveModel.promise_adaptive_lower_of_normalized hNormal (theorem1 hMom hAmplify hKutin)

end PUT.Paper
