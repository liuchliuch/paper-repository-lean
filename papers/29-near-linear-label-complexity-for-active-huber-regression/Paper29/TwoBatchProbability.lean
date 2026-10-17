import Paper29.TwoBatchSuccess

noncomputable section
open scoped BigOperators Classical
namespace Paper29.ProcessTools

def pilotConstant (δ₀ : ℝ) : ℝ := (1+2/Real.sqrt ((1-1/8)*δ₀))^2

theorem scoreProbability_nonneg {n : ℕ} (hn : 1 ≤ n) (τ : Fin n → ℝ)
    (hτ : ∀ i, 0 < τ i) : ∀ i, 0 ≤ scoreProbability τ i :=
  fun i => ((scoreProbability_spec hn τ hτ).2.1 i).le

/-- The complete actual two-batch probability guarantee on a reduced design.
The residual is selected from the pilot only, and conditional main bounds are
integrated over the independent product law. This theorem includes zero optimum. -/
theorem two_batch_probability {n d m₀ m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (hn : 16 < n) (τ : Fin n → ℝ) (hτ : ∀ i, 0 < τ i)
    (C G δ₀ δ η ε : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hδ₀ : 0 < δ₀) (hδ₀hi : δ₀ ≤ 1) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hη : 0 < η) (hηhi : η < 1/2) (hε : 0 ≤ ε)
    (hηdef : η = (2*ε+ε^2)/(2*pilotConstant δ₀))
    (external : ExternalProcess.AnchoredChaining C)
    (cover : ScoreGeometry A τ (G*logFactor n))
    (hsize₀ : (128*C*G)^2 * (2*∑ i,τ i) * Real.log (2*(n:ℝ))^3 *
      ((pilotGrid n).card:ℝ)^2 / δ₀^2 ≤ (m₀:ℝ))
    (hsize : transferConstant C G 16 * (∑ i,τ i) * Real.log (2*(n:ℝ))^3 /
      (η^2*δ^2) ≤ (m:ℝ)) (b : Fin n → ℝ) :
    let π₀ := scoreProbability (pilotScores τ)
    let π := scoreProbability τ
    let hp₀ := pilotProbability_nonneg (by omega) τ hτ
    let hp := scoreProbability_nonneg (by omega) τ hτ
    1-2*δ₀-δ ≤ Sampling.eventMass (batchMass π₀ π)
      (Finset.univ.filter (fun ω : (Fin m₀ → Fin n) × (Fin m → Fin n) =>
        ∀ x, Real.sqrt (objective A b (twoBatchOutput A b π₀ π hp₀ hp ω)) ≤
          (1+ε)*Real.sqrt (objective A b x))) := by
  have hn1 : 1 ≤ n := by omega
  let π₀ := scoreProbability (pilotScores τ)
  let π := scoreProbability τ
  have hp₀ := pilotProbability_nonneg hn1 τ hτ
  have hp := scoreProbability_nonneg hn1 τ hτ
  obtain ⟨hT, hπ, hsum, hrel⟩ := scoreProbability_spec hn1 τ hτ
  obtain ⟨_, hπ₀, hsum₀, _⟩ := scoreProbability_spec hn1 (pilotScores τ) (pilotScores_spec hn1 τ hτ).1
  obtain ⟨xstar, hopt⟩ := Attainment.affineHuber_attains A (fun _ => 1) b (fun _ => by norm_num)
  have hopt' : ∀ x, objective A b xstar ≤ objective A b x := by
    simpa only [Attainment.affineHuber, weightedHuber, one_mul, objective] using hopt
  let E := fun μ : Fin m₀ → Fin n => objective A b (pilotCenter A b π₀ hp₀ μ) ≤
    pilotConstant δ₀ * objective A b xstar
  let F := fun (μ : Fin m₀ → Fin n) (ν : Fin m → Fin n) =>
    baseline (pilotResidual A b π₀ hp₀ μ) = 0 ∨
      CenteredTransferEvent A (pilotResidual A b π₀ hp₀ μ) π
        (16*baseline (pilotResidual A b π₀ hp₀ μ)) (η*baseline (pilotResidual A b π₀ hp₀ μ)) ν
  have hE : 1-2*δ₀ ≤ Sampling.eventMass (Sampling.iidMass π₀) (Finset.univ.filter E) :=
    pilot_guarantee A hn τ hτ C G δ₀ hC hG hδ₀ hδ₀hi external cover hsize₀ b xstar
  have hF (μ : Fin m₀ → Fin n) (_ : E μ) :
      1-δ ≤ Sampling.eventMass (Sampling.iidMass π) (Finset.univ.filter (F μ)) := by
    let z := pilotResidual A b π₀ hp₀ μ
    have hz : 0 ≤ baseline z := Finset.sum_nonneg (fun i _ => huber_nonneg _)
    by_cases hzero : baseline z = 0
    · have he : Finset.univ.filter (F μ) = Finset.univ := by
        ext ν
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, F]
        exact iff_true_intro (Or.inl hzero)
      rw [he]
      simp only [Sampling.eventMass, Sampling.iidMass_sum π hsum]
      linarith
    · have hpz : 0 < baseline z := lt_of_le_of_ne hz (Ne.symm hzero)
      have ht := (centered_affine_transfer_scores A hn1 τ hτ C G 16 η δ hC hG external
        cover (by norm_num) hη hηhi hδ hδhi z hpz hsize).2
      apply ht.trans
      apply eventMass_mono _ (Sampling.iidMass_nonneg π hp)
      intro ν hν
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (Finset.mem_filter.mp hν).2⟩
  have hprob := independent_good_events (Sampling.iidMass π₀) (Sampling.iidMass π)
    (Sampling.iidMass_nonneg π₀ hp₀) (Sampling.iidMass_nonneg π hp)
    (Sampling.iidMass_sum π₀ hsum₀) (Sampling.iidMass_sum π hsum) E F hδ.le hE hF
  have hC₀ : 0 < pilotConstant δ₀ := by unfold pilotConstant; positivity
  dsimp only
  apply hprob.trans
  apply eventMass_mono _ (batchMass_nonneg π₀ π hp₀ hp)
  intro ω hω
  obtain ⟨hEω, hFω⟩ := (Finset.mem_filter.mp hω).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  exact twoBatch_good_implies_success A b π₀ π hp₀ hp ω.1 ω.2 xstar hopt'
    hC₀ hε (by linarith) hηdef hEω hFω

end Paper29.ProcessTools
