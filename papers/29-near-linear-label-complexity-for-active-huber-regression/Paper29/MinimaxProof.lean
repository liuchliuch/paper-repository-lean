import Paper29.Minimax
import Paper29.SequentialMeasurability
import Paper29.LowerProof
import Paper29.UpperProof

noncomputable section
open scoped ENNReal Classical
open MeasureTheory
namespace Paper29.QueryModel

/-- The infimum over valid design-aware algorithms inherits the actual fixed
rank lower bound. The witness design is allowed to depend on n,d,r,ε only. -/
theorem minimax_lower_of_lower (lower : LowerBoundStatement) :
    ∃ c : ℝ,0<c ∧ ∀ n d r ε,1≤r → r≤min n d → 0<ε → ε≤1/800 →
      ENNReal.ofReal (lowerBudget n r c ε) ≤ minimaxCost n d r ε := by
  obtain ⟨c,hc,hl⟩ := lower
  refine ⟨c,hc,?_⟩
  intro n d r ε hr hrd hε hεhi
  obtain ⟨A,hA,hAquery⟩ := hl n d r hr hrd ε hε hεhi
  apply le_iInf
  intro a
  apply le_iInf
  intro ha
  have hlower := hAquery (a.Seed A) (a.seedMeas A) (a.law A) (ha A).1 (a.policy A) (ha A).2
  apply hlower.trans
  exact le_iSup_of_le A (le_iSup_of_le hA (le_refl _))

/-- A family of actual nonadaptive witnesses gives one admissible design-aware
adaptive algorithm, after querying precisely each witness's selected set. -/
theorem minimax_upper_of_upper (upper : UpperBoundStatement) :
    ∃ C : ℝ,0<C ∧ ∀ n d r ε,0<ε → ε<1/2 →
      minimaxCost n d r ε ≤ ENNReal.ofReal (upperBudget n r C ε) := by
  obtain ⟨C,hC,hu⟩ := upper
  refine ⟨C,hC,?_⟩
  intro n d r ε hε hεhi
  choose Ω mΩ μ hμ p hp hbudget using (fun A : Matrix (Fin n) (Fin d) ℝ => hu n d A ε hε hεhi)
  let a : DesignAlgorithm n d := {
    Seed := Ω
    seedMeas := mΩ
    law := μ
    policy := fun A => sequentialPolicy (p A) }
  have ha : a.valid ε := by
    intro A
    exact ⟨hμ A,@sequential_correct (Ω A) (mΩ A) n d (μ A) (p A) A ε (hp A)⟩
  apply (iInf_le_of_le a (iInf_le_of_le ha le_rfl)).trans
  apply iSup_le
  intro A
  apply iSup_le
  intro hA
  apply iSup_le
  intro b
  letI := mΩ A
  letI := hμ A
  change (∫⁻ ω,queryCount (sequentialPolicy (p A)) ω b ∂μ A) ≤ _
  calc
    _ ≤ ∫⁻ _ω : Ω A,ENNReal.ofReal (upperBudget n r C ε) ∂μ A := by
      apply lintegral_mono
      intro ω
      dsimp only
      rw [sequential_queryCount]
      have hb := hbudget A ω
      rw [hA] at hb
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hb
    _ = _ := by simp

/-- Exact minimax infimum/supremum consequence of the two main statements. -/
theorem minimax_bounds_of_main (upper : UpperBoundStatement) (lower : LowerBoundStatement) :
    MinimaxBoundsStatement := by
  obtain ⟨c,hc,hl⟩ := minimax_lower_of_lower lower
  obtain ⟨C,hC,hu⟩ := minimax_upper_of_upper upper
  refine ⟨c,C,hc,hC,?_⟩
  intro n d r ε hr hrd hε hεhi
  exact ⟨hl n d r ε hr hrd hε hεhi,hu n d r ε hε (by linarith)⟩

theorem corollary2_3 (C Cₜ Cₑ : ℝ) (hC : 0<C) (hCₜ : 0<Cₜ) (hCₑ : 0<Cₑ)
    (external : ExternalProcess.AnchoredChaining C)
    (stability : WeightConstruction.RadiusLogNonexpansive)
    (transition : ExternalCovering.HuberPrimitive 4 Cₜ)
    (endpoint : ExternalCovering.PowerPrimitive Cₑ) (lewis : ExternalCovering.LewisOneNormalization) :
    MinimaxBoundsStatement :=
  minimax_bounds_of_main (ProcessTools.theorem2_1 C Cₜ Cₑ hC hCₜ hCₑ external stability transition endpoint lewis) theorem2_2

end Paper29.QueryModel
