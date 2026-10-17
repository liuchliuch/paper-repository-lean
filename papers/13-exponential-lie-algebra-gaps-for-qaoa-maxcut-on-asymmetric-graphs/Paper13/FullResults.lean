import Paper13.Main
import Paper13.ActualGap
import Paper13.Proposition5
import Paper13.InitialSector
import Paper13.PlusDimension
import Paper13.AutomorphismSymmetry
import Paper13.LocalNonPreservation
noncomputable section
namespace Paper13

/-- The complete finite-k main theorem for the actual graph, Hamiltonians and Lie closures. -/
theorem theorem1_actual (k : ℕ) (hk : 7 ≤ k) :
    (Gk k).Connected ∧ Fintype.card (GkVert k)=7*k ∧
    (Gk k).edgeFinset.card=9*k-1 ∧ (Gk k).maxDegree=5 ∧
    (∀ φ : Gk k ≃g Gk k, φ=1) ∧ Theorem1AlgebraClaim k ∧
    ((Module.finrank ℝ (graphNat (GkOrdinal k)) : ℚ) / Module.finrank ℝ (graphStd (GkOrdinal k))) ≥
      (2048/1985 : ℚ)^k-4/(15880 : ℚ)^k := by
  obtain ⟨hc,hv,he,hd,hr,_,_⟩ := lemma4 k hk
  exact ⟨hc,hv,he,hd,hr,theorem1_actual_algebras k hk,theorem1_actual_ratio k hk⟩
end Paper13
