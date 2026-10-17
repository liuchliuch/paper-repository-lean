import Paper13.GraphOperators
import Paper13.PortFactor
import Paper13.Certificate
import Paper13.Amplification
import Paper13.MainCore
import Paper13.InvariantGap
import Paper13.PortedBounds

/-! # Integrated local and graph results

The full actual algebra, ratio and invariant-component conclusions are integrated
in `Paper13.FullResults`, including the reconstructed multi-angle classification.
-/
noncomputable section
namespace Paper13

/-- The seven-qubit standard Lie algebra preserves the explicit local sector. -/
theorem local_standard_preserves_projector :
    ∀ A ∈ gStd (Xv (0 : Fin 7) + Xv 1 + Xv 2 + Xv 3 + Xv 4 + Xv 5 + Xv 6) Hzz_H,
      A * localP = localP * A := by
  apply gStd_commutes
  · exact localP_comm_HX.symm
  · rw [Hzz_H_mul_localP, localP_mul_Hzz_H]

/-- The complete graph-construction portion used by the main theorem. -/
theorem graph_family_properties (k : ℕ) (hk : 7 ≤ k) :
    (Gk k).Connected ∧ Fintype.card (GkVert k) = 7*k ∧
    (Gk k).edgeFinset.card = 9*k-1 ∧ (Gk k).maxDegree = 5 ∧
    (∀ φ : Gk k ≃g Gk k, φ = 1) ∧
    ¬ Nonempty ((Gk k).Coloring (Fin 2)) ∧ ¬ (Gk k).IsRegularOfDegree 2 := lemma4 k hk
end Paper13
