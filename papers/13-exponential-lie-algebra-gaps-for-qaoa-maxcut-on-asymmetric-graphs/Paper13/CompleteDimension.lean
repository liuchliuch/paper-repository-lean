import Paper13.MultiAngleConstraints
import Paper13.CompletePauliGeneration
import Paper13.PauliCount
import Paper13.PawCompletion
noncomputable section
namespace Paper13
attribute [local instance] Classical.propDecidable

def admissibleSpan (n : ℕ) : Submodule ℝ (Op n) :=
  Submodule.span ℝ (Set.range (fun w : {w : Fin n → Fin 4 // AdmissiblePauli w} => skewPauliWord w.val))

lemma graphMa_le_admissibleSpan {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) : graphMa G ≤ admissibleSpan n := by
  intro A hA
  exact mem_admissible_span A (graphMa_skew G A hA) (graphMa_comm_bitFlip G A hA)
    (graphMa_traceless G A hA) (graphMa_tracelessFlip hn G A hA)

lemma complete_graphMa_eq_span (n : ℕ) (hn : 2 ≤ n) : graphMa (⊤ : SimpleGraph (Fin n))=admissibleSpan n := by
  apply le_antisymm (graphMa_le_admissibleSpan hn ⊤)
  apply Submodule.span_le.mpr
  rintro A ⟨w,rfl⟩
  exact complete_generates_admissible n w.val w.property

lemma admissibleSpan_finrank (n : ℕ) (hn : 0 < n) : Module.finrank ℝ (admissibleSpan n)=2^(2*n-1)-2 := by
  have hi : LinearIndependent ℝ (fun w : {w : Fin n → Fin 4 // AdmissiblePauli w} => skewPauliWord w.val) := by
    simpa only [Function.comp_def] using (skewPauliWords_independent n).comp
      (fun w : {w : Fin n → Fin 4 // AdmissiblePauli w} => w.val) Subtype.val_injective
  rw [admissibleSpan,finrank_span_eq_card hi,admissiblePauli_card n hn]

/-- Exact real dimension, derived from actual generation, trace constraints and Pauli independence. -/
theorem complete_graphMa_dimension (n : ℕ) (hn : 2 ≤ n) :
    Module.finrank ℝ (graphMa (⊤ : SimpleGraph (Fin n)))=2^(2*n-1)-2 := by
  rw [complete_graphMa_eq_span n hn,admissibleSpan_finrank n (by omega)]

theorem graphMa_dimension_of_triangle {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    (hc : G.Connected) (a b c : Fin n) (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    Module.finrank ℝ (graphMa G)=2^(2*n-1)-2 := by
  rw [graphMa_eq_complete_of_triangle G hc a b c hab hac hbc,complete_graphMa_dimension n hn]
end Paper13
