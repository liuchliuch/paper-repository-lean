import Paper13.PawCertificate
import Mathlib.Combinatorics.SimpleGraph.Clique
noncomputable section
namespace Paper13
open Matrix
attribute [local instance] Classical.propDecidable

lemma graphMa_mono {n : ℕ} {G H : SimpleGraph (Fin n)} (h : G ≤ H) : graphMa G ≤ graphMa H := by
  apply lieClosure_le
  · rintro A (⟨v,rfl⟩ | ⟨e,he,rfl⟩)
    · exact subset_lieClosure (Or.inl ⟨v,rfl⟩)
    · exact graphMa_ZZ H _ _ (h ((Finset.mem_filter.mp he).2.2))
  · exact isLieSub_lieClosure _

/-- An edge is present exactly when its actual ZZ control is already generated. -/
def generatedGraph {n : ℕ} (G : SimpleGraph (Fin n)) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ Complex.I • ZZ u v ∈ graphMa G
  symm := by
    intro u v h
    refine ⟨h.1.symm,?_⟩
    simpa only [ZZ,(Zv_commute v u).eq] using h.2
  loopless := by intro v h; exact h.1 rfl

lemma le_generatedGraph {n : ℕ} (G : SimpleGraph (Fin n)) : G ≤ generatedGraph G :=
  fun u v h => ⟨h.ne,graphMa_ZZ G u v h⟩

lemma graphMa_generatedGraph {n : ℕ} (G : SimpleGraph (Fin n)) : graphMa (generatedGraph G)=graphMa G := by
  apply le_antisymm
  · apply lieClosure_le
    · rintro A (⟨v,rfl⟩ | ⟨e,he,rfl⟩)
      · exact subset_lieClosure (Or.inl ⟨v,rfl⟩)
      · exact ((Finset.mem_filter.mp he).2.2).2
    · exact isLieSub_lieClosure _
  · exact graphMa_mono (le_generatedGraph G)

def fourEmbedding {V : Type*} (a b c d : V)
    (hab : a≠b) (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (hcd : c≠d) : Fin 4 ↪ V where
  toFun := ![a,b,c,d]
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- The local paw rule, expressed without any dimension or classification assumption. -/
def PawClosed {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c d, a≠b → a≠c → a≠d → b≠c → b≠d → c≠d →
    G.Adj a b → G.Adj a c → G.Adj b c → G.Adj c d → G.Adj a d ∧ G.Adj b d

lemma generatedGraph_pawClosed {n : ℕ} (G : SimpleGraph (Fin n)) : PawClosed (generatedGraph G) := by
  intro a b c d hab hac had hbc hbd hcd habE hacE hbcE hcdE
  let f := fourEmbedding a b c d hab hac had hbc hbd hcd
  have hf : ∀ i j, pawGraph.Adj i j → (generatedGraph G).Adj (f i) (f j) := by
    intro i j h
    fin_cases i <;> fin_cases j
    all_goals first
      | exact habE | exact hacE | exact hbcE | exact hcdE
      | exact (generatedGraph G).symm habE | exact (generatedGraph G).symm hacE
      | exact (generatedGraph G).symm hbcE | exact (generatedGraph G).symm hcdE
      | exact False.elim ((by dsimp [pawGraph]; decide : ¬ pawGraph.Adj _ _) h)
  have h0 := registerLift_lie f pawGraph (generatedGraph G) hf _ paw_missing_edges.1
  have h1 := registerLift_lie f pawGraph (generatedGraph G) hf _ paw_missing_edges.2
  rw [map_smul,registerLift_ZZ,graphMa_generatedGraph] at h0 h1
  exact ⟨⟨had,h0⟩,⟨hbd,h1⟩⟩
end Paper13
