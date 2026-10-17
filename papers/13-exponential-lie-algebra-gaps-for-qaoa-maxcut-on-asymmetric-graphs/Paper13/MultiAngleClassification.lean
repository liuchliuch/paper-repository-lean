import Paper13.YCompletion
import Paper13.CompleteDimension
noncomputable section
namespace Paper13
attribute [local instance] Classical.propDecidable

/-- Classification by generated edges, with the original graph assumptions only. -/
theorem generatedGraph_complete_of_nonbip {n : ℕ} (G : SimpleGraph (Fin n))
    (hc : G.Connected) (hnb : ¬Nonempty (G.Coloring (Fin 2))) (hncy : ¬G.IsRegularOfDegree 2) :
    generatedGraph G=⊤ := by
  have hbranch : ∃ u, 2 < G.degree u := by
    by_contra h
    push_neg at h
    exact hncy (regular_two_of_nonbip_low_degree G hc hnb h)
  obtain ⟨u,hu⟩ := hbranch
  obtain ⟨a,ha,b,hb,c,hcN,hab,hac,hbc⟩ := Finset.two_lt_card.mp hu
  have hua : G.Adj u a := by simpa using ha
  have hub : G.Adj u b := by simpa using hb
  have huc : G.Adj u c := by simpa using hcN
  let R := generatedGraph G
  have hle : G ≤ R := le_generatedGraph G
  have hRc : R.Connected := hc.mono hle
  have hRnb : ¬Nonempty (R.Coloring (Fin 2)) := by
    rintro ⟨col⟩
    exact hnb ⟨col.comp (SimpleGraph.Hom.ofLE hle)⟩
  have htriangle : ∃ x y z, R.Adj x y ∧ R.Adj x z ∧ R.Adj y z := by
    by_contra h
    have htri : ∀ x y z, R.Adj x y → R.Adj x z → R.Adj y z → False := by
      intro x y z hxy hxz hyz
      exact h ⟨x,y,z,hxy,hxz,hyz⟩
    exact hRnb (colorable_of_yClosed_star R hRc (generatedGraph_yClosed G) htri u a b c
      (hle hua) (hle hub) (hle huc) hab hac hbc)
  obtain ⟨x,y,z,hxy,hxz,hyz⟩ := htriangle
  exact complete_of_pawClosed_triangle R hRc (generatedGraph_pawClosed G) x y z hxy hxz hyz

/-- The actual multi-angle algebra of a connected non-bipartite non-cycle graph. -/
theorem graphMa_eq_complete_of_nonbip {n : ℕ} (G : SimpleGraph (Fin n))
    (hc : G.Connected) (hnb : ¬Nonempty (G.Coloring (Fin 2))) (hncy : ¬G.IsRegularOfDegree 2) :
    graphMa G=graphMa (⊤ : SimpleGraph (Fin n)) := by
  rw [←generatedGraph_complete_of_nonbip G hc hnb hncy,graphMa_generatedGraph]

/-- Exact real dimension, without importing an unproved external classification assertion. -/
theorem graphMa_dimension_of_nonbip {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    (hc : G.Connected) (hnb : ¬Nonempty (G.Coloring (Fin 2))) (hncy : ¬G.IsRegularOfDegree 2) :
    Module.finrank ℝ (graphMa G)=2^(2*n-1)-2 := by
  rw [graphMa_eq_complete_of_nonbip G hc hnb hncy,complete_graphMa_dimension n hn]

/-- The complete operator classification: skew-Hermitian, global-parity commuting, and traceless in both parity sectors. -/
theorem graphMa_eq_scSpace_of_nonbip {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    (hc : G.Connected) (hnb : ¬Nonempty (G.Coloring (Fin 2))) (hncy : ¬G.IsRegularOfDegree 2) :
    graphMa G=scSpace n := by
  apply le_antisymm
  · intro A hA
    exact mem_scSpace.mpr ⟨graphMa_skew G A hA,graphMa_comm_bitFlip G A hA,
      graphMa_traceless G A hA,graphMa_tracelessFlip hn G A hA⟩
  · intro A hA
    obtain ⟨hsk,hco,htr,hfl⟩ := mem_scSpace.mp hA
    have hm := mem_admissible_span A hsk hco htr hfl
    rw [graphMa_eq_complete_of_nonbip G hc hnb hncy,complete_graphMa_eq_span n hn]
    exact hm
end Paper13
