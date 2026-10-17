import Paper13.GeneratedEdges
noncomputable section
namespace Paper13
attribute [local instance] Classical.propDecidable

/-- A connected graph closed under paw completion and containing a triangle is complete. -/
theorem complete_of_pawClosed_triangle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hc : G.Connected) (hp : PawClosed G)
    (a b c : V) (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) : G = ⊤ := by
  obtain ⟨s,hs⟩ := G.maximumClique_exists
  have ht : G.IsClique (({a,b,c} : Finset V) : Set V) := by
    intro u hu v hv hne
    simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
      simp_all only [ne_eq,not_true_eq_false,SimpleGraph.adj_comm]
  have hcard : 3 ≤ s.card := by
    have h := hs.maximum {a,b,c} ht
    simpa [hab.ne,hac.ne,hbc.ne] using h
  have hclosed : ∀ u ∈ s, ∀ v, G.Adj u v → v ∈ s := by
    intro u hu v huv
    by_contra hv
    have herase : 1 < (s.erase u).card := by
      rw [Finset.card_erase_of_mem hu]
      omega
    obtain ⟨p,hpS,q,hqS,hpq⟩ := Finset.one_lt_card.mp herase
    obtain ⟨hpu,hpS⟩ := Finset.mem_erase.mp hpS
    obtain ⟨hqu,hqS⟩ := Finset.mem_erase.mp hqS
    have hnv : ∀ x ∈ s, x ≠ v := by intro x hx h; exact hv (h ▸ hx)
    have hpqE := hs.isClique hpS hqS hpq
    have hpuE := hs.isClique hpS hu hpu
    have hquE := hs.isClique hqS hu hqu
    have hvpair := hp p q u v hpq hpu (hnv p hpS) hqu (hnv q hqS) huv.ne hpqE hpuE hquE huv
    have hvs : ∀ w ∈ s, G.Adj v w := by
      intro w hw
      by_cases hwu : w=u
      · subst w; exact G.symm huv
      by_cases hwp : w=p
      · subst w; exact G.symm hvpair.1
      have hwuE := hs.isClique hu hw (Ne.symm hwu)
      have hwv := hnv w hw
      have hr := hp v p u w (hnv p hpS).symm huv.ne.symm hwv.symm hpu (Ne.symm hwp) (Ne.symm hwu)
        (G.symm hvpair.1) (G.symm huv) hpuE hwuE
      exact hr.1
    have hi : G.IsClique ((insert v s : Finset V) : Set V) := by
      rw [Finset.coe_insert]
      exact hs.isClique.insert (fun w hw _ => hvs w hw)
    have hmax := hs.maximum (insert v s) hi
    rw [Finset.card_insert_of_notMem hv] at hmax
    omega
  obtain ⟨u,hu⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  have hwalk : ∀ {x y : V}, G.Walk x y → x ∈ s → y ∈ s := by
    intro x y p
    induction p with
    | nil => exact id
    | @cons x y z hxy p ih => exact fun hx => ih (hclosed x hx y hxy)
  have hall : ∀ v, v ∈ s := by
    intro v
    exact (hc u v).elim (fun p => hwalk p hu)
  ext x y
  exact ⟨fun h => h.ne, fun h => hs.isClique (hall x) (hall y) h⟩

lemma generatedGraph_eq_top_of_triangle {n : ℕ} (G : SimpleGraph (Fin n))
    (hc : G.Connected) (a b c : Fin n) (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    generatedGraph G = ⊤ := by
  apply complete_of_pawClosed_triangle (generatedGraph G)
    (hc.mono (le_generatedGraph G)) (generatedGraph_pawClosed G) a b c
  · exact le_generatedGraph G hab
  · exact le_generatedGraph G hac
  · exact le_generatedGraph G hbc

/-- All ZZ controls of the complete graph are genuinely generated from a connected graph with a triangle. -/
theorem graphMa_eq_complete_of_triangle {n : ℕ} (G : SimpleGraph (Fin n))
    (hc : G.Connected) (a b c : Fin n) (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    graphMa G = graphMa (⊤ : SimpleGraph (Fin n)) := by
  rw [← generatedGraph_eq_top_of_triangle G hc a b c hab hac hbc,graphMa_generatedGraph]
end Paper13
