import Paper13.GeneratedEdges
import Paper13.YCertificate
import Paper13.LowDegreeBipartite
import Mathlib.Order.Preorder.Finite
noncomputable section
namespace Paper13
attribute [local instance] Classical.propDecidable

def fiveEmbedding {V : Type*} (a b c d e : V)
    (hab : a≠b) (hac : a≠c) (had : a≠d) (hae : a≠e) (hbc : b≠c)
    (hbd : b≠d) (hbe : b≠e) (hcd : c≠d) (hce : c≠e) (hde : d≠e) : Fin 5 ↪ V where
  toFun := ![a,b,c,d,e]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def YClosed {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c d e, a≠b → a≠c → a≠d → a≠e → b≠c → b≠d → b≠e → c≠d → c≠e → d≠e →
    G.Adj a c → G.Adj b c → G.Adj c d → G.Adj d e → G.Adj a e ∧ G.Adj b e

lemma generatedGraph_yClosed {n : ℕ} (G : SimpleGraph (Fin n)) : YClosed (generatedGraph G) := by
  intro a b c d e hab hac had hae hbc hbd hbe hcd hce hde hacE hbcE hcdE hdeE
  let f := fiveEmbedding a b c d e hab hac had hae hbc hbd hbe hcd hce hde
  have hf : ∀ i j, yGraph.Adj i j → (generatedGraph G).Adj (f i) (f j) := by
    intro i j h
    fin_cases i <;> fin_cases j
    all_goals first
      | exact hacE | exact hbcE | exact hcdE | exact hdeE
      | exact (generatedGraph G).symm hacE | exact (generatedGraph G).symm hbcE
      | exact (generatedGraph G).symm hcdE | exact (generatedGraph G).symm hdeE
      | exact False.elim ((by dsimp [yGraph]; decide : ¬ yGraph.Adj _ _) h)
  have h0 := registerLift_lie f yGraph (generatedGraph G) hf _ y_missing_edges.1
  have h1 := registerLift_lie f yGraph (generatedGraph G) hf _ y_missing_edges.2
  rw [map_smul,registerLift_ZZ,graphMa_generatedGraph] at h0 h1
  exact ⟨⟨hae,h0⟩,⟨hbe,h1⟩⟩

lemma finset_exists_third {V : Type*} [DecidableEq V] (s : Finset V) (hs : 3 ≤ s.card) (a b : V) :
    ∃ c ∈ s, c≠a ∧ c≠b := by
  by_contra h
  push_neg at h
  have hsub : s ⊆ {a,b} := by
    intro c hc
    by_cases ha : c=a
    · simp [ha]
    · simp [h c hc ha]
  have := Finset.card_le_card hsub
  have hp : ({a,b} : Finset V).card ≤ 2 := by simp [Finset.card_le_two]
  omega

/-- Triangle-free Y-closed graphs with a branching vertex are bipartite.
The proof extends a maximal complete bipartite pair using the local Y rule. -/
theorem colorable_of_yClosed_star {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hc : G.Connected) (hy : YClosed G)
    (htri : ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c → False)
    (u a b c : V) (hua : G.Adj u a) (hub : G.Adj u b) (huc : G.Adj u c)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) : Nonempty (G.Coloring (Fin 2)) := by
  let P : Finset V × Finset V → Prop := fun S =>
    S.1.Nonempty ∧ 3 ≤ S.2.card ∧ Disjoint S.1 S.2 ∧ ∀ x ∈ S.1, ∀ y ∈ S.2, G.Adj x y
  have hinit : P ({u},{a,b,c}) := by
    refine ⟨by simp,by simp [hab,hac,hbc],?_,?_⟩
    · simp [Ne.symm hua.ne,Ne.symm hub.ne,Ne.symm huc.ne]
    · intro x hx y hy
      simp only [Finset.mem_singleton] at hx
      subst x
      simp only [Finset.mem_insert,Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl <;> assumption
  obtain ⟨S,hbase,hmax⟩ := Finite.exists_le_maximal hinit
  obtain ⟨hA,hB,hdis,hcross⟩ := hmax.1
  let A := S.1
  let B := S.2
  change 3 ≤ B.card at hB
  have hne : ∀ x ∈ A, ∀ y ∈ B, x≠y := by
    intro x hx y hy he
    exact Finset.disjoint_left.mp hdis hx (he ▸ hy)
  have hout : ∀ v, v ∉ A ∪ B → (∀ x ∈ A ∪ B, v≠x) := by
    intro v hv x hx he; exact hv (he ▸ hx)
  have extendB : ∀ x ∈ A, ∀ v, v ∉ A ∪ B → G.Adj x v → v ∈ B := by
    intro x hx v hv hxv
    obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
    have hvne := hout v hv
    have hnew : ∀ w ∈ A, G.Adj w v := by
      intro w hw
      by_cases hwx : w=x
      · subst w; exact hxv
      have hh := hy v p x q w
        (hvne p (Finset.mem_union_right A hp)) (hvne x (Finset.mem_union_left B hx))
        (hvne q (Finset.mem_union_right A hq)) (hvne w (Finset.mem_union_left B hw))
        (Ne.symm (hne x hx p hp)) hpq (Ne.symm (hne w hw p hp)) (hne x hx q hq)
        (Ne.symm hwx) (Ne.symm (hne w hw q hq))
        (G.symm hxv) (G.symm (hcross x hx p hp)) (hcross x hx q hq) (G.symm (hcross w hw q hq))
      exact G.symm hh.1
    have hvA : v ∉ A := fun h => hv (Finset.mem_union_left B h)
    have hP : P (A,insert v B) := by
      refine ⟨hA,le_trans hB (Finset.card_le_card (Finset.subset_insert _ _)),?_,?_⟩
      · exact Finset.disjoint_left.mpr (by intro x hx hxi; rcases Finset.mem_insert.mp hxi with rfl | h; exact hvA hx; exact Finset.disjoint_left.mp hdis hx h)
      · intro w hw y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hnew w hw
        · exact hcross w hw y hy
    have hm := hmax.2 hP (show S ≤ (A,insert v B) from ⟨le_refl _,Finset.subset_insert _ _⟩)
    exact hm.2 (Finset.mem_insert_self _ _)
  have extendA : ∀ y ∈ B, ∀ v, v ∉ A ∪ B → G.Adj y v → v ∈ A := by
    intro y hyB v hv hyv
    obtain ⟨x,hx⟩ := hA
    have hvne := hout v hv
    have hnew : ∀ w ∈ B, G.Adj v w := by
      intro w hw
      by_cases hwy : w=y
      · subst w; exact G.symm hyv
      obtain ⟨q,hq,hqy,hqw⟩ := finset_exists_third B hB y w
      have hh := hy w q x y v
        (Ne.symm hqw) (Ne.symm (hne x hx w hw)) hwy (Ne.symm (hvne w (Finset.mem_union_right A hw)))
        (Ne.symm (hne x hx q hq)) hqy (Ne.symm (hvne q (Finset.mem_union_right A hq)))
        (hne x hx y hyB) (Ne.symm (hvne x (Finset.mem_union_left B hx)))
        (Ne.symm (hvne y (Finset.mem_union_right A hyB)))
        (G.symm (hcross x hx w hw)) (G.symm (hcross x hx q hq)) (hcross x hx y hyB) hyv
      exact G.symm hh.1
    have hvB : v ∉ B := fun h => hv (Finset.mem_union_right A h)
    have hP : P (insert v A,B) := by
      refine ⟨Finset.insert_nonempty _ _,hB,?_,?_⟩
      · exact Finset.disjoint_left.mpr (by intro x hx hxb; rcases Finset.mem_insert.mp hx with rfl | h; exact hvB hxb; exact Finset.disjoint_left.mp hdis h hxb)
      · intro w hw y hy
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hnew y hy
        · exact hcross w hw y hy
    have hm := hmax.2 hP (show S ≤ (insert v A,B) from ⟨Finset.subset_insert _ _,le_refl _⟩)
    exact hm.1 (Finset.mem_insert_self _ _)
  have hclosed : ∀ x ∈ A ∪ B, ∀ v, G.Adj x v → v ∈ A ∪ B := by
    intro x hx v hxv
    by_contra hv
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hv (Finset.mem_union_right A (extendB x hx v hv hxv))
    · exact hv (Finset.mem_union_left B (extendA x hx v hv hxv))
  obtain ⟨x,hx⟩ := hA
  have hall : ∀ v, v ∈ A ∪ B := by
    have hwalk : ∀ {s t : V}, G.Walk s t → s ∈ A ∪ B → t ∈ A ∪ B := by
      intro s t p
      induction p with
      | nil => exact id
      | @cons s t z hst p ih => exact fun hs => ih (hclosed s hs t hst)
    intro v
    exact (hc x v).elim (fun p => hwalk p (Finset.mem_union_left B hx))
  refine ⟨⟨fun v => if v ∈ A then 0 else 1,?_⟩⟩
  intro v w hvw
  by_cases hv : v ∈ A <;> by_cases hw : w ∈ A
  · obtain ⟨y,hyB⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
    exact False.elim (htri v w y hvw (hcross v hv y hyB) (hcross w hw y hyB))
  · change (if v ∈ A then (0 : Fin 2) else 1) ≠ (if w ∈ A then 0 else 1)
    rw [if_pos hv,if_neg hw]; decide
  · change (if v ∈ A then (0 : Fin 2) else 1) ≠ (if w ∈ A then 0 else 1)
    rw [if_neg hv,if_pos hw]; decide
  · have hvB := (Finset.mem_union.mp (hall v)).resolve_left hv
    have hwB := (Finset.mem_union.mp (hall w)).resolve_left hw
    exact False.elim (htri v w x hvw (G.symm (hcross x hx v hvB)) (G.symm (hcross x hx w hwB)))
end Paper13
