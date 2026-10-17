import CounterFreeHDA.Appendix

namespace CounterFreeHDA.Appendix

def edgeMonoid : Fin 14 → BRel 3 3 := ![
  ident 3,D,K,pow D 2,comp D K,comp K D,pow K 2,comp (pow D 2) K,
  comp D (pow K 2),comp K (pow D 2),comp (comp K D) K,comp (pow K 2) D,
  pow K 3,comp D (pow K 3)]

def edgeRows : Fin 14 → BRel 3 3 := ![rel ![1,2,4],rel ![2,0,6],rel ![6,1,6],rel ![0,0,6],
  rel ![1,0,7],rel ![6,2,6],rel ![7,6,7],rel ![0,0,7],rel ![6,0,7],rel ![6,0,6],
  rel ![7,1,7],rel ![6,6,6],rel ![7,7,7],rel ![7,0,7]]
def timesD : Fin 14 → Fin 14 := ![1,3,5,3,1,9,11,3,9,9,5,11,11,9]
def timesK : Fin 14 → Fin 14 := ![2,4,6,7,8,10,12,7,13,13,6,12,12,13]
def leastExponent : Fin 14 → ℕ := ![1,2,3,1,1,1,2,1,2,1,2,1,1,1]

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

theorem exact_edge_words_rows : ∀ i, edgeMonoid i = edgeRows i := by decide
theorem exact_right_products : ∀ i, comp (edgeMonoid i) D = edgeMonoid (timesD i) ∧
    comp (edgeMonoid i) K = edgeMonoid (timesK i) := by decide

theorem exact_least_exponents : ∀ i : Fin 14,
    1 ≤ leastExponent i ∧ leastExponent i ≤ 3 ∧
    pow (edgeMonoid i) (leastExponent i) = pow (edgeMonoid i) (leastExponent i+1) ∧
    (∀ q : Fin 4, 1 ≤ q.val → q.val < leastExponent i → pow (edgeMonoid i) q.val ≠ pow (edgeMonoid i) (q.val+1)) := by decide

theorem exact_edge_exhaustion : Set.range edgeMonoid = {r | r ∈ table 1 1} := by
  have ht : Finset.univ.image edgeMonoid = table 1 1 := by decide
  ext r
  change (∃ i : Fin 14, edgeMonoid i = r) ↔ r ∈ table 1 1
  rw [← ht,Finset.mem_image]
  simp only [Finset.mem_univ,true_and]

/-- The last ×D entry is KD² with rows (6,0,6); it is distinguished
from the separate element K²D with rows (6,6,6). -/
theorem last_product_distinguishes_elements :
    comp (comp D (pow K 3)) D = comp K (pow D 2) ∧
    comp (comp D (pow K 3)) D ≠ comp (pow K 2) D := by decide

end CounterFreeHDA.Appendix
