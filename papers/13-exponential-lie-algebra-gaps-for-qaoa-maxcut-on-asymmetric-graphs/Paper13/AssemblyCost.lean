import Paper13.AssemblyBasis
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Pure graph port assembly, with no operator or dimension hypothesis. -/
def assembleGraph {k h : ℕ} (K : SimpleGraph (Fin h)) (p : Fin h) (B : SimpleGraph (Fin k)) :
    SimpleGraph (Fin k × Fin h) where
  Adj x y := (x.1=y.1 ∧ K.Adj x.2 y.2) ∨ (x.2=p ∧ y.2=p ∧ B.Adj x.1 y.1)
  symm := by
    rintro x y (h | h)
    · exact Or.inl ⟨h.1.symm,K.symm h.2⟩
    · exact Or.inr ⟨h.2.1,h.1,B.symm h.2.2⟩
  loopless := by
    rintro x (h | h)
    · exact K.loopless _ h.2
    · exact B.loopless _ h.2.2

def assembleOrdinal {k h : ℕ} (K : SimpleGraph (Fin h)) (p : Fin h) (B : SimpleGraph (Fin k)) :
    SimpleGraph (Fin (k*h)) := (assembleGraph K p B).comap finProdFinEquiv.symm

lemma finProd_lt_same_copy {k h : ℕ} (v : Fin k) (u t : Fin h) :
    finProdFinEquiv (v,u) < finProdFinEquiv (v,t) ↔ u < t := by
  change u.val+h*v.val < t.val+h*v.val ↔ u.val < t.val
  omega

lemma finProd_lt_same_position {k h : ℕ} (v w : Fin k) (u : Fin h) :
    finProdFinEquiv (v,u) < finProdFinEquiv (w,u) ↔ v < w := by
  change u.val+h*v.val < u.val+h*w.val ↔ v.val < w.val
  rw [Nat.add_lt_add_iff_left,Nat.mul_lt_mul_left (Nat.zero_lt_of_lt u.isLt)]

lemma assemble_edge_iff {k h : ℕ} (K : SimpleGraph (Fin h)) (p : Fin h) (B : SimpleGraph (Fin k))
    (v w : Fin k) (u t : Fin h) :
    (finProdFinEquiv (v,u) < finProdFinEquiv (w,t) ∧
      (assembleOrdinal K p B).Adj (finProdFinEquiv (v,u)) (finProdFinEquiv (w,t))) ↔
    (v=w ∧ u<t ∧ K.Adj u t) ∨ (u=p ∧ t=p ∧ v<w ∧ B.Adj v w) := by
  have hadj : (assembleOrdinal K p B).Adj (finProdFinEquiv (v,u)) (finProdFinEquiv (w,t)) ↔
      ((v=w ∧ K.Adj u t) ∨ (u=p ∧ t=p ∧ B.Adj v w)) := by
    change (assembleGraph K p B).Adj (finProdFinEquiv.symm (finProdFinEquiv (v,u)))
      (finProdFinEquiv.symm (finProdFinEquiv (w,t))) ↔ _
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
    rfl
  rw [hadj]
  constructor
  · rintro ⟨hlt,h | h⟩
    · rcases h with ⟨rfl,ha⟩
      exact Or.inl ⟨rfl,(finProd_lt_same_copy v u t).mp hlt,ha⟩
    · rcases h with ⟨hu,ht,ha⟩
      have hp : finProdFinEquiv (v,p) < finProdFinEquiv (w,p) := by simpa only [hu,ht] using hlt
      exact Or.inr ⟨hu,ht,(finProd_lt_same_position v w p).mp hp,ha⟩
  · rintro (⟨hvw,hlt,ha⟩ | ⟨hu,ht,hlt,ha⟩)
    · subst w
      exact ⟨(finProd_lt_same_copy v u t).mpr hlt,Or.inl ⟨rfl,ha⟩⟩
    · refine ⟨?_,Or.inr ⟨hu,ht,ha⟩⟩
      simpa only [hu,ht] using (finProd_lt_same_position v w p).mpr hlt

lemma graphCost_as_sum {n : ℕ} (G : SimpleGraph (Fin n)) :
    graphCost G = ∑ e : Fin n × Fin n, if e.1<e.2 ∧ G.Adj e.1 e.2 then ZZ e.1 e.2 else 0 := by
  classical
  simp [graphCost,graphEdges,Finset.sum_filter]

/-- Exact decomposition of the actual assembled graph cost into its local terms and port edges. -/
theorem assemblyReindex_cost {k h : ℕ} (K : SimpleGraph (Fin h)) (p : Fin h) (B : SimpleGraph (Fin k)) :
    assemblyReindex k h (graphCost (assembleOrdinal K p B)) =
      (∑ v : Fin k, liftSite v (graphCost K)) +
      ∑ e ∈ graphEdges B, liftSite e.1 (Zv p) * liftSite e.2 (Zv p) := by
  classical
  rw [graphCost_as_sum,map_sum]
  have hreindex := (Equiv.prodCongr (finProdFinEquiv : Fin k × Fin h ≃ Fin (k*h))
    finProdFinEquiv).sum_comp (fun e : Fin (k*h) × Fin (k*h) =>
      assemblyReindex k h (if e.1<e.2 ∧ (assembleOrdinal K p B).Adj e.1 e.2 then ZZ e.1 e.2 else 0))
  rw [← hreindex]
  simp only [Fintype.sum_prod_type,Equiv.prodCongr_apply,Prod.map,assemble_edge_iff,apply_ite,map_zero,assemblyReindex_ZZ]
  have hsplit (v w : Fin k) (u t : Fin h) :
      (if (v=w ∧ u<t ∧ K.Adj u t) ∨ (u=p ∧ t=p ∧ v<w ∧ B.Adj v w)
        then liftSite v (Zv u) * liftSite w (Zv t) else 0) =
      (if v=w ∧ u<t ∧ K.Adj u t then liftSite v (Zv u) * liftSite w (Zv t) else 0) +
      (if u=p ∧ t=p ∧ v<w ∧ B.Adj v w then liftSite v (Zv u) * liftSite w (Zv t) else 0) := by
    by_cases h1 : v=w ∧ u<t ∧ K.Adj u t
    · have hn : ¬ (u=p ∧ t=p ∧ v<w ∧ B.Adj v w) := by rintro ⟨_,_,hl,_⟩; omega
      simp [h1,hn]
    · simp [h1]
  simp only [hsplit,Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.sum_comm]
    have he (w : Fin k) :
        (∑ u : Fin h, ∑ t : Fin h, if v=w ∧ u<t ∧ K.Adj u t then liftSite v (Zv u)*liftSite w (Zv t) else 0) =
        if v=w then liftSite v (graphCost K) else 0 := by
      by_cases hw : v=w
      · subst w
        simp only [true_and]
        rw [graphCost_as_sum,liftSite_sum]
        simp only [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro t ht
        split_ifs <;> simp [← liftSite_mul,ZZ,liftSite_zero]
      · simp [hw]
    simp only [he]
    simp
  · simp only [graphEdges,Finset.sum_filter,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w hw
    rw [Finset.sum_comm]
    simp only [ite_and]
    simp
end Paper13
