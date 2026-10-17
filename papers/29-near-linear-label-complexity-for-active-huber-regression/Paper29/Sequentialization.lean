import Paper29.SeedCompression

noncomputable section
open scoped Classical ENNReal
open MeasureTheory
namespace Paper29.QueryModel

/-- Values in a finite observed history, with zero outside its queried set. -/
def historyLabels {n : ℕ} (h : History n) (i : Fin n) : ℝ :=
  if hi : ∃ z ∈ h,z.1=i then (Classical.choose hi).2 else 0

theorem historyLabels_eq {n : ℕ} (h : History n) (b : Fin n → ℝ)
    (hagrees : ∀ z ∈ h,z.2=b z.1) {i : Fin n} (hi : i∈h.map Prod.fst) : historyLabels h i=b i := by
  have hex : ∃ z∈h,z.1=i := by simpa only [List.mem_map] using hi
  rw [historyLabels,dif_pos hex]
  have hz := Classical.choose_spec hex
  rw [hagrees _ hz.1,hz.2]

def remaining {Ω : Type} {n d : ℕ} (a : NonadaptiveProcedure Ω n d) (ω : Ω) (h : History n) : Finset (Fin n) :=
  a.queried ω \ (h.map Prod.fst).toFinset

def nextFresh {n : ℕ} (s : Finset (Fin n)) : Fin n ⊕ Unit :=
  if hs : s.Nonempty then .inl hs.choose else .inr ()

def sequentialPolicy {Ω : Type} {n d : ℕ} (a : NonadaptiveProcedure Ω n d) : Policy Ω n d := fun ω h =>
  match nextFresh (remaining a ω h) with
  | .inl i => .query i
  | .inr _ => .output (a.answer ω (historyLabels h))

theorem sequentialPolicy_fresh {Ω : Type} {n d : ℕ} (a : NonadaptiveProcedure Ω n d) :
    Fresh (sequentialPolicy a) := by
  intro ω h i hi
  by_cases hs : (remaining a ω h).Nonempty
  · simp only [sequentialPolicy,nextFresh,dif_pos hs,Decision.query.injEq] at hi
    subst i
    exact fun hmem => (Finset.mem_sdiff.mp hs.choose_spec).2 (List.mem_toFinset.mpr hmem)
  · simp only [sequentialPolicy,nextFresh,dif_neg hs,Decision.noConfusion] at hi
    cases hi

theorem sequential_execute {Ω : Type} {n d : ℕ} (a : NonadaptiveProcedure Ω n d) (ω : Ω)
    (b : Fin n → ℝ) (k : ℕ) (h : History n)
    (hsub : (h.map Prod.fst).toFinset ⊆ a.queried ω)
    (hagrees : ∀ z∈h,z.2=b z.1) (hcard : (remaining a ω h).card ≤ k) :
    ∃ g, execute (sequentialPolicy a) ω b (k+1) h = some (a.answer ω b,g) ∧
      (g.map Prod.fst).toFinset=a.queried ω := by
  induction k generalizing h with
  | zero =>
    have hrem : remaining a ω h=∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    have hset : (h.map Prod.fst).toFinset=a.queried ω :=
      le_antisymm hsub (Finset.sdiff_eq_empty_iff_subset.mp hrem)
    have hout : a.answer ω (historyLabels h)=a.answer ω b := by
      unfold NonadaptiveProcedure.answer
      congr 1
      funext i
      exact historyLabels_eq h b hagrees (List.mem_toFinset.mp (hset.symm ▸ i.2))
    exact ⟨h,by simp [execute,sequentialPolicy,nextFresh,hrem,hout],hset⟩
  | succ k ih =>
    by_cases hs : (remaining a ω h).Nonempty
    · let i := hs.choose
      have himem : i∈remaining a ω h := hs.choose_spec
      have hiS := (Finset.mem_sdiff.mp himem).1
      have hiH := (Finset.mem_sdiff.mp himem).2
      have hsub' : (((h++[(i,b i)]).map Prod.fst).toFinset) ⊆ a.queried ω := by
        simpa only [List.map_append,List.map_cons,List.map_nil,List.toFinset_append,
          List.toFinset_cons,List.toFinset_nil,Finset.insert_empty,Finset.union_singleton] using Finset.insert_subset hiS hsub
      have hagrees' : ∀ z∈h++[(i,b i)],z.2=b z.1 := by
        intro z hz
        rcases List.mem_append.mp hz with hz|hz
        · exact hagrees z hz
        · have he : z=(i,b i) := List.mem_singleton.mp hz
          simpa only [he]
      have hrem : remaining a ω (h++[(i,b i)])=(remaining a ω h).erase i := by
        simp only [remaining,List.map_append,List.map_cons,List.map_nil,List.toFinset_append,
          List.toFinset_cons,List.toFinset_nil,Finset.insert_empty,Finset.union_singleton,Finset.sdiff_insert]
      have hcard' : (remaining a ω (h++[(i,b i)])).card ≤ k := by
        rw [hrem]
        have hh := Finset.card_erase_add_one himem
        omega
      obtain ⟨g,hg,hgset⟩ := ih (h++[(i,b i)]) hsub' hagrees' hcard'
      exact ⟨g,by simpa only [execute,sequentialPolicy,nextFresh,dif_pos hs] using hg,hgset⟩
    · have hrem : remaining a ω h=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      have hset : (h.map Prod.fst).toFinset=a.queried ω :=
        le_antisymm hsub (Finset.sdiff_eq_empty_iff_subset.mp hrem)
      have hout : a.answer ω (historyLabels h)=a.answer ω b := by
        unfold NonadaptiveProcedure.answer
        congr 1
        funext i
        exact historyLabels_eq h b hagrees (List.mem_toFinset.mp (hset.symm ▸ i.2))
      exact ⟨h,by simp [execute,sequentialPolicy,nextFresh,dif_neg hs,hout],hset⟩

theorem sequential_run {Ω : Type} {n d : ℕ} (a : NonadaptiveProcedure Ω n d) (ω : Ω) (b : Fin n → ℝ) :
    ∃ g, run (sequentialPolicy a) ω b=some (a.answer ω b,g) ∧ (g.map Prod.fst).toFinset=a.queried ω := by
  exact sequential_execute a ω b n [] (by simp) (by simp) (by simpa [remaining] using Finset.card_le_univ (a.queried ω))

theorem sequential_queryCount {Ω : Type} {n d : ℕ} (a : NonadaptiveProcedure Ω n d) (ω : Ω) (b : Fin n → ℝ) :
    queryCount (sequentialPolicy a) ω b = ((a.queried ω).card : ℝ≥0∞) := by
  obtain ⟨g,hg,hs⟩ := sequential_run a ω b
  simp only [queryCount,hg,hs]

theorem sequential_success_iff {Ω : Type} {n d : ℕ} (a : NonadaptiveProcedure Ω n d)
    (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) (ε : ℝ) (ω : Ω) :
    Successful (sequentialPolicy a) A b ε ω ↔ ∀ y,Real.sqrt (objective A b (a.answer ω b)) ≤
      (1+ε)*Real.sqrt (objective A b y) := by
  obtain ⟨g,hg,_⟩ := sequential_run a ω b
  unfold Successful
  simp only [hg,Option.some.injEq,Prod.mk.injEq]
  constructor
  · rintro ⟨x,h,he,hgood⟩; simpa only [he.1] using hgood
  · intro hh; exact ⟨a.answer ω b,g,⟨rfl,rfl⟩,hh⟩

end Paper29.QueryModel
