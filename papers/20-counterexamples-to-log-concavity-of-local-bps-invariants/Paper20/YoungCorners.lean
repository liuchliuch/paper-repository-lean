import Paper20.PartitionFinite

namespace Paper20.YoungCorners
open Finset
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- An actual outer corner, expressed by its two immediate predecessors. -/
def Addable (μ : YoungDiagram) (c : ℕ × ℕ) : Prop :=
  c ∉ μ ∧ (c.1=0 ∨ (c.1-1,c.2) ∈ μ) ∧ (c.2=0 ∨ (c.1,c.2-1) ∈ μ)

/-- An actual removable corner, with neither immediate successor present. -/
def Removable (μ : YoungDiagram) (c : ℕ × ℕ) : Prop :=
  c ∈ μ ∧ (c.1+1,c.2) ∉ μ ∧ (c.1,c.2+1) ∉ μ

lemma addable_lower (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Addable μ c)
    (a : ℕ × ℕ) (ha : a ≤ c) (hne : a ≠ c) : a ∈ μ := by
  obtain ⟨hn,hu,hl⟩ := hc
  have hi : a.1 ≤ c.1 := ha.1
  have hj : a.2 ≤ c.2 := ha.2
  by_cases he : a.1=c.1
  · have hj' : a.2 < c.2 := by
      by_contra hn'
      apply hne
      exact Prod.ext he (by omega)
    rcases hl with hz | hl
    · omega
    · exact μ.up_left_mem hi (by omega) hl
  · rcases hu with hz | hu
    · omega
    · exact μ.up_left_mem (by omega) hj hu

lemma removable_maximal (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Removable μ c)
    (a : ℕ × ℕ) (ha : a ∈ μ) (hle : c ≤ a) : a=c := by
  obtain ⟨hc,hd,hr⟩ := hc
  have hi : c.1 ≤ a.1 := hle.1
  have hj : c.2 ≤ a.2 := hle.2
  have hei : a.1=c.1 := by
    by_contra hn
    apply hd
    exact μ.up_left_mem (by omega) hj ha
  have hej : a.2=c.2 := by
    by_contra hn
    apply hr
    exact μ.up_left_mem hi (by omega) ha
  exact Prod.ext hei hej

/-- Insert a proved actual outer corner; lower closure is derived. -/
def insert (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Addable μ c) : YoungDiagram where
  cells := Insert.insert c μ.cells
  isLowerSet := by
    intro b a hab hb
    rcases Finset.mem_insert.mp hb with he | hb
    · subst b
      by_cases he : a=c
      · subst a
        exact Finset.mem_insert_self c μ.cells
      · exact Finset.mem_insert_of_mem (addable_lower μ c hc a hab he)
    · exact Finset.mem_insert_of_mem (μ.isLowerSet hab hb)

/-- Erase a proved actual maximal corner; lower closure is derived. -/
def erase (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Removable μ c) : YoungDiagram where
  cells := μ.cells.erase c
  isLowerSet := by
    intro b a hab hb
    obtain ⟨hbc,hb⟩ := Finset.mem_erase.mp hb
    apply Finset.mem_erase.mpr
    refine ⟨?_,μ.isLowerSet hab hb⟩
    intro he
    subst a
    exact hbc (removable_maximal μ c hc b hb hab)

@[simp] theorem insert_mem (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Addable μ c) (a : ℕ × ℕ) :
    a ∈ insert μ c hc ↔ a=c ∨ a ∈ μ := Finset.mem_insert

@[simp] theorem erase_mem (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Removable μ c) (a : ℕ × ℕ) :
    a ∈ erase μ c hc ↔ a ≠ c ∧ a ∈ μ := Finset.mem_erase

@[simp] theorem insert_card (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Addable μ c) :
    (insert μ c hc).cells.card=μ.cells.card+1 := Finset.card_insert_of_notMem hc.1

@[simp] theorem erase_card (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Removable μ c) :
    (erase μ c hc).cells.card=μ.cells.card-1 := Finset.card_erase_of_mem hc.1

lemma inserted_removable (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Addable μ c) :
    Removable (insert μ c hc) c := by
  refine ⟨by simp,?_,?_⟩
  · rw [insert_mem]
    rintro (he | hm)
    · have := congrArg Prod.fst he; omega
    · exact hc.1 (μ.up_left_mem (by omega) le_rfl hm)
  · rw [insert_mem]
    rintro (he | hm)
    · have := congrArg Prod.snd he; omega
    · exact hc.1 (μ.up_left_mem le_rfl (by omega) hm)

lemma erased_addable (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Removable μ c) :
    Addable (erase μ c hc) c := by
  refine ⟨by simp,?_,?_⟩
  · by_cases hi : c.1=0
    · exact Or.inl hi
    · apply Or.inr
      rw [erase_mem]
      refine ⟨?_,μ.up_left_mem (Nat.sub_le ..) le_rfl hc.1⟩
      intro he
      have := congrArg Prod.fst he
      omega
  · by_cases hj : c.2=0
    · exact Or.inl hj
    · apply Or.inr
      rw [erase_mem]
      refine ⟨?_,μ.up_left_mem le_rfl (Nat.sub_le ..) hc.1⟩
      intro he
      have := congrArg Prod.snd he
      omega

@[simp] theorem erase_insert (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Addable μ c) :
    erase (insert μ c hc) c (inserted_removable μ c hc)=μ := by
  apply YoungDiagram.ext
  exact Finset.erase_insert hc.1

@[simp] theorem insert_erase (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Removable μ c) :
    insert (erase μ c hc) c (erased_addable μ c hc)=μ := by
  apply YoungDiagram.ext
  exact Finset.insert_erase hc.1

lemma addable_row_end (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Addable μ c) : c.2=μ.rowLen c.1 := by
  have hn : ¬c.2 < μ.rowLen c.1 := by
    intro h
    exact hc.1 (YoungDiagram.mem_iff_lt_rowLen.mpr h)
  rcases hc.2.2 with hz | hm
  · omega
  · have hi := YoungDiagram.mem_iff_lt_rowLen.mp hm
    omega

lemma addable_row_bound (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Addable μ c) : c.1 ≤ μ.colLen 0 := by
  rcases hc.2.1 with hz | hm
  · omega
  · have hi := YoungDiagram.mem_iff_lt_colLen.mp hm
    have hl := μ.colLen_anti 0 c.2 (Nat.zero_le _)
    omega

/-- A complete finite enumeration of every actual addable corner. -/
def addableCells (μ : YoungDiagram) : Finset (ℕ × ℕ) :=
  ((range (μ.colLen 0+1)).image (fun i => (i,μ.rowLen i))).filter (Addable μ)

def removableCells (μ : YoungDiagram) : Finset (ℕ × ℕ) := μ.cells.filter (Removable μ)

@[simp] theorem mem_addableCells (μ : YoungDiagram) (c : ℕ × ℕ) :
    c ∈ addableCells μ ↔ Addable μ c := by
  rw [addableCells,Finset.mem_filter]
  constructor
  · exact And.right
  · intro hc
    refine ⟨?_,hc⟩
    exact mem_image.mpr ⟨c.1,mem_range.mpr (by have := addable_row_bound μ c hc; omega),
      Prod.ext rfl (addable_row_end μ c hc).symm⟩

@[simp] theorem mem_removableCells (μ : YoungDiagram) (c : ℕ × ℕ) :
    c ∈ removableCells μ ↔ Removable μ c := by
  simp only [removableCells,Finset.mem_filter]
  exact ⟨And.right,fun hc => ⟨hc.1,hc⟩⟩

end
end Paper20.YoungCorners
