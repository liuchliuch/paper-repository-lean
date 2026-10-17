import Paper20.YoungPathTableau

namespace Paper20.YoungShapes
open Finset Paper20.YoungCorners
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

abbrev Cells (μ : YoungDiagram) := {c : ℕ × ℕ // c ∈ μ.cells}

/-- Genuine standard Young fillings: a bijection between the finite
labels and all actual diagram cells, strictly increasing along the cell
partial order. -/
def StandardFilling {n : ℕ} (μ : Shape n) :=
  {e : Fin n ≃ Cells μ.val // StrictMono e.symm}

instance standardFillingFintype {n : ℕ} (μ : Shape n) : Fintype (StandardFilling μ) := by
  classical
  unfold StandardFilling
  infer_instance

def pathFilling {n : ℕ} {μ : Shape n} (t : Path n μ) : StandardFilling μ :=
  ⟨positionEquiv t,filling_strictMono t⟩

/-- The cell with the largest label in an actual standard filling is a
proved removable corner of the actual Young diagram. -/
theorem filling_last_removable {n : ℕ} {μ : Shape (n+1)} (t : StandardFilling μ) :
    Removable μ.val (t.val (Fin.last n)).val := by
  let c := t.val (Fin.last n)
  have hmax : ∀ a : Cells μ.val, c≤a → a=c := by
    intro a hca
    by_contra hn
    have hlt : c < a := lt_of_le_of_ne hca (Ne.symm hn)
    have he := t.property hlt
    rw [Equiv.symm_apply_apply] at he
    exact (not_lt_of_ge (Fin.le_last _)) he
  refine ⟨c.property,?_,?_⟩
  · intro hm
    have hle : c≤(⟨(c.val.1+1,c.val.2),hm⟩:Cells μ.val) :=
      ⟨Nat.le_succ _,le_rfl⟩
    have he := hmax ⟨(c.val.1+1,c.val.2),hm⟩ hle
    have hv := congrArg (fun a : Cells μ.val => a.val.1) he
    dsimp only at hv
    omega
  · intro hm
    have hle : c≤(⟨(c.val.1,c.val.2+1),hm⟩:Cells μ.val) :=
      ⟨le_rfl,Nat.le_succ _⟩
    have he := hmax ⟨(c.val.1,c.val.2+1),hm⟩ hle
    have hv := congrArg (fun a : Cells μ.val => a.val.2) he
    dsimp only at hv
    omega

/-- The genuine preceding shape obtained by deleting the last label. -/
def fillingPrevious {n : ℕ} {μ : Shape (n+1)} (t : StandardFilling μ) : Shape n :=
  ⟨erase μ.val (t.val (Fin.last n)).val (filling_last_removable t),by
    rw [erase_card,μ.property]
    omega⟩

lemma mem_fillingPrevious {n : ℕ} {μ : Shape (n+1)} (t : StandardFilling μ) (c : ℕ × ℕ) :
    c ∈ (fillingPrevious t).val ↔ c≠(t.val (Fin.last n)).val ∧ c ∈ μ.val :=
  erase_mem μ.val (t.val (Fin.last n)).val (filling_last_removable t) c

/-- The actual cell-label bijection restricted to all labels before the
last; its codomain is the actual erased diagram. -/
def fillingPrefixEquiv {n : ℕ} {μ : Shape (n+1)} (t : StandardFilling μ) :
    Fin n ≃ Cells (fillingPrevious t).val where
  toFun i := ⟨(t.val i.castSucc).val,by
    apply (mem_fillingPrevious t _).mpr
    refine ⟨?_,(t.val i.castSucc).property⟩
    intro he
    have ht : t.val i.castSucc=t.val (Fin.last n) := Subtype.ext he
    have hi := t.val.injective ht
    have hv := congrArg Fin.val hi
    simp only [Fin.coe_castSucc,Fin.val_last] at hv
    have := i.isLt
    omega⟩
  invFun c :=
    let a : Cells μ.val := ⟨c.val,((mem_fillingPrevious t _).mp c.property).2⟩
    ⟨(t.val.symm a).val,by
      have hi := (t.val.symm a).isLt
      have hn : t.val.symm a≠Fin.last n := by
        intro he
        have ht := congrArg t.val he
        rw [Equiv.apply_symm_apply] at ht
        have hc := ((mem_fillingPrevious t _).mp c.property).1
        exact hc (congrArg Subtype.val ht)
      have hn' : (t.val.symm a).val≠n := by
        intro he
        exact hn (Fin.ext he)
      omega⟩
  left_inv i := by
    apply Fin.ext
    change (t.val.symm ⟨(t.val i.castSucc).val,_⟩).val=i.val
    have he : (⟨(t.val i.castSucc).val,_⟩:Cells μ.val)=t.val i.castSucc := rfl
    rw [he,Equiv.symm_apply_apply]
    rfl
  right_inv c := by
    apply Subtype.ext
    let a : Cells μ.val := ⟨c.val,((mem_fillingPrevious t _).mp c.property).2⟩
    have ha : (t.val.symm a).val < n := by
      have hn : t.val.symm a≠Fin.last n := by
        intro he
        have ht := congrArg t.val he
        rw [Equiv.apply_symm_apply] at ht
        exact ((mem_fillingPrevious t _).mp c.property).1 (congrArg Subtype.val ht)
      have hn' : (t.val.symm a).val≠n := fun he => hn (Fin.ext he)
      have hlt := (t.val.symm a).isLt
      omega
    change (t.val (Fin.castSucc ⟨(t.val.symm a).val,ha⟩)).val=c.val
    have hi : Fin.castSucc (⟨(t.val.symm a).val,ha⟩:Fin n)=t.val.symm a := Fin.ext rfl
    rw [hi,Equiv.apply_symm_apply]

/-- The restriction of an actual standard filling remains standard on
the actual preceding Young diagram. -/
def fillingPrefix {n : ℕ} {μ : Shape (n+1)} (t : StandardFilling μ) :
    StandardFilling (fillingPrevious t) :=
  ⟨fillingPrefixEquiv t,by
    intro a b hab
    have he := t.property (show (⟨a.val,((mem_fillingPrevious t _).mp a.property).2⟩:Cells μ.val)<
      ⟨b.val,((mem_fillingPrevious t _).mp b.property).2⟩ from hab)
    exact he⟩

end
end Paper20.YoungShapes
