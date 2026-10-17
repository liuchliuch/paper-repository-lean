import Paper20.YoungCorners

namespace Paper20.YoungCorners
open Finset
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

/-- A genuine single-box cover in the Young-diagram inclusion order. -/
def Covers (μ ν : YoungDiagram) : Prop := μ ≤ ν ∧ ν.cells.card=μ.cells.card+1

lemma insert_covers (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Addable μ c) : Covers μ (insert μ c hc) := by
  refine ⟨?_,insert_card μ c hc⟩
  intro a ha
  exact Finset.mem_insert_of_mem ha

lemma erase_covers (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Removable μ c) : Covers (erase μ c hc) μ := by
  refine ⟨Finset.erase_subset _ _,?_⟩
  rw [erase_card]
  have hp : 0 < μ.cells.card := Finset.card_pos.mpr ⟨c,hc.1⟩
  omega

/-- Every actual cover adds precisely one proved outer corner. -/
theorem cover_is_insert (μ ν : YoungDiagram) (hc : Covers μ ν) :
    ∃ c : ℕ × ℕ, ∃ ha : Addable μ c, ν=insert μ c ha := by
  have hsub : μ.cells ⊆ ν.cells := hc.1
  have hcard : (ν.cells\μ.cells).card=1 := by
    rw [Finset.card_sdiff_of_subset hsub,hc.2]
    omega
  obtain ⟨c,hcset⟩ := Finset.card_eq_one.mp hcard
  have hmem : c ∈ ν.cells\μ.cells := by rw [hcset]; simp
  obtain ⟨hν,hμ⟩ := Finset.mem_sdiff.mp hmem
  have hcells : ν.cells=Insert.insert c μ.cells := by
    have he := Finset.sdiff_union_of_subset hsub
    rw [hcset] at he
    simpa only [Finset.singleton_union] using he.symm
  have hpred (a : ℕ × ℕ) (ha : a ≤ c) (hne : a ≠ c) : a ∈ μ := by
    have hm : a ∈ ν.cells := ν.isLowerSet ha hν
    rw [hcells,Finset.mem_insert] at hm
    exact hm.resolve_left hne
  have ha : Addable μ c := by
    refine ⟨hμ,?_,?_⟩
    · by_cases hi : c.1=0
      · exact Or.inl hi
      · apply Or.inr
        apply hpred (c.1-1,c.2) ⟨Nat.sub_le c.1 1,le_rfl⟩
        intro he
        have := congrArg Prod.fst he
        omega
    · by_cases hj : c.2=0
      · exact Or.inl hj
      · apply Or.inr
        apply hpred (c.1,c.2-1) ⟨le_rfl,Nat.sub_le c.2 1⟩
        intro he
        have := congrArg Prod.snd he
        omega
  exact ⟨c,ha,YoungDiagram.ext hcells⟩

lemma insert_injective (μ : YoungDiagram) (c d : ℕ × ℕ) (hc : Addable μ c) (hd : Addable μ d)
    (he : insert μ c hc=insert μ d hd) : c=d := by
  have hm : c ∈ insert μ d hd := by rw [← he]; simp
  exact ((insert_mem μ d hd c).mp hm).resolve_right hc.1

/-- The set of all actual upper covers is equivalent to the finite,
complete enumeration of actual addable corners. -/
def upperCoverEquiv (μ : YoungDiagram) :
    {ν : YoungDiagram // Covers μ ν} ≃ {c : ℕ × ℕ // c ∈ addableCells μ} where
  toFun ν :=
    let c := Classical.choose (cover_is_insert μ ν.val ν.property)
    ⟨c,mem_addableCells μ c |>.2 (Classical.choose_spec
      (cover_is_insert μ ν.val ν.property)).choose⟩
  invFun c := ⟨insert μ c.val ((mem_addableCells μ c.val).mp c.property),
    insert_covers μ c.val ((mem_addableCells μ c.val).mp c.property)⟩
  left_inv ν := by
    apply Subtype.ext
    exact (Classical.choose_spec (Classical.choose_spec (cover_is_insert μ ν.val ν.property))).symm
  right_inv c := by
    apply Subtype.ext
    let ν := insert μ c.val ((mem_addableCells μ c.val).mp c.property)
    have he := Classical.choose_spec (Classical.choose_spec
      (cover_is_insert μ ν (insert_covers μ c.val ((mem_addableCells μ c.val).mp c.property))))
    exact insert_injective μ _ c.val _ _ he.symm

instance upperCoverFinite (μ : YoungDiagram) : Fintype {ν : YoungDiagram // Covers μ ν} :=
  Fintype.ofEquiv {c : ℕ × ℕ // c ∈ addableCells μ} (upperCoverEquiv μ).symm

theorem upperCover_card (μ : YoungDiagram) :
    Fintype.card {ν : YoungDiagram // Covers μ ν}=(addableCells μ).card := by
  rw [Fintype.card_congr (upperCoverEquiv μ),Fintype.card_coe]

/-- Every actual lower cover erases precisely one proved inner corner. -/
theorem cover_is_erase (μ κ : YoungDiagram) (hc : Covers κ μ) :
    ∃ c : ℕ × ℕ, ∃ hr : Removable μ c, κ=erase μ c hr := by
  obtain ⟨c,ha,hμ⟩ := cover_is_insert κ μ hc
  subst μ
  exact ⟨c,inserted_removable κ c ha,(erase_insert κ c ha).symm⟩

lemma erase_injective (μ : YoungDiagram) (c d : ℕ × ℕ) (hc : Removable μ c) (hd : Removable μ d)
    (he : erase μ c hc=erase μ d hd) : c=d := by
  by_contra hn
  have hm : c ∈ erase μ d hd := (erase_mem ..).2 ⟨hn,hc.1⟩
  rw [← he] at hm
  simpa only [erase_mem,ne_eq,not_true_eq_false,false_and] using hm

def lowerCoverEquiv (μ : YoungDiagram) :
    {κ : YoungDiagram // Covers κ μ} ≃ {c : ℕ × ℕ // c ∈ removableCells μ} where
  toFun κ :=
    let c := Classical.choose (cover_is_erase μ κ.val κ.property)
    ⟨c,mem_removableCells μ c |>.2 (Classical.choose_spec
      (cover_is_erase μ κ.val κ.property)).choose⟩
  invFun c := ⟨erase μ c.val ((mem_removableCells μ c.val).mp c.property),
    erase_covers μ c.val ((mem_removableCells μ c.val).mp c.property)⟩
  left_inv κ := by
    apply Subtype.ext
    exact (Classical.choose_spec (Classical.choose_spec (cover_is_erase μ κ.val κ.property))).symm
  right_inv c := by
    apply Subtype.ext
    let κ := erase μ c.val ((mem_removableCells μ c.val).mp c.property)
    have he := Classical.choose_spec (Classical.choose_spec
      (cover_is_erase μ κ (erase_covers μ c.val ((mem_removableCells μ c.val).mp c.property))))
    exact erase_injective μ _ c.val _ _ he.symm

instance lowerCoverFinite (μ : YoungDiagram) : Fintype {κ : YoungDiagram // Covers κ μ} :=
  Fintype.ofEquiv {c : ℕ × ℕ // c ∈ removableCells μ} (lowerCoverEquiv μ).symm

theorem lowerCover_card (μ : YoungDiagram) :
    Fintype.card {κ : YoungDiagram // Covers κ μ}=(removableCells μ).card := by
  rw [Fintype.card_congr (lowerCoverEquiv μ),Fintype.card_coe]

end
end Paper20.YoungCorners
