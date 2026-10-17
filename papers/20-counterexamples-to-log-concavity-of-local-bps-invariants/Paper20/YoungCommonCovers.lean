import Paper20.YoungCovers

namespace Paper20.YoungCorners
open Finset
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

lemma union_strict (μ ν : YoungDiagram) (hn : μ.cells.card=ν.cells.card) (hne : μ ≠ ν) :
    μ.cells ⊂ (μ ⊔ ν).cells := by
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.subset_union_left,?_⟩
  intro he
  have hsub : ν.cells ⊆ μ.cells := by rw [he]; exact Finset.subset_union_right
  have hc : ν.cells=μ.cells := Finset.eq_of_subset_of_card_le hsub (by omega)
  exact hne (YoungDiagram.ext hc.symm)

lemma inter_strict (μ ν : YoungDiagram) (hn : μ.cells.card=ν.cells.card) (hne : μ ≠ ν) :
    (μ ⊓ ν).cells ⊂ μ.cells := by
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.inter_subset_left,?_⟩
  intro he
  have hsub : μ.cells ⊆ ν.cells := by rw [← he]; exact Finset.inter_subset_right
  have hc : μ.cells=ν.cells := Finset.eq_of_subset_of_card_le hsub (by omega)
  exact hne (YoungDiagram.ext hc)

/-- Distinct shapes at the same level have at most one common upper
cover, and it is their actual union. -/
theorem common_upper_eq_sup (μ ν γ : YoungDiagram)
    (hn : μ.cells.card=ν.cells.card) (hne : μ ≠ ν)
    (hμ : Covers μ γ) (hν : Covers ν γ) : γ=μ ⊔ ν := by
  have hsub : (μ ⊔ ν).cells ⊆ γ.cells := Finset.union_subset hμ.1 hν.1
  have hlt := Finset.card_lt_card (union_strict μ ν hn hne)
  apply YoungDiagram.ext
  exact (Finset.eq_of_subset_of_card_le hsub (by have := hμ.2; omega)).symm

/-- The analogous common lower cover is their actual intersection. -/
theorem common_lower_eq_inf (μ ν κ : YoungDiagram)
    (hn : μ.cells.card=ν.cells.card) (hne : μ ≠ ν)
    (hμ : Covers κ μ) (hν : Covers κ ν) : κ=μ ⊓ ν := by
  have hsub : κ.cells ⊆ (μ ⊓ ν).cells := Finset.subset_inter hμ.1 hν.1
  have hlt := Finset.card_lt_card (inter_strict μ ν hn hne)
  apply YoungDiagram.ext
  exact Finset.eq_of_subset_of_card_le hsub (by have := hμ.2; omega)

/-- A common upper cover exists exactly when a common lower cover does.
The proof uses the actual union/intersection cardinal identity. -/
theorem common_cover_nonempty_iff (μ ν : YoungDiagram)
    (hn : μ.cells.card=ν.cells.card) (hne : μ ≠ ν) :
    (∃ γ, Covers μ γ ∧ Covers ν γ) ↔ (∃ κ, Covers κ μ ∧ Covers κ ν) := by
  have hcard := Finset.card_union_add_card_inter μ.cells ν.cells
  constructor
  · rintro ⟨γ,hμ,hν⟩
    have he := common_upper_eq_sup μ ν γ hn hne hμ hν
    have hc : (μ ⊔ ν).cells.card=μ.cells.card+1 := by rw [← he]; exact hμ.2
    refine ⟨μ ⊓ ν,⟨Finset.inter_subset_left,?_⟩,⟨Finset.inter_subset_right,?_⟩⟩
    · change μ.cells.card=(μ.cells ∩ ν.cells).card+1
      change (μ.cells ∪ ν.cells).card=μ.cells.card+1 at hc
      omega
    · change ν.cells.card=(μ.cells ∩ ν.cells).card+1
      change (μ.cells ∪ ν.cells).card=μ.cells.card+1 at hc
      omega
  · rintro ⟨κ,hμ,hν⟩
    have he := common_lower_eq_inf μ ν κ hn hne hμ hν
    have hc : μ.cells.card=(μ ⊓ ν).cells.card+1 := by rw [← he]; exact hμ.2
    refine ⟨μ ⊔ ν,⟨Finset.subset_union_left,?_⟩,⟨Finset.subset_union_right,?_⟩⟩
    · change (μ.cells ∪ ν.cells).card=μ.cells.card+1
      change μ.cells.card=(μ.cells ∩ ν.cells).card+1 at hc
      omega
    · change (μ.cells ∪ ν.cells).card=ν.cells.card+1
      change μ.cells.card=(μ.cells ∩ ν.cells).card+1 at hc
      omega

/-- The off-diagonal Young-lattice differential identity, on genuine
finite single-box covers of actual diagrams. -/
theorem common_cover_card (μ ν : YoungDiagram)
    (hn : μ.cells.card=ν.cells.card) (hne : μ ≠ ν) :
    Nat.card {γ : YoungDiagram // Covers μ γ ∧ Covers ν γ}=
      Nat.card {κ : YoungDiagram // Covers κ μ ∧ Covers κ ν} := by
  let U := {γ : YoungDiagram // Covers μ γ ∧ Covers ν γ}
  let D := {κ : YoungDiagram // Covers κ μ ∧ Covers κ ν}
  have hU : Subsingleton U := ⟨by
    intro a b
    apply Subtype.ext
    exact (common_upper_eq_sup μ ν a.val hn hne a.property.1 a.property.2).trans
      (common_upper_eq_sup μ ν b.val hn hne b.property.1 b.property.2).symm⟩
  have hD : Subsingleton D := ⟨by
    intro a b
    apply Subtype.ext
    exact (common_lower_eq_inf μ ν a.val hn hne a.property.1 a.property.2).trans
      (common_lower_eq_inf μ ν b.val hn hne b.property.1 b.property.2).symm⟩
  letI := hU
  letI := hD
  by_cases hu : Nonempty U
  · letI := hu
    have hd : Nonempty D := by
      obtain ⟨u⟩ := hu
      obtain ⟨d,hd⟩ := (common_cover_nonempty_iff μ ν hn hne).1 ⟨u.val,u.property⟩
      exact ⟨⟨d,hd⟩⟩
    letI := hd
    exact (Nat.card_unique : Nat.card U=1).trans (Nat.card_unique : Nat.card D=1).symm
  · have hd : ¬Nonempty D := by
      intro hd
      obtain ⟨d⟩ := hd
      obtain ⟨u,hu'⟩ := (common_cover_nonempty_iff μ ν hn hne).2 ⟨d.val,d.property⟩
      exact hu ⟨⟨u,hu'⟩⟩
    letI : IsEmpty U := ⟨fun u => hu ⟨u⟩⟩
    letI : IsEmpty D := ⟨fun d => hd ⟨d⟩⟩
    change Nat.card U=Nat.card D
    exact (Nat.card_of_isEmpty : Nat.card U=0).trans (Nat.card_of_isEmpty : Nat.card D=0).symm

end
end Paper20.YoungCorners
