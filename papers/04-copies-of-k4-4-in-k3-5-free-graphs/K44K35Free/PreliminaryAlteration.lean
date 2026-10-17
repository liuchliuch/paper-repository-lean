import K44K35Free.RandomPairing

/-!
# The two preliminary deletions

Edges and copies retain their original indices.  The definitions below perform
exactly the two deletions of Section 3: all edges of isMutual blocks first, then
edges whose load in the original nonmutual blocks exceeds `L`.
-/

open scoped BigOperators
open Finset

namespace K44K35Free.PreliminaryAlteration

variable {E I C : Type*} [DecidableEq E] [Fintype I]

noncomputable def mutualEdges (blocks : I → Finset E) (isMutual : I → Prop) : Finset E := by
  classical
  exact (univ.filter isMutual).biUnion blocks

noncomputable def firstEdges (initial : Finset E) (blocks : I → Finset E)
    (isMutual : I → Prop) : Finset E := initial \ mutualEdges blocks isMutual

noncomputable def blockLoad (blocks : I → Finset E) (isMutual : I → Prop) (e : E) : ℕ := by
  classical
  exact (univ.filter fun i => ¬ isMutual i ∧ e ∈ blocks i).card

noncomputable def preliminaryEdges (initial : Finset E) (blocks : I → Finset E)
    (isMutual : I → Prop) (L : ℕ) : Finset E := by
  classical
  exact (firstEdges initial blocks isMutual).filter fun e => blockLoad blocks isMutual e ≤ L

noncomputable def totalBlockEdges (blocks : I → Finset E) : ℕ := ∑ i, (blocks i).card

noncomputable def mutualBlockEdges (blocks : I → Finset E) (isMutual : I → Prop) : ℕ := by
  classical
  exact ∑ i ∈ univ.filter isMutual, (blocks i).card

@[simp] theorem mem_firstEdges (initial : Finset E) (blocks : I → Finset E)
    (isMutual : I → Prop) (e : E) :
    e ∈ firstEdges initial blocks isMutual ↔
      e ∈ initial ∧ e ∉ mutualEdges blocks isMutual := by
  classical
  exact mem_sdiff

@[simp] theorem mem_preliminaryEdges (initial : Finset E) (blocks : I → Finset E)
    (isMutual : I → Prop) (L : ℕ) (e : E) :
    e ∈ preliminaryEdges initial blocks isMutual L ↔
      e ∈ firstEdges initial blocks isMutual ∧ blockLoad blocks isMutual e ≤ L := by
  classical
  exact mem_filter

theorem preliminaryEdges_subset (initial : Finset E) (blocks : I → Finset E)
    (isMutual : I → Prop) (L : ℕ) :
    preliminaryEdges initial blocks isMutual L ⊆ initial := by
  intro e he
  exact (mem_firstEdges _ _ _ _).1 ((mem_preliminaryEdges _ _ _ _ _).1 he).1 |>.1

theorem preliminaryEdges_load_le (initial : Finset E) (blocks : I → Finset E)
    (isMutual : I → Prop) (L : ℕ) {e : E}
    (he : e ∈ preliminaryEdges initial blocks isMutual L) :
    blockLoad blocks isMutual e ≤ L :=
  ((mem_preliminaryEdges _ _ _ _ _).1 he).2

theorem preliminaryEdges_no_mutual (initial : Finset E) (blocks : I → Finset E)
    (isMutual : I → Prop) (L : ℕ) {e : E}
    (he : e ∈ preliminaryEdges initial blocks isMutual L) {i : I} (hi : isMutual i) :
    e ∉ blocks i := by
  classical
  intro hei
  have hn := ((mem_firstEdges _ _ _ _).1
    ((mem_preliminaryEdges _ _ _ _ _).1 he).1).2
  exact hn (mem_biUnion.2 ⟨i, mem_filter.2 ⟨mem_univ _, hi⟩, hei⟩)

theorem card_mutualEdges_le (blocks : I → Finset E) (isMutual : I → Prop) :
    (mutualEdges blocks isMutual).card ≤ mutualBlockEdges blocks isMutual := by
  classical
  exact card_biUnion_le

/-- Double counting the original indexed block incidences. -/
theorem sum_blockLoad_le (es : Finset E) (blocks : I → Finset E) (isMutual : I → Prop) :
    (∑ e ∈ es, blockLoad blocks isMutual e) ≤ totalBlockEdges blocks := by
  classical
  unfold blockLoad totalBlockEdges
  simp_rw [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  refine sum_le_sum fun i _ => ?_
  have heq : (∑ e ∈ es, if ¬isMutual i ∧ e ∈ blocks i then (1 : ℕ) else 0) =
      (es.filter fun e => ¬isMutual i ∧ e ∈ blocks i).card := by
    exact sum_boole _ _
  rw [heq]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  apply card_le_card
  intro e he
  exact (mem_filter.1 he).2.2

/-- Edges removed by the load threshold cost at most `Z/L`, in integral form. -/
theorem load_deletion_bound (es : Finset E) (blocks : I → Finset E)
    (isMutual : I → Prop) (L : ℕ) :
    L * (es.filter fun e => L < blockLoad blocks isMutual e).card ≤
      totalBlockEdges blocks := by
  classical
  calc
    L * (es.filter fun e => L < blockLoad blocks isMutual e).card =
        ∑ _e ∈ es.filter (fun e => L < blockLoad blocks isMutual e), L := by simp [Nat.mul_comm]
    _ ≤ ∑ e ∈ es.filter (fun e => L < blockLoad blocks isMutual e),
        blockLoad blocks isMutual e := by
      apply sum_le_sum
      intro e he
      exact Nat.le_of_lt (mem_filter.1 he).2
    _ ≤ ∑ e ∈ es, blockLoad blocks isMutual e := by
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by simp)
    _ ≤ _ := sum_blockLoad_le es blocks isMutual

/-- The actual removed edge set is bounded by the two deletion costs. -/
theorem preliminary_deleted_edges_bound (initial : Finset E) (blocks : I → Finset E)
    (isMutual : I → Prop) (L : ℕ) :
    L * (initial \ preliminaryEdges initial blocks isMutual L).card ≤
      L * mutualBlockEdges blocks isMutual + totalBlockEdges blocks := by
  classical
  let high := (firstEdges initial blocks isMutual).filter
    (fun e => L < blockLoad blocks isMutual e)
  have hsub : initial \ preliminaryEdges initial blocks isMutual L ⊆
      mutualEdges blocks isMutual ∪ high := by
    intro e he
    rcases mem_sdiff.1 he with ⟨hei, hen⟩
    by_cases hem : e ∈ mutualEdges blocks isMutual
    · exact mem_union_left _ hem
    · apply mem_union_right
      refine mem_filter.2 ⟨(mem_firstEdges _ _ _ _).2 ⟨hei, hem⟩, ?_⟩
      by_contra hn
      have hl : blockLoad blocks isMutual e ≤ L := by omega
      exact hen ((mem_preliminaryEdges _ _ _ _ _).2
        ⟨(mem_firstEdges _ _ _ _).2 ⟨hei, hem⟩, hl⟩)
  have hc := card_le_card hsub
  have hu := card_union_le (mutualEdges blocks isMutual) high
  have hm := card_mutualEdges_le blocks isMutual
  have hh := load_deletion_bound (firstEdges initial blocks isMutual) blocks isMutual L
  change L * high.card ≤ totalBlockEdges blocks at hh
  nlinarith

noncomputable def survivingCopies [DecidableEq C] (copies : Finset C)
    (copyEdges : C → Finset E) (kept : Finset E) : Finset C := by
  classical
  exact copies.filter fun c => copyEdges c ⊆ kept

/-- Charging destroyed copies to deleted edges, without choosing a charge map.
Every copy is contained in `initial`; each original edge lies in at most `M`
original copies. -/
theorem destroyed_copies_bound [DecidableEq C]
    (initial kept : Finset E) (copies : Finset C) (copyEdges : C → Finset E) (M : ℕ)
    (hcontained : ∀ c ∈ copies, copyEdges c ⊆ initial)
    (hthrough : ∀ e ∈ initial, (copies.filter fun c => e ∈ copyEdges c).card ≤ M) :
    copies.card ≤ (survivingCopies copies copyEdges kept).card +
      M * (initial \ kept).card := by
  classical
  let lost := copies \ survivingCopies copies copyEdges kept
  have hsub : lost ⊆ (initial \ kept).biUnion
      (fun e => copies.filter fun c => e ∈ copyEdges c) := by
    intro c hc
    rcases mem_sdiff.1 hc with ⟨hcc, hcn⟩
    have hn : ¬ copyEdges c ⊆ kept := by
      intro hs
      exact hcn (mem_filter.2 ⟨hcc, hs⟩)
    obtain ⟨e, he, hen⟩ := Finset.not_subset.1 hn
    exact mem_biUnion.2 ⟨e, mem_sdiff.2 ⟨hcontained c hcc he, hen⟩,
      mem_filter.2 ⟨hcc, he⟩⟩
  have hcount : lost.card ≤ M * (initial \ kept).card := by
    calc
      lost.card ≤ ((initial \ kept).biUnion
          (fun e => copies.filter fun c => e ∈ copyEdges c)).card := card_le_card hsub
      _ ≤ ∑ e ∈ initial \ kept, (copies.filter fun c => e ∈ copyEdges c).card := card_biUnion_le
      _ ≤ ∑ _e ∈ initial \ kept, M := by
        apply sum_le_sum
        intro e he
        exact hthrough e (mem_sdiff.1 he).1
      _ = _ := by simp [Nat.mul_comm]
  have hsurv : survivingCopies copies copyEdges kept ⊆ copies := filter_subset _ _
  have hcard := card_sdiff_of_subset hsurv
  change lost.card = _ at hcard
  have hle := card_le_card hsurv
  omega

/-- Pointwise equation (24), in an exact denominator-free natural-number form. -/
theorem preliminary_copies_bound [DecidableEq C]
    (initial : Finset E) (blocks : I → Finset E) (isMutual : I → Prop) (L : ℕ)
    (copies : Finset C) (copyEdges : C → Finset E) (M : ℕ)
    (hcontained : ∀ c ∈ copies, copyEdges c ⊆ initial)
    (hthrough : ∀ e ∈ initial, (copies.filter fun c => e ∈ copyEdges c).card ≤ M) :
    L * copies.card ≤
      L * (survivingCopies copies copyEdges (preliminaryEdges initial blocks isMutual L)).card +
        M * (L * mutualBlockEdges blocks isMutual + totalBlockEdges blocks) := by
  have hd := preliminary_deleted_edges_bound initial blocks isMutual L
  have hc := destroyed_copies_bound initial (preliminaryEdges initial blocks isMutual L)
    copies copyEdges M hcontained hthrough
  nlinarith

/-- Equation (24), in the real-valued form of the paper. -/
theorem preliminary_copies_bound_real [DecidableEq C]
    (initial : Finset E) (blocks : I → Finset E) (isMutual : I → Prop) (L : ℕ)
    (copies : Finset C) (copyEdges : C → Finset E) (M : ℕ) (hL : 0 < L)
    (hcontained : ∀ c ∈ copies, copyEdges c ⊆ initial)
    (hthrough : ∀ e ∈ initial, (copies.filter fun c => e ∈ copyEdges c).card ≤ M) :
    (copies.card : ℝ) - M * ((mutualBlockEdges blocks isMutual : ℝ) +
      (totalBlockEdges blocks : ℝ) / L) ≤
      ((survivingCopies copies copyEdges (preliminaryEdges initial blocks isMutual L)).card : ℝ) := by
  have hc := preliminary_copies_bound initial blocks isMutual L copies copyEdges M
    hcontained hthrough
  have hc' : (L : ℝ) * copies.card ≤ (L : ℝ) *
      (survivingCopies copies copyEdges (preliminaryEdges initial blocks isMutual L)).card +
        M * ((L : ℝ) * mutualBlockEdges blocks isMutual + totalBlockEdges blocks) := by
    exact_mod_cast hc
  have hl : (0 : ℝ) < L := by exact_mod_cast hL
  have he : (L : ℝ) * ((mutualBlockEdges blocks isMutual : ℝ) +
      (totalBlockEdges blocks : ℝ) / L) =
      (L : ℝ) * mutualBlockEdges blocks isMutual + totalBlockEdges blocks := by
    field_simp
  nlinarith

/-- The copy count and both costs can be averaged together, so they hold for
one and the same group element rather than separately chosen outcomes. -/
theorem exists_preliminary_copies [DecidableEq C]
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (initial : Ω → Finset E) (blocks : Ω → I → Finset E) (isMutual : Ω → I → Prop)
    (L : ℕ) (copies : Ω → Finset C) (copyEdges : C → Finset E) (M : ℕ)
    (hL : 0 < L)
    (hcontained : ∀ ω c, c ∈ copies ω → copyEdges c ⊆ initial ω)
    (hthrough : ∀ ω e, e ∈ initial ω →
      ((copies ω).filter fun c => e ∈ copyEdges c).card ≤ M) :
    ∃ ω, RandomPairing.mean (fun ω => ((copies ω).card : ℝ)) -
      M * (RandomPairing.mean (fun ω => (mutualBlockEdges (blocks ω) (isMutual ω) : ℝ)) +
        RandomPairing.mean (fun ω => (totalBlockEdges (blocks ω) : ℝ)) / L) ≤
      ((survivingCopies (copies ω) copyEdges
        (preliminaryEdges (initial ω) (blocks ω) (isMutual ω) L)).card : ℝ) := by
  let K : Ω → ℝ := fun ω =>
    ((survivingCopies (copies ω) copyEdges
      (preliminaryEdges (initial ω) (blocks ω) (isMutual ω) L)).card : ℝ)
  have hp := RandomPairing.mean_mono
    (fun ω => ((copies ω).card : ℝ) - M *
      ((mutualBlockEdges (blocks ω) (isMutual ω) : ℝ) +
        (totalBlockEdges (blocks ω) : ℝ) / L)) K
    (fun ω => preliminary_copies_bound_real (initial ω) (blocks ω) (isMutual ω)
      L (copies ω) copyEdges M hL (hcontained ω) (hthrough ω))
  obtain ⟨ω, hω⟩ := RandomPairing.exists_mean_le K
  refine ⟨ω, le_trans ?_ hω⟩
  convert hp using 1 <;>
    simp only [RandomPairing.mean, sum_sub_distrib, sum_add_distrib,
      ← mul_sum, ← sum_div, sub_div, add_div, mul_div_assoc] <;> ring

end K44K35Free.PreliminaryAlteration
