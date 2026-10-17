import K44K35Free.Pruning
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Independent local choices and surviving designated copies

The finite sample space is the full Cartesian product of the original local
choice sets. Thus the counting argument implements independent uniform choices,
including choices incident with edges removed at the preliminary stage.
-/

open Finset
open scoped BigOperators

namespace K44K35Free

attribute [local instance] Classical.propDecidable

noncomputable section

section IndependentChoices

variable {I C : Type*} {A : I → Type*} [Fintype I] [DecidableEq I]
  [∀ i, DecidableEq (A i)]

/-- A local event in a product sample space costs at most one factor of six for
    every index in its support. This is an integer form of the independence
    product bound, so no measure-theoretic probability space is needed. -/
theorem independent_choice_count
    (options : ∀ i, Finset (A i)) (good : ∀ i, Finset (A i))
    (affecting : Finset I) (N : ℕ)
    (hlocal : ∀ i, (options i).card ≤
      (if i ∈ affecting then 6 else 1) * (good i).card)
    (haffecting : affecting.card ≤ N) :
    (Fintype.piFinset options).card ≤ 6 ^ N * (Fintype.piFinset good).card := by
  rw [Fintype.card_piFinset, Fintype.card_piFinset]
  have hprod := Finset.prod_le_prod' (s := (univ : Finset I))
    (fun i _ => hlocal i)
  rw [Finset.prod_mul_distrib] at hprod
  have hfactor : (∏ i : I, if i ∈ affecting then (6 : ℕ) else 1) =
      6 ^ affecting.card := by
    rw [← Finset.prod_filter]
    simp
  rw [hfactor] at hprod
  exact hprod.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) haffecting))

/-- Double-count successful object/outcome pairs. -/
theorem sum_survival_counts
    (objects : Finset C) (outcomes : Finset (∀ i, A i))
    (P : C → (∀ i, A i) → Prop) [∀ d r, Decidable (P d r)] :
    (∑ d ∈ objects, (outcomes.filter (P d)).card) =
      ∑ r ∈ outcomes, (objects.filter (fun d => P d r)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

/-- Finite averaging: if every object survives in at least the fraction `1/k`
    of the outcomes, an outcome retains at least that fraction of all objects. -/
theorem exists_many_survivors
    (objects : Finset C) (outcomes : Finset (∀ i, A i))
    (houtcomes : outcomes.Nonempty) (P : C → (∀ i, A i) → Prop)
    [∀ d r, Decidable (P d r)] (k : ℕ)
    (hcount : ∀ d ∈ objects, outcomes.card ≤ k * (outcomes.filter (P d)).card) :
    ∃ r ∈ outcomes, objects.card ≤ k * (objects.filter (fun d => P d r)).card := by
  have hsum := Finset.sum_le_sum hcount
  have hswap := sum_survival_counts objects outcomes P
  have havg : (∑ _r ∈ outcomes, objects.card) ≤
      ∑ r ∈ outcomes, k * (objects.filter (fun d => P d r)).card := by
    rw [← Finset.mul_sum, hswap, Finset.mul_sum] at hsum
    simpa only [Finset.sum_const, smul_eq_mul, Nat.mul_comm] using hsum
  exact Finset.exists_le_of_sum_le houtcomes havg

/-- Independent local choice events followed by averaging. The hypotheses are
    cardinal inequalities for the actual local choice sets, rather than an
    assumed survival bound for the resulting graph. -/
theorem independent_choices_retain_fraction
    (objects : Finset C) (options : ∀ i, Finset (A i))
    (good : C → ∀ i, Finset (A i)) (affecting : C → Finset I) (N : ℕ)
    (hoptions : ∀ i, (options i).Nonempty)
    (hsub : ∀ d ∈ objects, ∀ i, good d i ⊆ options i)
    (hlocal : ∀ d ∈ objects, ∀ i, (options i).card ≤
      (if i ∈ affecting d then 6 else 1) * (good d i).card)
    (haffecting : ∀ d ∈ objects, (affecting d).card ≤ N) :
    ∃ r ∈ Fintype.piFinset options,
      objects.card ≤ 6 ^ N *
        (objects.filter (fun d => ∀ i, r i ∈ good d i)).card := by
  have hc : ∀ d ∈ objects, (Fintype.piFinset options).card ≤ 6 ^ N *
      ((Fintype.piFinset options).filter (fun r => ∀ i, r i ∈ good d i)).card := by
    intro d hd
    have heq : ((Fintype.piFinset options).filter
        (fun r => ∀ i, r i ∈ good d i)) = Fintype.piFinset (good d) := by
      ext r
      simp only [Finset.mem_filter, Fintype.mem_piFinset]
      exact ⟨fun h => h.2, fun h => ⟨fun i => hsub d hd i (h i), h⟩⟩
    rw [heq]
    exact independent_choice_count options (good d) (affecting d) N
      (hlocal d hd) (haffecting d hd)
  obtain ⟨r, hr, hb⟩ := exists_many_survivors objects (Fintype.piFinset options)
    (Fintype.piFinset_nonempty.2 hoptions) (fun d r => ∀ i, r i ∈ good d i) (6 ^ N) hc
  refine ⟨r, hr, ?_⟩
  simpa only using hb

end IndependentChoices

section TwoSubsets

variable {V : Type*} [DecidableEq V]

/-- A requirement using at most two vertices extends to a two-subset of the
    original controlled side. -/
theorem exists_two_subset_extension (X Q : Finset V) (hQX : Q ⊆ X)
    (hQ : Q.card ≤ 2) (hX : 2 ≤ X.card) :
    ((X.powersetCard 2).filter (fun R => Q ⊆ R)).Nonempty := by
  obtain ⟨R, hQR, hRX, hR⟩ := Finset.exists_subsuperset_card_eq hQX hQ hX
  exact ⟨R, Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2 ⟨hRX, hR⟩, hQR⟩⟩

/-- The uniform two-subset choice from a three- or four-point controlled side
    retains every fixed requirement of size at most two with probability at
    least `1/6`, written without division. -/
theorem two_subset_retention_count (X Q : Finset V)
    (hX : X.card = 3 ∨ X.card = 4) (hQX : Q ⊆ X) (hQ : Q.card ≤ 2) :
    (X.powersetCard 2).card ≤
      6 * ((X.powersetCard 2).filter (fun R => Q ⊆ R)).card := by
  have hne := exists_two_subset_extension X Q hQX hQ (by omega)
  have hpos := Finset.card_pos.2 hne
  have hsmall : (X.powersetCard 2).card ≤ 6 := by
    rw [Finset.card_powersetCard]
    rcases hX with hX | hX <;> rw [hX] <;> decide
  omega

end TwoSubsets

namespace Pruning

section BlockChoices

variable {P I C : Type*} [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]

/-- Exactly those original block/exceptional-endpoint pairs at which pruning
    makes a nontrivial random choice. -/
def RelevantChoice (blocks : I → Block P) (isMutual : I → Prop) (j : I × P) : Prop :=
  ¬ isMutual j.1 ∧ Active (blocks j.1) ∧ j.2 ∈ (blocks j.1).exceptional

/-- The original two-subset choice sets; irrelevant coordinates have one
    dummy value and do not contribute to the probability cost. -/
noncomputable def choiceOptions (blocks : I → Block P) (isMutual : I → Prop)
    (j : I × P) : Finset (Finset P) :=
  if RelevantChoice blocks isMutual j then (blocks j.1).controlled.powersetCard 2 else {∅}

/-- The actual required controlled-side vertices of one designated edge set. -/
noncomputable def choiceRequirement (D : Finset (P × P))
    (blocks : I → Block P) (isMutual : I → Prop) (j : I × P) : Finset P :=
  if RelevantChoice blocks isMutual j then requirements D (blocks j.1) j.2 else ∅

/-- A choice affects a copy precisely when that choice has a nonempty
    requirement. -/
noncomputable def affectingChoices (D : Finset (P × P))
    (blocks : I → Block P) (isMutual : I → Prop) : Finset (I × P) :=
  univ.filter fun j => RelevantChoice blocks isMutual j ∧
    (requirements D (blocks j.1) j.2).Nonempty

@[simp] theorem mem_affectingChoices {D : Finset (P × P)}
    {blocks : I → Block P} {isMutual : I → Prop} {j : I × P} :
    j ∈ affectingChoices D blocks isMutual ↔
      RelevantChoice blocks isMutual j ∧ (requirements D (blocks j.1) j.2).Nonempty := by
  simp [affectingChoices]

/-- Every affecting choice can be charged injectively to a copy-edge/block
    incidence. Different exceptional endpoints charge different edges. -/
theorem affectingChoices_card_le_incidence (D : Finset (P × P))
    (blocks : I → Block P) (isMutual : I → Prop) :
    (affectingChoices D blocks isMutual).card ≤
      ∑ e ∈ D, (univ.filter fun i => ¬ isMutual i ∧ e ∈ (blocks i).edges).card := by
  let S := affectingChoices D blocks isMutual
  have hreq (j : {j // j ∈ S}) : (requirements D (blocks j.1.1) j.1.2).Nonempty :=
    (mem_affectingChoices.mp j.2).2
  let chosen (j : {j // j ∈ S}) : P := (hreq j).choose
  have hchosen (j : {j // j ∈ S}) :
      chosen j ∈ requirements D (blocks j.1.1) j.1.2 := (hreq j).choose_spec
  let incidence := (D ×ˢ (univ : Finset I)).filter
    (fun ei => ¬ isMutual ei.2 ∧ ei.1 ∈ (blocks ei.2).edges)
  let f (j : {j // j ∈ S}) : (P × P) × I :=
    ((blocks j.1.1).edge (chosen j) j.1.2, j.1.1)
  have hmem (j : {j // j ∈ S}) : f j ∈ incidence := by
    obtain ⟨hrel, _⟩ := mem_affectingChoices.mp j.2
    obtain ⟨hx, he⟩ := mem_requirements.mp (hchosen j)
    exact mem_filter.mpr ⟨mem_product.mpr ⟨he, mem_univ _⟩,
      hrel.1, (Block.edge_mem_edges _ _ _).mpr ⟨hx, hrel.2.2⟩⟩
  have hinj : Function.Injective f := by
    intro j k h
    have hi : j.1.1 = k.1.1 := congrArg Prod.snd h
    have he : (blocks j.1.1).edge (chosen j) j.1.2 =
        (blocks k.1.1).edge (chosen k) k.1.2 := congrArg Prod.fst h
    have hy := congrArg (fun e => (blocks j.1.1).exceptionalEnd e) he
    have hy' : j.1.2 = k.1.2 := by
      simpa only [← hi, Block.exceptionalEnd_edge] using hy
    exact Subtype.ext (Prod.ext hi hy')
  have hcard : S.attach.card ≤ incidence.card :=
    Finset.card_le_card_of_injOn f (fun j _ => hmem j) (fun _ _ _ _ h => hinj h)
  have hincidence : incidence.card =
      ∑ e ∈ D, (univ.filter fun i => ¬ isMutual i ∧ e ∈ (blocks i).edges).card := by
    simp only [incidence, card_eq_sum_ones, sum_filter, sum_product]
  simpa only [card_attach, S, hincidence] using hcard

/-- The load bound is applied to the original indexed nonmutual blocks, and
    bounds the number of independent choices affecting a fixed edge set. -/
theorem affectingChoices_card_le (D : Finset (P × P))
    (blocks : I → Block P) (isMutual : I → Prop) (L : ℕ)
    (hload : ∀ e ∈ D,
      (univ.filter fun i => ¬ isMutual i ∧ e ∈ (blocks i).edges).card ≤ L) :
    (affectingChoices D blocks isMutual).card ≤ D.card * L := by
  calc
    _ ≤ ∑ e ∈ D, (univ.filter fun i => ¬ isMutual i ∧ e ∈ (blocks i).edges).card :=
      affectingChoices_card_le_incidence D blocks isMutual
    _ ≤ ∑ _e ∈ D, L := sum_le_sum hload
    _ = D.card * L := by simp

/-- Off the affecting support, a local choice imposes no requirement at all. -/
theorem choiceRequirement_eq_empty_of_not_affecting
    (D : Finset (P × P)) (blocks : I → Block P) (isMutual : I → Prop) (j : I × P)
    (hj : j ∉ affectingChoices D blocks isMutual) :
    choiceRequirement D blocks isMutual j = ∅ := by
  by_cases hrel : RelevantChoice blocks isMutual j
  · have hne : ¬ (requirements D (blocks j.1) j.2).Nonempty := by
      intro h
      exact hj (mem_affectingChoices.mpr ⟨hrel, h⟩)
    simp only [choiceRequirement, if_pos hrel]
    exact Finset.not_nonempty_iff_eq_empty.mp hne
  · simp only [choiceRequirement, if_neg hrel]

/-- **Proposition 10, finite combinatorial form.** The choices range over all
    original controlled sides. Every retained copy satisfies the actual
    simultaneous edge-pruning rule. The `16 L` exponent follows from the
    sixteen copy edges and the independently proved edge-load bound. -/
theorem exists_pruning_retaining_fraction
    (objects : Finset C) (copyEdges : C → Finset (P × P))
    (pre : Finset (P × P)) (blocks : I → Block P) (isMutual : I → Prop) (L : ℕ)
    (hpre : ∀ d ∈ objects, copyEdges d ⊆ pre)
    (hsize : ∀ d ∈ objects, (copyEdges d).card ≤ 16)
    (hcontrolled : ∀ i, ¬ isMutual i → (blocks i).controlled.card ≤ 4)
    (hrequirements : ∀ d ∈ objects, ∀ i, ¬ isMutual i → Active (blocks i) →
      ∀ y ∈ (blocks i).exceptional, (requirements (copyEdges d) (blocks i) y).card ≤ 2)
    (hload : ∀ e ∈ pre,
      (univ.filter fun i => ¬ isMutual i ∧ e ∈ (blocks i).edges).card ≤ L) :
    ∃ R : I → P → Finset P,
      (∀ i, ¬ isMutual i → Active (blocks i) → ∀ y ∈ (blocks i).exceptional,
        R i y ∈ (blocks i).controlled.powersetCard 2) ∧
      objects.card ≤ 6 ^ (16 * L) *
        (objects.filter (fun d => copyEdges d ⊆ prunedEdges pre blocks isMutual R)).card := by
  let options := choiceOptions blocks isMutual
  let Q := fun d => choiceRequirement (copyEdges d) blocks isMutual
  let good := fun d j => (options j).filter fun R => Q d j ⊆ R
  have hoptions : ∀ j, (options j).Nonempty := by
    intro j
    by_cases hrel : RelevantChoice blocks isMutual j
    · have h2 : 2 ≤ (blocks j.1).controlled.card := by
        have := hrel.2.1
        unfold Active at this
        omega
      obtain ⟨R, hRX, hR⟩ := Finset.exists_subset_card_eq h2
      refine ⟨R, ?_⟩
      simp only [options, choiceOptions, if_pos hrel]
      exact mem_powersetCard.mpr ⟨hRX, hR⟩
    · simp only [options, choiceOptions, if_neg hrel, singleton_nonempty]
  have hsub : ∀ d ∈ objects, ∀ j, good d j ⊆ options j := by
    intro d _ j
    exact filter_subset _ _
  have hlocal : ∀ d ∈ objects, ∀ j, (options j).card ≤
      (if j ∈ affectingChoices (copyEdges d) blocks isMutual then 6 else 1) *
        (good d j).card := by
    intro d hd j
    by_cases hj : j ∈ affectingChoices (copyEdges d) blocks isMutual
    · obtain ⟨hrel, _⟩ := mem_affectingChoices.mp hj
      have hlo : 3 ≤ (blocks j.1).controlled.card := hrel.2.1
      have hhi := hcontrolled j.1 hrel.1
      have hX : (blocks j.1).controlled.card = 3 ∨ (blocks j.1).controlled.card = 4 := by omega
      have hQX := requirements_subset (copyEdges d) (blocks j.1) j.2
      have hQ := hrequirements d hd j.1 hrel.1 hrel.2.1 j.2 hrel.2.2
      simpa only [good, options, Q, choiceOptions, choiceRequirement, if_pos hrel,
        if_pos hj] using two_subset_retention_count (blocks j.1).controlled
          (requirements (copyEdges d) (blocks j.1) j.2) hX hQX hQ
    · have hQ := choiceRequirement_eq_empty_of_not_affecting
        (copyEdges d) blocks isMutual j hj
      simp only [if_neg hj, good, Q, hQ, empty_subset, filter_true, one_mul, le_refl]
  have haffecting : ∀ d ∈ objects,
      (affectingChoices (copyEdges d) blocks isMutual).card ≤ 16 * L := by
    intro d hd
    exact (affectingChoices_card_le (copyEdges d) blocks isMutual L
      (fun e he => hload e (hpre d hd he))).trans
        (Nat.mul_le_mul_right L (hsize d hd))
  obtain ⟨r, hr, hmany⟩ := independent_choices_retain_fraction objects options good
    (fun d => affectingChoices (copyEdges d) blocks isMutual) (16 * L)
    hoptions hsub hlocal haffecting
  let R : I → P → Finset P := fun i y => r (i, y)
  have hvalid : ∀ i, ¬ isMutual i → Active (blocks i) → ∀ y ∈ (blocks i).exceptional,
      R i y ∈ (blocks i).controlled.powersetCard 2 := by
    intro i hi ha y hy
    have h := Fintype.mem_piFinset.mp hr (i, y)
    have hrel : RelevantChoice blocks isMutual (i, y) := ⟨hi, ha, hy⟩
    simpa only [R, options, choiceOptions, if_pos hrel] using h
  refine ⟨R, hvalid, ?_⟩
  have heq : (objects.filter (fun d => ∀ j, r j ∈ good d j)) =
      objects.filter (fun d => copyEdges d ⊆ prunedEdges pre blocks isMutual R) := by
    apply filter_congr
    intro d hd
    constructor
    · intro h
      apply subset_prunedEdges_iff.mpr
      refine ⟨hpre d hd, ?_⟩
      intro i hi ha y hy
      have hgood := (mem_filter.mp (h (i, y))).2
      have hrel : RelevantChoice blocks isMutual (i, y) := ⟨hi, ha, hy⟩
      simpa only [R, Q, choiceRequirement, if_pos hrel] using hgood
    · intro h j
      refine mem_filter.mpr ⟨Fintype.mem_piFinset.mp hr j, ?_⟩
      by_cases hrel : RelevantChoice blocks isMutual j
      · have hreq := (subset_prunedEdges_iff.mp h).2 j.1 hrel.1 hrel.2.1 j.2 hrel.2.2
        simpa only [Q, choiceRequirement, if_pos hrel] using hreq
      · simp only [Q, choiceRequirement, if_neg hrel, empty_subset]
  rwa [heq] at hmany

/-- Real-valued paper form of the same finite averaging conclusion. -/
theorem exists_pruning_retaining_fraction_real
    (objects : Finset C) (copyEdges : C → Finset (P × P))
    (pre : Finset (P × P)) (blocks : I → Block P) (isMutual : I → Prop) (L : ℕ)
    (hpre : ∀ d ∈ objects, copyEdges d ⊆ pre)
    (hsize : ∀ d ∈ objects, (copyEdges d).card ≤ 16)
    (hcontrolled : ∀ i, ¬ isMutual i → (blocks i).controlled.card ≤ 4)
    (hrequirements : ∀ d ∈ objects, ∀ i, ¬ isMutual i → Active (blocks i) →
      ∀ y ∈ (blocks i).exceptional, (requirements (copyEdges d) (blocks i) y).card ≤ 2)
    (hload : ∀ e ∈ pre,
      (univ.filter fun i => ¬ isMutual i ∧ e ∈ (blocks i).edges).card ≤ L) :
    ∃ R : I → P → Finset P,
      (∀ i, ¬ isMutual i → Active (blocks i) → ∀ y ∈ (blocks i).exceptional,
        R i y ∈ (blocks i).controlled.powersetCard 2) ∧
      (objects.card : ℝ) / 6 ^ (16 * L) ≤
        (objects.filter (fun d => copyEdges d ⊆ prunedEdges pre blocks isMutual R)).card := by
  obtain ⟨R, hR, hcount⟩ := exists_pruning_retaining_fraction objects copyEdges pre blocks
    isMutual L hpre hsize hcontrolled hrequirements hload
  refine ⟨R, hR, ?_⟩
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 6 ^ (16 * L))]
  have hcast : (objects.card : ℝ) ≤ 6 ^ (16 * L) *
      (objects.filter (fun d => copyEdges d ⊆ prunedEdges pre blocks isMutual R)).card := by
    exact_mod_cast hcount
  simpa only [mul_comm] using hcast

end BlockChoices

end Pruning

end

end K44K35Free
