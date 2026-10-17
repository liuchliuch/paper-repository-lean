import Paper09.ColorInfluence
import Paper09.LocalSimulation
import Paper09.CouplingPatch

open Finset BigOperators Classical Real
open Paper09.Disagreement Paper09.ColorInfluence Paper09.BlockKernels Paper09.LocalSimulation
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000

namespace Paper09.SimulatedColorInfluence

variable {V ι : Type*} [Fintype V] [Fintype ι]

/-- All other selected blocks, after isolating the unique affected one. -/
def restSites (I : Finset ι) (B : ι → Finset V) (i : ι) : Finset V :=
  selectedSites (I.erase i) B

theorem selectedSites_split (I : Finset ι) (B : ι → Finset V) {i : ι} (hi : i ∈ I) :
    selectedSites I B = B i ∪ restSites I B i := by
  unfold selectedSites restSites
  conv_lhs => rw [← insert_erase hi]
  rw [biUnion_insert]
  rfl

theorem block_rest_disjoint (Λ : Lattice V) (I : Finset ι) (B : ι → Finset V)
    (hdis : I.toSet.PairwiseDisjoint (fun i => closure Λ (B i)))
    {i : ι} (hi : i ∈ I) : Disjoint (B i) (restSites I B i) := by
  apply disjoint_left.mpr
  intro x hxi hxC
  obtain ⟨j, hj, hxj⟩ := mem_biUnion.mp hxC
  have hji := (mem_erase.mp hj).1
  exact hji (selected_block_unique Λ I B hdis (mem_erase.mp hj).2 hi
    (mem_union_left _ hxj) (mem_union_left _ hxi))

theorem block_rest_no_edge (Λ : Lattice V) (I : Finset ι) (B : ι → Finset V)
    (hdis : I.toSet.PairwiseDisjoint (fun i => closure Λ (B i)))
    {i : ι} (hi : i ∈ I) : ∀ x ∈ B i, ∀ z ∈ restSites I B i, ¬ Λ.adj x z := by
  intro x hx z hz
  obtain ⟨j, hj, hzj⟩ := mem_biUnion.mp hz
  exact selected_no_edge Λ I B hdis hi (mem_erase.mp hj).2 (mem_erase.mp hj).1.symm hx hzj

/-- Every vertex of the union closure belongs to a selected block closure. -/
theorem closure_selected_subset (Λ : Lattice V) (I : Finset ι) (B : ι → Finset V) :
    closure Λ (selectedSites I B) ⊆ I.biUnion (fun i => closure Λ (B i)) := by
  intro x hx
  rcases mem_union.mp hx with hx | hx
  · obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hx
    exact mem_biUnion.mpr ⟨i, hi, mem_union_left _ hxi⟩
  · obtain ⟨hxU, z, hzU, hzx⟩ := Λ.mem_boundary.mp hx
    obtain ⟨i, hi, hzi⟩ := mem_biUnion.mp hzU
    have hxBi : x ∉ B i := fun hh => hxU (mem_biUnion.mpr ⟨i, hi, hh⟩)
    exact mem_biUnion.mpr ⟨i, hi,
      mem_union_right _ (Λ.mem_boundary.mpr ⟨hxBi, z, hzi, hzx⟩)⟩

/-- The whole untouched union's closure is disjoint from the affected block's
closure, so common local CT evolution cannot see its discrepancies. -/
theorem closure_rest_disjoint (Λ : Lattice V) (I : Finset ι) (B : ι → Finset V)
    (hdis : I.toSet.PairwiseDisjoint (fun i => closure Λ (B i)))
    {i : ι} (hi : i ∈ I) : Disjoint (closure Λ (B i)) (closure Λ (restSites I B i)) := by
  apply disjoint_left.mpr
  intro x hxi hxC
  obtain ⟨j, hj, hxj⟩ := mem_biUnion.mp (closure_selected_subset Λ (I.erase i) B hxC)
  exact (mem_erase.mp hj).1 (selected_block_unique Λ I B hdis (mem_erase.mp hj).2 hi hxj hxi)

/-- The input supports for all unaffected block evolutions agree on their
whole closure, after arbitrary outputs of the affected block have been drawn. -/
theorem affected_supports_agree_rest (Λ : Lattice V) (I : Finset ι) (B : ι → Finset V)
    (hdis : I.toSet.PairwiseDisjoint (fun i => closure Λ (B i)))
    {i : ι} (hi : i ∈ I) {y : V} (hy : y ∈ closure Λ (B i))
    (τ τ' : Config V) (hrest : ∀ z, z ≠ y → τ z = τ' z)
    {p q : FinProb (Config V)} (hp : FrozenOutside (B i) τ p) (hq : FrozenOutside (B i) τ' q)
    (η ξ : Config V) (hη : p.w η ≠ 0) (hξ : q.w ξ ≠ 0) :
    ∀ z ∈ closure Λ (restSites I B i), η z = ξ z := by
  intro z hz
  have hdz := closure_rest_disjoint Λ I B hdis hi
  have hzBi : z ∉ B i := fun hh => disjoint_left.mp hdz (mem_union_left _ hh) hz
  have hzy : z ≠ y := fun he => disjoint_left.mp hdz hy (he ▸ hz)
  rw [hp η hη z hzBi, hq ξ hξ z hzBi, hrest z hzy]

/-- Exact simultaneous CT evolution on a color class cannot have greater
transport cost than its unique affected local CT evolution. Every other block
is evolved by a genuine synchronous coupling with exactly preserved cost. -/
theorem union_transition_le_affected (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (I : Finset ι) (B : ι → Finset V)
    (hdis : I.toSet.PairwiseDisjoint (fun i => closure Λ (B i)))
    {i : ι} (hi : i ∈ I) {y : V} (hy : y ∈ closure Λ (B i))
    (τ τ' : Config V) (hrest : ∀ z, z ≠ y → τ z = τ' z) (t : ℝ) :
    hammingWasserstein
      (Censoring.siteTransition (gibbs Λ h β univ ∅ (fun _ => 0)) (Censoring.gibbs_positive Λ h β ∅ _) (selectedSites I B) t τ)
      (Censoring.siteTransition (gibbs Λ h β univ ∅ (fun _ => 0)) (Censoring.gibbs_positive Λ h β ∅ _) (selectedSites I B) t τ') ≤
    hammingWasserstein
      (Censoring.siteTransition (gibbs Λ h β univ ∅ (fun _ => 0)) (Censoring.gibbs_positive Λ h β ∅ _) (B i) t τ)
      (Censoring.siteTransition (gibbs Λ h β univ ∅ (fun _ => 0)) (Censoring.gibbs_positive Λ h β ∅ _) (B i) t τ') := by
  let p := gibbs Λ h β univ ∅ (fun _ => 0)
  let hp := Censoring.gibbs_positive Λ h β ∅ (fun _ => 0)
  let C := restSites I B i
  have hd := block_rest_disjoint Λ I B hdis hi
  have hno := block_rest_no_edge Λ I B hdis hi
  have hτ := gibbs_siteTransition_union Λ h β ∅ (fun _ => 0) (B i) C hd hno t τ
  have hτ' := gibbs_siteTransition_union Λ h β ∅ (fun _ => 0) (B i) C hd hno t τ'
  rw [← selectedSites_split I B hi] at hτ hτ'
  rw [← hτ, ← hτ']
  apply CouplingPatch.bind_wasserstein_le _ C (closure Λ C) subset_union_left
  · intro η
    exact siteTransition_frozen p hp C t η
  · intro η ξ hcl
    exact gibbs_siteTransition_closure_transport Λ h β ∅ C (fun _ => 0) η ξ hcl t
  · intro η ξ hη hξ
    exact affected_supports_agree_rest Λ I B hdis hi hy τ τ' hrest
      (siteTransition_frozen p hp (B i) t τ) (siteTransition_frozen p hp (B i) t τ') η ξ hη hξ

/-- If the discrepancy misses every selected closure, all actual local
physical evolutions can use the same samples and retain cost exactly one. -/
theorem unaffected_transition_le_one (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (I : Finset ι) (B : ι → Finset V) (τ τ' : Config V) (y : V)
    (hy : τ y ≠ τ' y) (hrest : ∀ z, z ≠ y → τ z = τ' z)
    (hmiss : ∀ i ∈ I, y ∉ closure Λ (B i)) (t : ℝ) :
    hammingWasserstein
      (Censoring.siteTransition (gibbs Λ h β univ ∅ (fun _ => 0)) (Censoring.gibbs_positive Λ h β ∅ _) (selectedSites I B) t τ)
      (Censoring.siteTransition (gibbs Λ h β univ ∅ (fun _ => 0)) (Censoring.gibbs_positive Λ h β ∅ _) (selectedSites I B) t τ') ≤ 1 := by
  let U := selectedSites I B
  have hcl : ∀ z ∈ closure Λ U, τ z = τ' z := by
    intro z hz
    apply hrest z
    intro hzy
    subst z
    obtain ⟨i, hi, hyi⟩ := mem_biUnion.mp (closure_selected_subset Λ I B hz)
    exact hmiss i hi hyi
  have hw := CouplingPatch.row_wasserstein_le
    (Censoring.siteTransition (gibbs Λ h β univ ∅ (fun _ => 0)) (Censoring.gibbs_positive Λ h β ∅ _) U t)
    U (closure Λ U) subset_union_left τ τ'
    (siteTransition_frozen _ _ U t τ)
    (gibbs_siteTransition_closure_transport Λ h β ∅ U (fun _ => 0) τ τ' hcl t) hcl
  have hh : hamming τ τ' = 1 := (hamming_eq_one_iff τ τ').mpr ⟨y, hy, hrest⟩
  simpa only [hammingR, hh, Nat.cast_one] using hw

/-- Only one local approximation on each side is charged: the rest of the
color class is coupled by its exact CT locality, without approximation. -/
theorem affected_simulation_gluing (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (I : Finset ι) (B : ι → Finset V)
    (hdis : I.toSet.PairwiseDisjoint (fun i => closure Λ (B i)))
    {i : ι} (hi : i ∈ I) {y : V} (hy : y ∈ closure Λ (B i))
    (M : ℕ) (hM : (B i).card ≤ M) (δ : ℝ) (hδ : 0 ≤ δ)
    (τ τ' : Config V) (hrest : ∀ z, z ≠ y → τ z = τ' z) (t : ℝ)
    (hlocal : ∀ η, tvDist
      (Censoring.siteTransition (gibbs Λ h β univ ∅ (fun _ => 0)) (Censoring.gibbs_positive Λ h β ∅ _) (B i) t η)
      (blockHeatBath (gibbs Λ h β univ ∅ (fun _ => 0)) (gibbs_positive Λ h β univ ∅ _) (B i) η) ≤ δ) :
    hammingWasserstein
      (Censoring.siteTransition (gibbs Λ h β univ ∅ (fun _ => 0)) (Censoring.gibbs_positive Λ h β ∅ _) (selectedSites I B) t τ)
      (Censoring.siteTransition (gibbs Λ h β univ ∅ (fun _ => 0)) (Censoring.gibbs_positive Λ h β ∅ _) (selectedSites I B) t τ') ≤
    hammingWasserstein
      (blockHeatBath (gibbs Λ h β univ ∅ (fun _ => 0)) (gibbs_positive Λ h β univ ∅ _) (B i) τ)
      (blockHeatBath (gibbs Λ h β univ ∅ (fun _ => 0)) (gibbs_positive Λ h β univ ∅ _) (B i) τ') + 2 * (M : ℝ) * δ := by
  let p := gibbs Λ h β univ ∅ (fun _ => 0)
  let hp := Censoring.gibbs_positive Λ h β ∅ (fun _ => 0)
  have hglue := block_simulation_gluing (B i) τ τ'
    (Censoring.siteTransition p hp (B i) t τ) (Censoring.siteTransition p hp (B i) t τ')
    (blockHeatBath p hp (B i) τ) (blockHeatBath p hp (B i) τ') δ δ
    (siteTransition_frozen p hp (B i) t τ) (blockHeatBath_support p hp (B i) τ)
    (siteTransition_frozen p hp (B i) t τ') (blockHeatBath_support p hp (B i) τ')
    (hlocal τ) (by rw [tvDist_comm]; exact hlocal τ')
  have hsize : (B i).card * (δ + δ) ≤ 2 * (M : ℝ) * δ := by
    have hm : ((B i).card : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    nlinarith
  exact (union_transition_le_affected Λ h β I B hdis hi hy τ τ' hrest t).trans
    (hglue.trans (add_le_add_left hsize _))

private theorem sum_affected_indicator (Λ : Lattice V) (I : Finset ι) (B : ι → Finset V)
    (hdis : I.toSet.PairwiseDisjoint (fun i => closure Λ (B i)))
    {i : ι} (hi : i ∈ I) {y : V} (hy : y ∈ closure Λ (B i))
    (P : ι → Prop) [DecidablePred P] (hP : ∀ j, P j → y ∈ closure Λ (B j)) :
    (∑ j ∈ I, if P j then (1 : ℝ) else 0) = if P i then 1 else 0 := by
  apply sum_eq_single i
  · intro j hj hji
    have hn : ¬ P j := by
      intro hjP
      exact hji (selected_block_unique Λ I B hdis hj hi (hP j hjP) hy)
    simp [hn]
  · intro hn
    exact False.elim (hn hi)

/-- The actual CT color update has the ideal per-color budget plus exactly
two local approximation errors on its unique affected block. All unaffected
physical block evolutions are coupled synchronously, with no error charge. -/
theorem simulated_color_update_budget {d : ℕ} (Λ : Lattice V)
    (h : LatticeGeometry.Point d → ℝ) (K β : ℝ)
    (f : V → LatticeGeometry.Point d) (hf : Function.Injective f)
    (hadj : ∀ ⦃x z⦄, Λ.adj x z → LatticeGeometry.Adj (f x) (f z))
    (I : Finset ι) (B : ι → Finset V)
    (hdis : I.toSet.PairwiseDisjoint (fun i => closure Λ (B i)))
    (R r₀ s M : ℕ) (hr₀ : 0 < r₀) (hrs : r₀ ≤ s)
    (hM : ∀ i ∈ I, (B i).card ≤ M) (δ : ℝ) (hδ : 0 ≤ δ)
    (τ τ' : Config V) (y : V) (hy : τ y ≠ τ' y)
    (hrest : ∀ z, z ≠ y → τ z = τ' z)
    (hβ : 0 ≤ β) (hdeg : (Λ.maxDegree : ℝ) ≤ 2 * d)
    (hgood : ∀ i ∈ I, y ∈ Λ.boundary (B i) → ∃ v : LatticeGeometry.Point d,
      Percolation.goodLabel K (rho K d β) R r₀ s h v ∧
      f y ∈ Percolation.latticeCube (Percolation.coarseCenter R v) R)
    (t : ℝ)
    (hlocal : ∀ i ∈ I, ∀ η, tvDist
      (Censoring.siteTransition (gibbs Λ (fun z => h (f z)) β univ ∅ (fun _ => 0))
        (Censoring.gibbs_positive Λ _ β ∅ _) (B i) t η)
      (blockHeatBath (gibbs Λ (fun z => h (f z)) β univ ∅ (fun _ => 0))
        (gibbs_positive Λ _ β univ ∅ _) (B i) η) ≤ δ) :
    hammingWasserstein
      (Censoring.siteTransition (gibbs Λ (fun z => h (f z)) β univ ∅ (fun _ => 0))
        (Censoring.gibbs_positive Λ _ β ∅ _) (selectedSites I B) t τ)
      (Censoring.siteTransition (gibbs Λ (fun z => h (f z)) β univ ∅ (fun _ => 0))
        (Censoring.gibbs_positive Λ _ β ∅ _) (selectedSites I B) t τ') ≤
      1 - (∑ i ∈ I, if y ∈ B i then (1 : ℝ) else 0) +
        goodRootBudget K β d r₀ s M * (∑ i ∈ I, if y ∈ Λ.boundary (B i) then (1 : ℝ) else 0) +
        2 * (M : ℝ) * δ * ((∑ i ∈ I, if y ∈ B i then (1 : ℝ) else 0) +
          (∑ i ∈ I, if y ∈ Λ.boundary (B i) then (1 : ℝ) else 0)) := by
  by_cases haff : ∃ i ∈ I, y ∈ closure Λ (B i)
  · obtain ⟨i, hi, hyi⟩ := haff
    have hI : (∑ j ∈ I, if y ∈ B j then (1 : ℝ) else 0) = if y ∈ B i then 1 else 0 :=
      sum_affected_indicator Λ I B hdis hi hyi (fun j => y ∈ B j) (fun j hj => mem_union_left _ hj)
    have hD : (∑ j ∈ I, if y ∈ Λ.boundary (B j) then (1 : ℝ) else 0) =
        if y ∈ Λ.boundary (B i) then 1 else 0 :=
      sum_affected_indicator Λ I B hdis hi hyi (fun j => y ∈ Λ.boundary (B j))
        (fun j hj => mem_union_right _ hj)
    have hsum : (if y ∈ B i then (1 : ℝ) else 0) +
        (if y ∈ Λ.boundary (B i) then 1 else 0) = 1 := by
      by_cases hyBi : y ∈ B i
      · have hyDb : y ∉ Λ.boundary (B i) := fun hh => (Λ.mem_boundary.mp hh).1 hyBi
        simp [hyBi, hyDb]
      · have hyDb : y ∈ Λ.boundary (B i) := (mem_union.mp hyi).resolve_left hyBi
        simp [hyBi, hyDb]
    have hsingle : ({i} : Finset ι).toSet.PairwiseDisjoint (fun j => closure Λ (B j)) := by
      intro j hj k hk hne
      have hji : j = i := by simpa using hj
      have hki : k = i := by simpa using hk
      exact False.elim (hne (hji.trans hki.symm))
    have hideal := color_update_good_root_budget Λ h K β f hf hadj {i} B hsingle R r₀ s M hr₀ hrs
      (fun j hj => by
        have hji : j = i := by simpa using hj
        subst j
        exact hM i hi)
      τ τ' y hy hrest hβ hdeg
      (fun j hj hjb => by
        have hji : j = i := by simpa using hj
        subst j
        exact hgood i hi hjb)
    simp only [selectedSites, singleton_biUnion, sum_singleton] at hideal
    have hsim := affected_simulation_gluing Λ (fun z => h (f z)) β I B hdis hi hyi M (hM i hi)
      δ hδ τ τ' hrest t (hlocal i hi)
    rw [hI, hD, hsum, mul_one]
    exact hsim.trans (add_le_add_right hideal _)
  · have hmiss : ∀ i ∈ I, y ∉ closure Λ (B i) := fun i hi hcl => haff ⟨i, hi, hcl⟩
    have hI : (∑ i ∈ I, if y ∈ B i then (1 : ℝ) else 0) = 0 := by
      apply sum_eq_zero
      intro i hi
      have hn : y ∉ B i := fun hh => hmiss i hi (mem_union_left _ hh)
      simp [hn]
    have hD : (∑ i ∈ I, if y ∈ Λ.boundary (B i) then (1 : ℝ) else 0) = 0 := by
      apply sum_eq_zero
      intro i hi
      have hn : y ∉ Λ.boundary (B i) := fun hh => hmiss i hi (mem_union_right _ hh)
      simp [hn]
    rw [hI, hD]
    simp only [sub_zero, mul_zero, add_zero]
    exact unaffected_transition_le_one Λ (fun z => h (f z)) β I B τ τ' y hy hrest hmiss t

end Paper09.SimulatedColorInfluence
