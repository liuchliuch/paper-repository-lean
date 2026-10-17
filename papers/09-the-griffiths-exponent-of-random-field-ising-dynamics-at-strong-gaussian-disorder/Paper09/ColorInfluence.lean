import Paper09.Disagreement
import Paper09.BlockKernels
import Paper09.BlockDynamics
import Paper09.DisagreementGoodRoot

open Finset BigOperators Classical Real
open Paper09.Disagreement Paper09.BlockKernels
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000

namespace Paper09.ColorInfluence

variable {V ι : Type*} [Fintype V] [Fintype ι]

def closure (Λ : Lattice V) (A : Finset V) : Finset V := A ∪ Λ.boundary A

def selectedSites (I : Finset ι) (B : ι → Finset V) : Finset V := I.biUnion B

theorem selected_block_unique (Λ : Lattice V) (I : Finset ι) (B : ι → Finset V)
    (hdis : I.toSet.PairwiseDisjoint (fun i => closure Λ (B i)))
    {i j : ι} (hi : i ∈ I) (hj : j ∈ I) {y : V}
    (hyi : y ∈ closure Λ (B i)) (hyj : y ∈ closure Λ (B j)) : i = j := by
  by_contra hne
  exact disjoint_left.mp (hdis hi hj hne) hyi hyj

theorem selected_no_edge (Λ : Lattice V) (I : Finset ι) (B : ι → Finset V)
    (hdis : I.toSet.PairwiseDisjoint (fun i => closure Λ (B i)))
    {i j : ι} (hi : i ∈ I) (hj : j ∈ I) (hne : i ≠ j)
    {u v : V} (hu : u ∈ B i) (hv : v ∈ B j) : ¬ Λ.adj u v := by
  intro ha
  have hvi : v ∈ closure Λ (B i) := by
    by_cases hvB : v ∈ B i
    · exact mem_union_left _ hvB
    · exact mem_union_right _ (Λ.mem_boundary.mpr ⟨hvB, u, hu, ha⟩)
  exact hne (selected_block_unique Λ I B hdis hi hj hvi (mem_union_left _ hv))

theorem root_neighbor_unique (Λ : Lattice V) (I : Finset ι) (B : ι → Finset V)
    (hdis : I.toSet.PairwiseDisjoint (fun i => closure Λ (B i)))
    {i : ι} (hi : i ∈ I) {y v : V} (hy : y ∈ Λ.boundary (B i))
    (hv : v ∈ selectedSites I B) (ha : Λ.adj y v) : v ∈ B i := by
  obtain ⟨j, hj, hvj⟩ := mem_biUnion.mp hv
  have hyj : y ∈ closure Λ (B j) := by
    by_cases hyB : y ∈ B j
    · exact mem_union_left _ hyB
    · exact mem_union_right _ (Λ.mem_boundary.mpr ⟨hyB, v, hvj, Λ.symm ha⟩)
  have hij := selected_block_unique Λ I B hdis hi hj (mem_union_right _ hy) hyj
  simpa only [hij] using hvj

/-- A path of actual disagreements entering one selected block cannot cross
to any other block of the class; this uses the disjoint closures themselves. -/
theorem disagreement_path_confined (Λ : Lattice V) (I : Finset ι) (B : ι → Finset V)
    (hdis : I.toSet.PairwiseDisjoint (fun i => closure Λ (B i)))
    {i : ι} (hi : i ∈ I) {y : V} (hy : y ∈ Λ.boundary (B i))
    (Γ : V → Prop) (hΓ : ∀ z, Γ z → z = y ∨ z ∈ selectedSites I B)
    {x : V} (hx : x ∈ selectedSites I B) (hxy : x ≠ y)
    (hpath : (Percolation.openGraph (latticeGraph Λ) Γ).Reachable y x) : x ∈ B i := by
  by_contra hxB
  have hxS : x ∉ insert y (B i) := by simp [hxB, hxy]
  obtain ⟨u, hu, v, hv, huv⟩ := Percolation.reachable_exit (mem_insert_self y (B i)) hxS hpath
  have hvy : v ≠ y := fun he => hv (by simp [he])
  have hvU : v ∈ selectedSites I B := (hΓ v huv.2.2).resolve_left hvy
  have hvBi : v ∉ B i := fun hh => hv (mem_insert_of_mem hh)
  rcases mem_insert.mp hu with rfl | hu
  · exact hvBi (root_neighbor_unique Λ I B hdis hi hy hvU huv.1)
  · obtain ⟨j, hj, hvj⟩ := mem_biUnion.mp hvU
    have hne : i ≠ j := by intro he; exact hvBi (he ▸ hvj)
    exact selected_no_edge Λ I B hdis hi hj hne hu hvj huv.1

/-- A single initial discrepancy contributes exactly one to any revealed set
which contains its location, and zero otherwise. -/
theorem defectCount_one_site (E : Finset V) (η ξ : Config V) (y : V)
    (hy : η y ≠ ξ y) (hrest : ∀ z, z ≠ y → η z = ξ z) :
    defectCount E ξ η = if y ∈ E then 1 else 0 := by
  have he : (E.filter fun z => η z ≠ ξ z) = if y ∈ E then {y} else ∅ := by
    ext z
    by_cases hzy : z = y
    · subst z; by_cases hyE : y ∈ E <;> simp [hy, hyE]
    · by_cases hyE : y ∈ E <;> simp [hzy, hrest z hzy, hyE]
  unfold defectCount
  rw [he]
  split_ifs <;> simp

/-- When the selected union contains the discrepancy, exact block resampling
has equal inputs on its frozen exterior and hence identical output laws. -/
theorem containing_update_erases (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (U : Finset V) (η ξ : Config V) (y : V) (hyU : y ∈ U)
    (hrest : ∀ z, z ≠ y → η z = ξ z) :
    hammingWasserstein (blockHeatBath p hp U η) (blockHeatBath p hp U ξ) = 0 := by
  have he : blockHeatBath p hp U η = blockHeatBath p hp U ξ := by
    apply condition_eq_of_agrees
    intro z hz
    have hzy : z ≠ y := fun he => (mem_sdiff.mp hz).2 (he ▸ hyU)
    exact (hrest z hzy).symm
  rw [he]
  exact Wasserstein.self hammingR_nonneg (fun ζ => by simp [hammingR, hamming_self])

/-- A block boundary point cannot lie inside any other selected block. -/
theorem boundary_outside_selected (Λ : Lattice V) (I : Finset ι) (B : ι → Finset V)
    (hdis : I.toSet.PairwiseDisjoint (fun i => closure Λ (B i)))
    {i : ι} (hi : i ∈ I) {y : V} (hy : y ∈ Λ.boundary (B i)) :
    y ∉ selectedSites I B := by
  intro hyU
  obtain ⟨j, hj, hyj⟩ := mem_biUnion.mp hyU
  have hij := selected_block_unique Λ I B hdis hi hj (mem_union_right _ hy) (mem_union_left _ hyj)
  exact (Λ.mem_boundary.mp hy).1 (hij ▸ hyj)

/-- The actual forced-cluster influence statistic for the selected color.
The independent marks range over the whole selected union, while `M` is the
size of its unique affected block. -/
def influenceStatistic (Λ : Lattice V) (h : V → ℝ) (β K d : ℝ)
    (U : Finset V) (M : ℕ) (y : V) : ℝ :=
  (DisagreementMarks.productMarks (openingProbability h K (rho K d β))
    (openingProbability_nonneg h K _ (rho_pos _ _ _).le)
    (openingProbability_le_one h K _ (rho_lt_one _ _ _).le) U).expect
      (fun ω => (min M (forcedClusterCard Λ ω y) : ℝ))

/-- For a boundary perturbation, the exploration's actual Hamming cost is
charged only to the unique affected block, regardless of the union's size. -/
theorem color_pointwise_bound (Λ : Lattice V) (I : Finset ι) (B : ι → Finset V)
    (hdis : I.toSet.PairwiseDisjoint (fun i => closure Λ (B i)))
    {i : ι} (hi : i ∈ I) {y : V} (hyB : y ∈ Λ.boundary (B i))
    (M : ℕ) (hM : (B i).card ≤ M) (τ τ' η ξ : Config V)
    (hy : τ y ≠ τ' y) (hrest : ∀ z, z ≠ y → τ z = τ' z)
    (ω : V → Bool)
    (hη : agrees (univ \ selectedSites I B) τ η)
    (hξ : agrees (univ \ selectedSites I B) τ' ξ)
    (hsupp : ExplorationSupport Λ univ ∅ (univ \ selectedSites I B)
      (fun _ => 0) (fun _ => 0) τ τ' η ξ ω) :
    hamming η ξ ≤ 1 + min M (forcedClusterCard Λ ω y) := by
  let U := selectedSites I B
  let E : Finset V := univ \ U
  have hyU : y ∉ U := boundary_outside_selected Λ I B hdis hi hyB
  have hyE : y ∈ E := by simp [E, hyU]
  have horigin : ∀ r, origin E ∅ τ τ' (fun _ => 0) (fun _ => 0) r → r = y := by
    intro r hr
    rcases hr with ⟨hr, hrdiff⟩ | ⟨hr, _⟩
    · by_contra hry
      exact hrdiff (hrest r hry)
    · simp at hr
  have hopen : ∀ z, differenceOpen univ ∅ (fun _ => 0) (fun _ => 0) η ξ z → z = y ∨ z ∈ U := by
    intro z hz
    have hzdiff : η z ≠ ξ z := by simpa [differenceOpen] using hz
    by_cases hzU : z ∈ U
    · exact Or.inr hzU
    · have hzE : z ∈ E := by simp [E, hzU]
      by_cases hzy : z = y
      · exact Or.inl hzy
      · exact False.elim (hzdiff (by rw [hη z hzE, hξ z hzE, hrest z hzy]))
  have hconfined (z : V) (hz : z ∈ U) (hzdiff : η z ≠ ξ z) : z ∈ B i := by
    have hz' : z ∈ (univ : Finset V) \ E := by simpa [E] using hz
    obtain ⟨r, hr, hpath⟩ := hsupp.2.1 z hz' hzdiff
    have hry := horigin r hr
    subst r
    exact disagreement_path_confined Λ I B hdis hi hyB _ hopen hz
      (fun hzy => hyU (hzy ▸ hz)) hpath
  have hcM : (U.filter fun z => η z ≠ ξ z).card ≤ M := by
    apply (card_le_card ?_).trans hM
    intro z hz
    exact hconfined z (mem_filter.mp hz).1 (mem_filter.mp hz).2
  have hcC : (U.filter fun z => η z ≠ ξ z).card ≤ forcedClusterCard Λ ω y := by
    apply card_le_card
    intro z hz
    obtain ⟨hzU, hzdiff⟩ := mem_filter.mp hz
    have hz' : z ∈ (univ : Finset V) \ E := by simpa [E] using hzU
    exact mem_filter.mpr ⟨mem_univ _, disagreement_cluster_from_sources Λ univ ∅ E
      (fun _ => 0) (fun _ => 0) τ τ' η ξ ω y horigin hsupp.2.1 hsupp.2.2 hη hξ z hz' hzdiff⟩
  have heq := hamming_revealed_partition univ E (subset_univ E) τ τ' η ξ hη hξ
    (fun z hz => False.elim (hz (mem_univ z)))
  have hcount := defectCount_one_site E τ τ' y hy hrest
  rw [if_pos hyE] at hcount
  have hUE : (univ : Finset V) \ E = U := by ext z; simp [E]
  rw [hUE] at heq
  rw [heq, hcount]
  exact Nat.add_le_add_left (le_min hcM hcC) 1

/-- The unique affected block controls a parallel color update's actual
conditional Gibbs resampling cost. -/
theorem boundary_update_influence (Λ : Lattice V) (h : V → ℝ) (β K d : ℝ)
    (I : Finset ι) (B : ι → Finset V)
    (hdis : I.toSet.PairwiseDisjoint (fun i => closure Λ (B i)))
    {i : ι} (hi : i ∈ I) {y : V} (hyB : y ∈ Λ.boundary (B i))
    (M : ℕ) (hM : (B i).card ≤ M) (τ τ' : Config V)
    (hy : τ y ≠ τ' y) (hrest : ∀ z, z ≠ y → τ z = τ' z)
    (hβ : 0 ≤ β) (hdeg : (Λ.maxDegree : ℝ) ≤ 2 * d) :
    hammingWasserstein
      (blockHeatBath (gibbs Λ h β univ ∅ (fun _ => 0)) (gibbs_positive Λ h β univ ∅ _) (selectedSites I B) τ)
      (blockHeatBath (gibbs Λ h β univ ∅ (fun _ => 0)) (gibbs_positive Λ h β univ ∅ _) (selectedSites I B) τ') ≤
      1 + influenceStatistic Λ h β K d (selectedSites I B) M y := by
  let E : Finset V := univ \ selectedSites I B
  obtain ⟨c, hc⟩ := exists_marked_exploration Λ h β K d univ ∅ (by simp) (fun _ => 0)
    (fun _ => 0) hβ hdeg E (subset_univ E) τ τ'
  calc hammingWasserstein _ _ ≤ c.toCoupling.cost hammingR := Wasserstein.le_cost hammingR_nonneg _
    _ ≤ _ := by
      have hbound := marked_cost_le c (fun ω => 1 + (min M (forcedClusterCard Λ ω y) : ℝ)) ?_
      · have hUE : (univ : Finset V) \ E = selectedSites I B := by ext z; simp [E]
        simpa only [FinProb.expect_add, FinProb.expect_const, hUE, influenceStatistic] using hbound
      · intro η ξ ω hm
        have hη : agrees E τ η := by
          apply condition_support _ _ E τ η
          intro hz
          exact hm (c.mass_eq_zero_of_left hz ξ ω)
        have hξ : agrees E τ' ξ := by
          apply condition_support _ _ E τ' ξ
          intro hz
          exact hm (c.mass_eq_zero_of_right hz η ω)
        have hb := color_pointwise_bound Λ I B hdis hi hyB M hM τ τ' η ξ hy hrest ω hη hξ (hc η ξ ω hm)
        dsimp only
        unfold hammingR
        exact_mod_cast hb

/-- An update with no adjacent boundary perturbation retains only the original
one-site discrepancy, by the actual Gibbs spatial Markov coupling. -/
theorem unaffected_update_influence (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (U : Finset V) (τ τ' : Config V) (y : V) (hyU : y ∉ U)
    (hrest : ∀ z, z ≠ y → τ z = τ' z)
    (hadj : ∀ z ∈ U, ¬ Λ.adj y z) :
    hammingWasserstein
      (blockHeatBath (gibbs Λ h β univ ∅ (fun _ => 0)) (gibbs_positive Λ h β univ ∅ _) U τ)
      (blockHeatBath (gibbs Λ h β univ ∅ (fun _ => 0)) (gibbs_positive Λ h β univ ∅ _) U τ') ≤ 1 := by
  let E : Finset V := univ \ U
  have hUE : (univ : Finset V) \ E = U := by ext z; simp [E]
  have hsep : ∀ u ∈ (univ : Finset V) \ E, ∀ v ∈ E, Λ.adj u v → τ v = τ' v := by
    intro u hu v hv ha
    rw [hUE] at hu
    by_cases hvy : v = y
    · subst v
      exact False.elim (hadj u hu (Λ.symm ha))
    · exact hrest v hvy
  let c := stoppedCoupling Λ h β univ ∅ E (fun _ => 0) (fun _ => 0) τ τ' hsep
    (by intro u hu v hv; simp at hv)
  have hcost : c.cost hammingR ≤ 1 := by
    calc c.cost hammingR ≤ c.cost (fun _ _ => 1) := by
          unfold Coupling.cost
          apply sum_le_sum
          intro η _
          apply sum_le_sum
          intro ξ _
          by_cases hm : c.mass η ξ = 0
          · simp [hm]
          · apply mul_le_mul_of_nonneg_left _ (c.nonneg η ξ)
            have hη := coupling_revealed_left _ _ _ E τ c hm
            have hξ := coupling_revealed_right _ _ _ E τ' c hm
            have hoff : ∀ z, z ≠ y → η z = ξ z := by
              intro z hzy
              by_cases hzE : z ∈ E
              · rw [hη z hzE, hξ z hzE, hrest z hzy]
              · exact stoppedCoupling_identical_unexplored Λ h β univ ∅ E
                  (fun _ => 0) (fun _ => 0) τ τ' _ _ η ξ hm z hzE
            have hn : hamming η ξ ≤ 1 := by
              have hsub : (univ.filter fun z => η z ≠ ξ z) ⊆ {y} := by
                intro z hz
                by_contra hzy
                exact (mem_filter.mp hz).2 (hoff z (by simpa using hzy))
              simpa [hamming] using card_le_card hsub
            dsimp only
            unfold hammingR
            exact_mod_cast hn
      _ = 1 := c.cost_const _
  exact (Wasserstein.le_cost hammingR_nonneg c).trans hcost

private theorem sum_indicator_single {S : Finset ι} {P : ι → Prop} [DecidablePred P] {i : ι}
    (hi : i ∈ S) (hPi : P i) (hunique : ∀ j ∈ S, P j → j = i) :
    (∑ j ∈ S, if P j then (1 : ℝ) else 0) = 1 := by
  have he : S.filter P = {i} := by
    ext j
    constructor
    · intro hj
      exact mem_singleton.mpr (hunique j (mem_filter.mp hj).1 (mem_filter.mp hj).2)
    · intro hj
      have hji := mem_singleton.mp hj
      subst j
      exact mem_filter.mpr ⟨hi, hPi⟩
  rw [sum_boole, he]
  simp

/-- The exact per-color budget derived from actual conditional Gibbs updates,
with no kernel-coupling or contraction hypothesis. -/
theorem color_update_statistic_budget (Λ : Lattice V) (h : V → ℝ) (β K d : ℝ)
    (I : Finset ι) (B : ι → Finset V)
    (hdis : I.toSet.PairwiseDisjoint (fun i => closure Λ (B i)))
    (M : ℕ) (hM : ∀ i ∈ I, (B i).card ≤ M) (τ τ' : Config V) (y : V)
    (hy : τ y ≠ τ' y) (hrest : ∀ z, z ≠ y → τ z = τ' z)
    (hβ : 0 ≤ β) (hdeg : (Λ.maxDegree : ℝ) ≤ 2 * d) :
    hammingWasserstein
      (blockHeatBath (gibbs Λ h β univ ∅ (fun _ => 0)) (gibbs_positive Λ h β univ ∅ _) (selectedSites I B) τ)
      (blockHeatBath (gibbs Λ h β univ ∅ (fun _ => 0)) (gibbs_positive Λ h β univ ∅ _) (selectedSites I B) τ') ≤
      1 - (∑ i ∈ I, if y ∈ B i then (1 : ℝ) else 0) +
        influenceStatistic Λ h β K d (selectedSites I B) M y *
          (∑ i ∈ I, if y ∈ Λ.boundary (B i) then (1 : ℝ) else 0) := by
  by_cases hyU : y ∈ selectedSites I B
  · obtain ⟨i, hi, hyi⟩ := mem_biUnion.mp hyU
    have hsum : (∑ i ∈ I, if y ∈ B i then (1 : ℝ) else 0) = 1 := by
      apply sum_indicator_single (P := fun j => y ∈ B j) hi hyi
      intro j hj hyj
      exact selected_block_unique Λ I B hdis hj hi (mem_union_left _ hyj) (mem_union_left _ hyi)
    have hbd : (∑ i ∈ I, if y ∈ Λ.boundary (B i) then (1 : ℝ) else 0) = 0 := by
      apply sum_eq_zero
      intro j hj
      have hnot : y ∉ Λ.boundary (B j) := by
        intro hyj
        exact boundary_outside_selected Λ I B hdis hj hyj (mem_biUnion.mpr ⟨i, hi, hyi⟩)
      simp [hnot]
    rw [hsum, hbd, mul_zero, sub_self, add_zero]
    exact le_of_eq (containing_update_erases _ _ _ τ τ' y (mem_biUnion.mpr ⟨i, hi, hyi⟩) hrest)
  · have hsum : (∑ i ∈ I, if y ∈ B i then (1 : ℝ) else 0) = 0 := by
      apply sum_eq_zero
      intro i hi
      have hnot : y ∉ B i := fun hyi => hyU (mem_biUnion.mpr ⟨i, hi, hyi⟩)
      simp [hnot]
    rw [hsum, sub_zero]
    by_cases hbd : ∃ i ∈ I, y ∈ Λ.boundary (B i)
    · obtain ⟨i, hi, hyi⟩ := hbd
      have hsumB : (∑ i ∈ I, if y ∈ Λ.boundary (B i) then (1 : ℝ) else 0) = 1 := by
        apply sum_indicator_single (P := fun j => y ∈ Λ.boundary (B j)) hi hyi
        intro j hj hyj
        exact selected_block_unique Λ I B hdis hj hi (mem_union_right _ hyj) (mem_union_right _ hyi)
      rw [hsumB, mul_one]
      exact boundary_update_influence Λ h β K d I B hdis hi hyi M (hM i hi) τ τ' hy hrest hβ hdeg
    · have hsumB : (∑ i ∈ I, if y ∈ Λ.boundary (B i) then (1 : ℝ) else 0) = 0 := by
        apply sum_eq_zero
        intro i hi
        have hnot : y ∉ Λ.boundary (B i) := fun hyi => hbd ⟨i, hi, hyi⟩
        simp [hnot]
      rw [hsumB, mul_zero, add_zero]
      apply unaffected_update_influence Λ h β _ τ τ' y hyU hrest
      intro z hz ha
      obtain ⟨i, hi, hzi⟩ := mem_biUnion.mp hz
      have hyi : y ∉ B i := fun hh => hyU (mem_biUnion.mpr ⟨i, hi, hh⟩)
      exact hbd ⟨i, hi, Λ.mem_boundary.mpr ⟨hyi, z, hzi, Λ.symm ha⟩⟩

/-- The explicit uniform influence budget supplied by the actual good-root
percolation bound, before the scale substitution `r₀≈(log R)^2`, `s≈R/8`. -/
def goodRootBudget (K β : ℝ) (d r₀ s M : ℕ) : ℝ :=
  (r₀ : ℝ) + 2 / rho K d β + (M : ℝ) / rho K d β * exp (-(s : ℝ))

theorem influenceStatistic_good_root {d : ℕ} (Λ : Lattice V)
    (h : LatticeGeometry.Point d → ℝ) (K β : ℝ)
    (f : V → LatticeGeometry.Point d) (hf : Function.Injective f)
    (hadj : ∀ ⦃x z⦄, Λ.adj x z → LatticeGeometry.Adj (f x) (f z))
    (U : Finset V) (y : V) (hyU : y ∉ U) (R r₀ s M : ℕ) (v : LatticeGeometry.Point d)
    (hr₀ : 0 < r₀) (hrs : r₀ ≤ s)
    (hgood : Percolation.goodLabel K (rho K d β) R r₀ s h v)
    (hy : f y ∈ Percolation.latticeCube (Percolation.coarseCenter R v) R) :
    influenceStatistic Λ (fun z => h (f z)) β K d U M y ≤ goodRootBudget K β d r₀ s M := by
  simpa only [influenceStatistic, goodRootBudget, DisagreementUniforms.openingParameter,
    openingProbability] using DisagreementGoodRoot.expected_forced_cluster Λ h K (rho K d β)
      (rho_pos K d β) (rho_lt_one K d β).le f hf hadj U y hyU R r₀ s M v hr₀ hrs hgood hy

/-- Equation (3.15) for an actual union-of-disjoint-blocks heat-bath update.
The numerical boundary cost is proved from source good labels and the actual
uniform noise, rather than supplied as a coupling or tail hypothesis. -/
theorem color_update_good_root_budget {d : ℕ} (Λ : Lattice V)
    (h : LatticeGeometry.Point d → ℝ) (K β : ℝ)
    (f : V → LatticeGeometry.Point d) (hf : Function.Injective f)
    (hadj : ∀ ⦃x z⦄, Λ.adj x z → LatticeGeometry.Adj (f x) (f z))
    (I : Finset ι) (B : ι → Finset V)
    (hdis : I.toSet.PairwiseDisjoint (fun i => closure Λ (B i)))
    (R r₀ s M : ℕ) (hr₀ : 0 < r₀) (hrs : r₀ ≤ s)
    (hM : ∀ i ∈ I, (B i).card ≤ M) (τ τ' : Config V) (y : V)
    (hy : τ y ≠ τ' y) (hrest : ∀ z, z ≠ y → τ z = τ' z)
    (hβ : 0 ≤ β) (hdeg : (Λ.maxDegree : ℝ) ≤ 2 * d)
    (hgood : ∀ i ∈ I, y ∈ Λ.boundary (B i) → ∃ v : LatticeGeometry.Point d,
      Percolation.goodLabel K (rho K d β) R r₀ s h v ∧
      f y ∈ Percolation.latticeCube (Percolation.coarseCenter R v) R) :
    hammingWasserstein
      (blockHeatBath (gibbs Λ (fun z => h (f z)) β univ ∅ (fun _ => 0))
        (gibbs_positive Λ _ β univ ∅ _) (selectedSites I B) τ)
      (blockHeatBath (gibbs Λ (fun z => h (f z)) β univ ∅ (fun _ => 0))
        (gibbs_positive Λ _ β univ ∅ _) (selectedSites I B) τ') ≤
      1 - (∑ i ∈ I, if y ∈ B i then (1 : ℝ) else 0) +
        goodRootBudget K β d r₀ s M * (∑ i ∈ I, if y ∈ Λ.boundary (B i) then (1 : ℝ) else 0) := by
  have hbudget := color_update_statistic_budget Λ (fun z => h (f z)) β K d I B hdis M hM
    τ τ' y hy hrest hβ hdeg
  by_cases hbd : ∃ i ∈ I, y ∈ Λ.boundary (B i)
  · obtain ⟨i, hi, hyi⟩ := hbd
    obtain ⟨v, hv, hyv⟩ := hgood i hi hyi
    have hstat := influenceStatistic_good_root Λ h K β f hf hadj (selectedSites I B) y
      (boundary_outside_selected Λ I B hdis hi hyi) R r₀ s M v hr₀ hrs hv hyv
    have hnonneg : 0 ≤ (∑ i ∈ I, if y ∈ Λ.boundary (B i) then (1 : ℝ) else 0) :=
      sum_nonneg fun i _ => by split_ifs <;> norm_num
    exact hbudget.trans (add_le_add_left (mul_le_mul_of_nonneg_right hstat hnonneg) _)
  · have hsum : (∑ i ∈ I, if y ∈ Λ.boundary (B i) then (1 : ℝ) else 0) = 0 := by
      apply sum_eq_zero
      intro i hi
      have hn : y ∉ Λ.boundary (B i) := fun hyi => hbd ⟨i, hi, hyi⟩
      simp [hn]
    simpa only [hsum, mul_zero, add_zero] using hbudget

/-- A specified color's actual union of blocks. -/
def colorSites {Q : ℕ} (c : ι → Fin Q) (B : ι → Finset V) (a : Fin Q) : Finset V :=
  selectedSites (univ.filter fun i => c i = a) B

/-- The real per-color conditional Gibbs kernel satisfies exactly the
`BlockDynamics.stepBudget` consumed by the already-proved color averaging. -/
theorem color_stepBudget {d Q : ℕ} (Λ : Lattice V)
    (h : LatticeGeometry.Point d → ℝ) (K β : ℝ)
    (f : V → LatticeGeometry.Point d) (hf : Function.Injective f)
    (hadj : ∀ ⦃x z⦄, Λ.adj x z → LatticeGeometry.Adj (f x) (f z))
    (c : ι → Fin Q) (B : ι → Finset V)
    (hdis : ∀ i j, i ≠ j → c i = c j → Disjoint (closure Λ (B i)) (closure Λ (B j)))
    (R r₀ s M : ℕ) (hr₀ : 0 < r₀) (hrs : r₀ ≤ s)
    (hM : ∀ i, (B i).card ≤ M) (τ τ' : Config V) (y : V)
    (hy : τ y ≠ τ' y) (hrest : ∀ z, z ≠ y → τ z = τ' z)
    (hβ : 0 ≤ β) (hdeg : (Λ.maxDegree : ℝ) ≤ 2 * d)
    (hgood : ∀ i, y ∈ Λ.boundary (B i) → ∃ v : LatticeGeometry.Point d,
      Percolation.goodLabel K (rho K d β) R r₀ s h v ∧
      f y ∈ Percolation.latticeCube (Percolation.coarseCenter R v) R) (a : Fin Q) :
    hammingWasserstein
      (blockHeatBath (gibbs Λ (fun z => h (f z)) β univ ∅ (fun _ => 0))
        (gibbs_positive Λ _ β univ ∅ _) (colorSites c B a) τ)
      (blockHeatBath (gibbs Λ (fun z => h (f z)) β univ ∅ (fun _ => 0))
        (gibbs_positive Λ _ β univ ∅ _) (colorSites c B a) τ') ≤
      BlockDynamics.stepBudget c B (fun i => Λ.boundary (B i)) (goodRootBudget K β d r₀ s M) a y := by
  let I : Finset ι := univ.filter fun i => c i = a
  have hdisI : I.toSet.PairwiseDisjoint (fun i => closure Λ (B i)) := by
    intro i hi j hj hne
    exact hdis i j hne (((mem_filter.mp hi).2).trans (mem_filter.mp hj).2.symm)
  have hb := color_update_good_root_budget Λ h K β f hf hadj I B hdisI R r₀ s M hr₀ hrs
    (fun i _ => hM i) τ τ' y hy hrest hβ hdeg (fun i _ => hgood i)
  simpa only [BlockDynamics.stepBudget, colorSites, I, Finset.sum_filter, ite_and] using hb

end Paper09.ColorInfluence
