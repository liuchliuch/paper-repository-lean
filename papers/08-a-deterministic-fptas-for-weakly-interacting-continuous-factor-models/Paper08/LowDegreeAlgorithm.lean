import Paper08.MultiMoments
import Paper08.SmallDegree
import Paper08.CellGrid
import Paper08.Oracle
import Paper08.FPTAS
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting

/-! # The actual component algorithm for primal degree at most one

The coordinate blocks and the allocation of factor occurrences are constructed
from the input scopes. No partition or integral-factorization certificate is an input.
-/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Paper08.LowDegreeAlgorithm
open Integral

/-- The actual primal graph on coordinates. -/
def primal {n r m : ℕ} (E : FactorFamily n r m) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ∃ e, u ∈ (E e).scope ∧ v ∈ (E e).scope
  symm := by rintro u v ⟨hne, e, hu, hv⟩; exact ⟨hne.symm, e, hv, hu⟩
  loopless := by intro u h; exact h.1 rfl

instance {n r m : ℕ} (E : FactorFamily n r m) : DecidableRel (primal E).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ ∃ e : Fin m, _ ∧ _))

theorem neighborFinset_primal {n r m : ℕ} (E : FactorFamily n r m) (v : Fin n) :
    (primal E).neighborFinset v = primalNeighbors E v := by
  ext u
  simp only [SimpleGraph.mem_neighborFinset, primal, primalNeighbors,
    Finset.mem_filter, Finset.mem_univ, true_and]
  aesop

/-- In a graph of maximum degree one every reachable pair is already adjacent
or equal. The proof rules out two distinct neighbours at the middle of a walk. -/
theorem reachable_eq_or_adj {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v ≤ 1)
    {u v : V} (huv : G.Reachable u v) : u = v ∨ G.Adj u v := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => exact Or.inl rfl
  | @cons u v w huv p ih =>
    rcases ih with h | hvw
    · subst w
      exact Or.inr huv
    · left
      exact Finset.card_le_one.mp (hdeg v) u (by simpa using huv.symm) w (by simpa using hvw)

/-- An explicitly enumerated closed neighbourhood. Under the degree-one
hypothesis it is the complete connected component. -/
def block {n r m : ℕ} (E : FactorFamily n r m) (v : Fin n) : Finset (Fin n) :=
  insert v (primalNeighbors E v)

def blocks {n r m : ℕ} (E : FactorFamily n r m) : Finset (Finset (Fin n)) :=
  Finset.univ.image (block E)

theorem mem_block_iff_reachable {n r m : ℕ} (E : FactorFamily n r m)
    (hdeg : FamilyPrimalDegreeLe E 1) (u v : Fin n) :
    v ∈ block E u ↔ (primal E).Reachable u v := by
  rw [block, ← neighborFinset_primal]
  simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro (h | h)
    · subst v; exact SimpleGraph.Reachable.rfl
    · exact h.reachable
  · intro h
    rcases reachable_eq_or_adj (primal E)
      (fun v => by simpa [← neighborFinset_primal] using hdeg v) h with h | h
    · exact Or.inl h.symm
    · exact Or.inr h

theorem block_eq_of_mem {n r m : ℕ} (E : FactorFamily n r m)
    (hdeg : FamilyPrimalDegreeLe E 1) {u v : Fin n} (hv : v ∈ block E u) :
    block E v = block E u := by
  have huv := (mem_block_iff_reachable E hdeg u v).mp hv
  ext w
  simp only [mem_block_iff_reachable E hdeg]
  exact ⟨fun h => huv.trans h, fun h => huv.symm.trans h⟩

theorem block_card_le_two {n r m : ℕ} (E : FactorFamily n r m)
    (hdeg : FamilyPrimalDegreeLe E 1) {C : Finset (Fin n)} (hC : C ∈ blocks E) :
    C.card ≤ 2 := by
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hC
  exact (Finset.card_insert_le _ _).trans (by have := hdeg v; omega)

theorem block_nonempty {n r m : ℕ} (E : FactorFamily n r m)
    {C : Finset (Fin n)} (hC : C ∈ blocks E) : C.Nonempty := by
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hC
  exact ⟨v, Finset.mem_insert_self _ _⟩

theorem blocks_card_le {n r m : ℕ} (E : FactorFamily n r m) : (blocks E).card ≤ n := by
  exact Finset.card_image_le.trans_eq (by simp)

theorem blocks_pairwise_disjoint {n r m : ℕ} (E : FactorFamily n r m)
    (hdeg : FamilyPrimalDegreeLe E 1) :
    (blocks E : Set (Finset (Fin n))).PairwiseDisjoint id := by
  intro C hC D hD hne
  apply Finset.disjoint_left.mpr
  intro x hxC hxD
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hD
  exact hne ((block_eq_of_mem E hdeg hxC).symm.trans (block_eq_of_mem E hdeg hxD))

/-- Assign an occurrence to the block of its least scoped coordinate. -/
def owner {n r m : ℕ} (E : FactorFamily n r m) (e : Fin m) : Finset (Fin n) :=
  block E ((E e).scope.min' (E e).nonempty)

def blockFactors {n r m : ℕ} (E : FactorFamily n r m) (C : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter fun e => owner E e = C

theorem owner_mem_blocks {n r m : ℕ} (E : FactorFamily n r m) (e : Fin m) :
    owner E e ∈ blocks E := Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

theorem scope_subset_owner {n r m : ℕ} (E : FactorFamily n r m) (e : Fin m) :
    (E e).scope ⊆ owner E e := by
  intro v hv
  let u := (E e).scope.min' (E e).nonempty
  have hu : u ∈ (E e).scope := Finset.min'_mem _ _
  change v ∈ insert u (primalNeighbors E u)
  by_cases h : v = u
  · exact Finset.mem_insert.mpr (Or.inl h)
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, h, e, hv, hu⟩))

theorem scope_subset_block {n r m : ℕ} (E : FactorFamily n r m)
    {C : Finset (Fin n)} {e : Fin m} (he : e ∈ blockFactors E C) : (E e).scope ⊆ C := by
  have ho := (Finset.mem_filter.mp he).2
  rw [← ho]
  exact scope_subset_owner E e

/-- Bounded occurrence gives at most `2 Δ` factors in every actual block. -/
theorem blockFactors_card_le {n r m Δ : ℕ} (E : FactorFamily n r m)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ)
    {C : Finset (Fin n)} (hC : C ∈ blocks E) : (blockFactors E C).card ≤ 2 * Δ := by
  let incident := fun v => Finset.univ.filter fun e : Fin m => v ∈ (E e).scope
  have hsub : blockFactors E C ⊆ C.biUnion incident := by
    intro e he
    obtain ⟨v, hv⟩ := (E e).nonempty
    exact Finset.mem_biUnion.mpr ⟨v, scope_subset_block E he hv,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
  calc
    (blockFactors E C).card ≤ (C.biUnion incident).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ C, (incident v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ C, Δ := Finset.sum_le_sum fun v _ => hocc v
    _ = C.card * Δ := by simp
    _ ≤ 2 * Δ := Nat.mul_le_mul_right _ (block_card_le_two E hdeg hC)

/-- The original factors in one component, in ambient coordinates. -/
def blockProduct {n r m : ℕ} (E : FactorFamily n r m) (C : Finset (Fin n))
    (x : Fin n → ℝ) : ℝ := ∏ e ∈ blockFactors E C, Factor.ambient (E e) x

def blockIntegral {n r m : ℕ} (E : FactorFamily n r m) (C : Finset (Fin n)) : ℝ :=
  cubeIntegral (blockProduct E C)

theorem blockProduct_depends {n r m : ℕ} (E : FactorFamily n r m)
    (C : Finset (Fin n)) (x y : Fin n → ℝ) (hxy : ∀ v ∈ C, x v = y v) :
    blockProduct E C x = blockProduct E C y := by
  apply Finset.prod_congr rfl
  intro e he
  unfold Factor.ambient pullback
  congr 1
  funext i
  exact hxy _ (scope_subset_block E he ((E e).scope.orderEmbOfFin_mem rfl i))

/-- Fubini factorization for a finite family of disjoint coordinate groups. -/
theorem cubeIntegral_prod_disjoint {n : ℕ} {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (C : ι → Finset (Fin n)) (f : ι → (Fin n → ℝ) → ℝ)
    (hdisj : (S : Set ι).PairwiseDisjoint C)
    (hdep : ∀ i ∈ S, ∀ x y, (∀ v ∈ C i, x v = y v) → f i x = f i y) :
    cubeIntegral (fun x => ∏ i ∈ S, f i x) = ∏ i ∈ S, cubeIntegral (f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hdisjS : (S : Set ι).PairwiseDisjoint C := by
      intro j hj k hk hne
      exact hdisj (by simp [hj]) (by simp [hk]) hne
    have hdepS : ∀ j ∈ S, ∀ x y, (∀ v ∈ C j, x v = y v) → f j x = f j y :=
      fun j hj => hdep j (by simp [hj])
    have hc : Disjoint (C i) (S.biUnion C) := by
      apply Finset.disjoint_left.mpr
      intro v hvi hvS
      obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.mp hvS
      exact Finset.disjoint_left.mp (hdisj (by simp) (by simp [hj]) (by
        intro heq; subst j; exact hi hj)) hvi hvj
    simp only [Finset.prod_insert hi]
    rw [MultiMoments.cubeIntegral_mul_of_depends (C i) (S.biUnion C) hc
      (f i) (fun x => ∏ j ∈ S, f j x) (hdep i (by simp))]
    · rw [ih hdisjS hdepS]
    · intro x y hxy
      apply Finset.prod_congr rfl
      intro j hj
      apply hdepS j hj x y
      intro v hv
      exact hxy v (Finset.mem_biUnion.mpr ⟨j, hj, hv⟩)

/-- The actual partition function factors over the blocks constructed from the
input scopes. This is a proved integral equality, not a partition certificate. -/
theorem partitionFunction_eq_prod_blocks {n r m : ℕ} (E : FactorFamily n r m)
    (hdeg : FamilyPrimalDegreeLe E 1) :
    partitionFunctionFactor E = ∏ C ∈ blocks E, blockIntegral E C := by
  have hprod (x : Fin n → ℝ) : (∏ C ∈ blocks E, blockProduct E C x) =
      ∏ e : Fin m, Factor.ambient (E e) x := by
    exact Finset.prod_fiberwise_of_maps_to (fun e _ => owner_mem_blocks E e)
      (fun e => Factor.ambient (E e) x)
  unfold partitionFunctionFactor partitionFunction blockIntegral
  change cubeIntegral (fun x => ∏ e : Fin m, Factor.ambient (E e) x) = _
  rw [show (fun x => ∏ e : Fin m, Factor.ambient (E e) x) =
      (fun x => ∏ C ∈ blocks E, blockProduct E C x) from funext (fun x => (hprod x).symm)]
  exact cubeIntegral_prod_disjoint (blocks E) id (blockProduct E)
    (blocks_pairwise_disjoint E hdeg) (fun C _ => blockProduct_depends E C)

/-- Only coordinates of the current component are refined. -/
def levels {n : ℕ} (C : Finset (Fin n)) (L : ℕ) (v : Fin n) : ℕ := if v ∈ C then L else 0

lemma sum_levels {n : ℕ} (C : Finset (Fin n)) (L : ℕ) :
    (∑ v, levels C L v) = C.card * L := by
  simp [levels, ← Finset.sum_filter]

theorem grid_card_le {n r m : ℕ} (E : FactorFamily n r m)
    (hdeg : FamilyPrimalDegreeLe E 1) {C : Finset (Fin n)} (hC : C ∈ blocks E) (L : ℕ) :
    Fintype.card (CellGrid.Grid (levels C L)) ≤ 2 ^ (2 * L) := by
  rw [CellGrid.card_grid, sum_levels]
  exact Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right L (block_card_le_two E hdeg hC))

lemma grid_weights_sum {n : ℕ} (C : Finset (Fin n)) (L : ℕ) :
    (∑ _z : CellGrid.Grid (levels C L), (CellGrid.weightQ (levels C L) : ℝ)) = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, CellGrid.card_grid]
  simp [CellGrid.weightQ]

lemma lower_corner {n : ℕ} {a : Fin n → ℕ} (z : CellGrid.Grid a) (v : Fin n) :
    Dyadic.lower (a v) (CellGrid.corner z v) = CellGrid.corner z v := by
  rw [Dyadic.lower, CellGrid.cellIndex_corner, CellGrid.corner_apply]

/-- The exact-sample lower-corner product rule. Its coordinates refine at the
same order as the midpoint rule in Appendix A; the error estimate below keeps
the extra factor explicitly. -/
def exactRule {n r m : ℕ} (E : FactorFamily n r m) (C : Finset (Fin n)) (L : ℕ) : ℝ :=
  ∑ z : CellGrid.Grid (levels C L),
    (CellGrid.weightQ (levels C L) : ℝ) * blockProduct E C (CellGrid.corner z)

def blockStep {n r m : ℕ} (E : FactorFamily n r m) (C : Finset (Fin n)) (L : ℕ)
    (x : Fin n → ℝ) : ℝ :=
  ∏ e ∈ blockFactors E C,
    (Dyadic.step (E e).psi L).toFun (restrictTo (E e).scope x)

lemma blockStep_on_cell {n r m L : ℕ} (E : FactorFamily n r m) (C : Finset (Fin n))
    (z : CellGrid.Grid (levels C L)) (x : Fin n → ℝ) (hx : x ∈ CellGrid.cell (levels C L) z) :
    blockStep E C L x = blockStep E C L (CellGrid.corner z) := by
  apply Finset.prod_congr rfl
  intro e he
  apply congrArg (E e).psi.toFun
  funext j
  apply CellGrid.lower_eq_on_cell hx
  simp [levels, scope_subset_block E he ((E e).scope.orderEmbOfFin_mem rfl j)]

lemma blockStep_at_corner {n r m L : ℕ} (E : FactorFamily n r m) (C : Finset (Fin n))
    (z : CellGrid.Grid (levels C L)) :
    blockStep E C L (CellGrid.corner z) = blockProduct E C (CellGrid.corner z) := by
  apply Finset.prod_congr rfl
  intro e he
  apply congrArg (E e).psi.toFun
  funext j
  let v := (E e).scope.orderEmbOfFin rfl j
  have hv : v ∈ C := scope_subset_block E he ((E e).scope.orderEmbOfFin_mem rfl j)
  change Dyadic.lower L (CellGrid.corner z v) = CellGrid.corner z v
  simpa only [levels, if_pos hv] using lower_corner z v

lemma exactRule_eq_integral_step {n r m : ℕ} (E : FactorFamily n r m)
    (C : Finset (Fin n)) (L : ℕ) : exactRule E C L = cubeIntegral (blockStep E C L) := by
  rw [CellGrid.cubeIntegral_eq_cell_sum (levels C L) _ (blockStep_on_cell E C)]
  unfold exactRule
  apply Finset.sum_congr rfl
  intro z _
  rw [blockStep_at_corner]

theorem exactRule_error {n r m : ℕ} (E : FactorFamily n r m)
    (hdeg : FamilyPrimalDegreeLe E 1) {C : Finset (Fin n)} (hC : C ∈ blocks E) (L : ℕ)
    {U K : ℝ} (hU : 0 ≤ U) (hK : 0 ≤ K)
    (hbound : ∀ e, (E e).psi.BoundBy U) (hLip : ∀ e, (E e).LipOk K) :
    |exactRule E C L - blockIntegral E C| ≤
      (blockFactors E C).card * U ^ ((blockFactors E C).card - 1) *
        (Real.sqrt 2 * K * ((2 : ℝ) ^ L)⁻¹) := by
  have hstep : IntegrableOn (blockStep E C L) (cube n) := by
    apply integrableOn_cube_of_bound
    · exact Finset.measurable_prod _ (fun e _ =>
        (Dyadic.measurable_step (E e).psi L).comp (measurable_restrictTo _))
    · intro x hx
      exact SmallDegree.abs_product_le _ _ hU (fun e _ =>
        Dyadic.step_bound (level := L) (hbound e) _ (mem_cube.mp (restrictTo_mem_cube _ hx)))
  have htrue : IntegrableOn (blockProduct E C) (cube n) := by
    have hcont : ContinuousOn (blockProduct E C) (cube n) :=
      continuousOn_finset_prod _ fun e _ =>
        (ZeroFree.continuousOn_of_lip (E e).psi (hLip e)).comp
          (ZeroFree.continuous_restrictTo _).continuousOn (fun _ hx => restrictTo_mem_cube _ hx)
    exact hcont.integrableOn_compact (ZeroFree.isCompact_cube n)
  rw [exactRule_eq_integral_step]
  apply abs_cubeIntegral_sub_le hstep htrue
  intro x hx
  apply SmallDegree.product_perturbation _ _ _ hU (by positivity)
  · intro e he
    exact Dyadic.step_bound (level := L) (hbound e) _ (mem_cube.mp (restrictTo_mem_cube _ hx))
  · intro e he
    exact hbound e _ (mem_cube.mp (restrictTo_mem_cube _ hx))
  · intro e he
    have hcard : (E e).scope.card ≤ 2 :=
      (Finset.card_le_card (scope_subset_block E he)).trans (block_card_le_two E hdeg hC)
    have hsqrt : Real.sqrt ((E e).scope.card : ℝ) ≤ Real.sqrt 2 :=
      Real.sqrt_le_sqrt (by exact_mod_cast hcard)
    exact (Dyadic.step_error hK (hLip e) (restrictTo_mem_cube _ hx)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsqrt hK) (by positivity))

/-- Rational projection onto the known fixed range. -/
def projectQ (U : ℕ) (y : ℚ) : ℚ := min (U : ℚ) (max 1 y)

lemma project_range (U : ℕ) (hU : 1 ≤ U) (y : ℚ) : 1 ≤ projectQ U y ∧ projectQ U y ≤ U := by
  exact ⟨le_min (by exact_mod_cast hU) (le_max_left _ _), min_le_left _ _⟩

lemma project_error (U : ℕ) (y z : ℝ) (hz : 1 ≤ z) (hUz : z ≤ U) :
    |min (U : ℝ) (max 1 y) - z| ≤ |y - z| := by
  have hleft : |max 1 y - z| ≤ |y - z| := by
    rcases le_total y 1 with hy | hy
    · rw [max_eq_left hy, abs_of_nonpos (by linarith : (1 : ℝ) - z ≤ 0),
        abs_of_nonpos (by linarith : y - z ≤ 0)]
      linarith
    · rw [max_eq_right hy]
  apply le_trans _ hleft
  rcases le_total (max 1 y) U with hy | hy
  · rw [min_eq_right hy]
  · rw [min_eq_left hy, abs_of_nonneg (by linarith : (U : ℝ) - z ≥ 0),
      abs_of_nonneg (by linarith : max 1 y - z ≥ 0)]
    linarith

/-- The actual rational oracle point for a factor in a component cell. -/
def localPointQ {n r m L : ℕ} (E : FactorFamily n r m) (C : Finset (Fin n))
    (z : CellGrid.Grid (levels C L)) (e : Fin m) : Fin (E e).scope.card → ℚ :=
  fun j => CellGrid.cornerQ z ((E e).scope.orderEmbOfFin rfl j)

lemma localPointQ_mem {n r m L : ℕ} (E : FactorFamily n r m) (C : Finset (Fin n))
    (z : CellGrid.Grid (levels C L)) (e : Fin m) :
    ∀ j, 0 ≤ localPointQ E C z e j ∧ localPointQ E C z e j ≤ 1 := by
  intro j
  have hx := mem_cube.mp (CellGrid.cell_subset_cube _ _ (CellGrid.corner_mem_cell z))
  have h := hx ((E e).scope.orderEmbOfFin rfl j)
  change (0 : ℝ) ≤ (localPointQ E C z e j : ℝ) ∧ (localPointQ E C z e j : ℝ) ≤ 1 at h
  exact_mod_cast h

/-- One rounded, projected oracle answer, with a prescribed common dyadic denominator. -/
def sampleQ {n r m L : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (U b : ℕ) (C : Finset (Fin n)) (z : CellGrid.Grid (levels C L)) (e : Fin m) : ℚ :=
  projectQ U (Oracle.dyadQ b (query e (localPointQ E C z e) b))

/-- The actual rational component rule, using only rational coordinates and arithmetic. -/
def componentEstimateQ {n r m : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (U b L : ℕ) (C : Finset (Fin n)) : ℚ :=
  ∑ z : CellGrid.Grid (levels C L), CellGrid.weightQ (levels C L) *
    ∏ e ∈ blockFactors E C, sampleQ E query U b C z e

def outputQ {n r m : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (U b L : ℕ) : ℚ := ∏ C ∈ blocks E, componentEstimateQ E query U b L C

lemma sampleQ_error {n r m L : ℕ} (E : FactorFamily n r m)
    (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
    (U b : ℕ) (hb : 1 ≤ b) (C : Finset (Fin n)) (z : CellGrid.Grid (levels C L)) (e : Fin m)
    (hrange : ∀ x, x ∈ cube (E e).scope.card →
      1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ U) :
    |(sampleQ E (fun e => (O e).query) U b C z e : ℝ) - Factor.ambient (E e) (CellGrid.corner z)| ≤
      2 * (2 : ℝ) ^ (-(b : ℝ)) := by
  let p := localPointQ E C z e
  have hp := localPointQ_mem E C z e
  have hc : (fun j => (p j : ℝ)) = restrictTo (E e).scope (CellGrid.corner z) := rfl
  have hr := hrange _ (restrictTo_mem_cube _
    (CellGrid.cell_subset_cube _ _ (CellGrid.corner_mem_cell z)))
  have ho := (O e).query_approx p b hp hb
  have hd := Oracle.abs_dyadQ_sub_le b ((O e).query p b)
  change |((projectQ U (Oracle.dyadQ b ((O e).query p b)) : ℚ) : ℝ) - _| ≤ _
  simp only [projectQ, Rat.cast_min, Rat.cast_natCast, Rat.cast_max, Rat.cast_one]
  apply (project_error U _ _ hr.1 hr.2).trans
  have htri := abs_sub_le (Oracle.dyadQ b ((O e).query p b) : ℝ)
    (((O e).query p b : ℚ) : ℝ) (Factor.ambient (E e) (CellGrid.corner z))
  have ho' : |(((O e).query p b : ℚ) : ℝ) - Factor.ambient (E e) (CellGrid.corner z)| ≤
      (2 : ℝ) ^ (-(b : ℝ)) := by simpa only [hc] using ho
  change |(Oracle.dyadQ b ((O e).query p b) : ℝ) - Factor.ambient (E e) (CellGrid.corner z)| ≤ _
  linarith

lemma weighted_error {ι : Type*} [Fintype ι] (w : ℝ) (hw : 0 ≤ w)
    (hsum : (∑ _i : ι, w) = 1) (f g : ι → ℝ) {δ : ℝ}
    (herr : ∀ i, |f i - g i| ≤ δ) :
    |(∑ i, w * f i) - ∑ i, w * g i| ≤ δ := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |w * f i - w * g i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, w * |f i - g i| := by simp_rw [← mul_sub, abs_mul, abs_of_nonneg hw]
    _ ≤ ∑ _i : ι, w * δ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (herr i) hw
    _ = (∑ _i : ι, w) * δ := (Finset.sum_mul _ _ _).symm
    _ = δ := by rw [hsum, one_mul]

/-- Finite precision error of the actual rational rule, relative to exact samples. -/
theorem componentEstimateQ_sample_error {n r m : ℕ} (E : FactorFamily n r m)
    (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
    (U b L : ℕ) (hU : 1 ≤ U) (hb : 1 ≤ b) (C : Finset (Fin n))
    (hrange : ∀ e x, x ∈ cube (E e).scope.card →
      1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ U) :
    |(componentEstimateQ E (fun e => (O e).query) U b L C : ℝ) - exactRule E C L| ≤
      (blockFactors E C).card * (U : ℝ) ^ ((blockFactors E C).card - 1) *
        (2 * (2 : ℝ) ^ (-(b : ℝ))) := by
  unfold componentEstimateQ exactRule
  push_cast
  apply weighted_error _ (by simp only [CellGrid.weightQ, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat]; positivity) (grid_weights_sum C L)
  intro z
  apply SmallDegree.product_perturbation _ _ _ (Nat.cast_nonneg U) (by positivity)
  · intro e he
    rw [abs_of_nonneg (by exact_mod_cast (project_range U hU _).1.trans' (by norm_num : (0 : ℚ) ≤ 1))]
    exact_mod_cast (project_range U hU _).2
  · intro e he
    have hr := hrange e _ (restrictTo_mem_cube _
      (CellGrid.cell_subset_cube _ _ (CellGrid.corner_mem_cell z)))
    change |(E e).psi.toFun (restrictTo (E e).scope (CellGrid.corner z))| ≤ _
    exact abs_le.mpr ⟨by linarith [hr.1], hr.2⟩
  · intro e he
    exact sampleQ_error E O U b hb C z e (hrange e)

lemma one_le_real_prod {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 1 ≤ f i) : 1 ≤ ∏ i ∈ S, f i := by
  apply Finset.prod_induction (p := fun z : ℝ => 1 ≤ z)
  · intro a b ha hb; nlinarith
  · norm_num
  · exact hf

theorem componentEstimateQ_ge_one {n r m : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (U b L : ℕ) (hU : 1 ≤ U) (C : Finset (Fin n)) :
    1 ≤ (componentEstimateQ E query U b L C : ℝ) := by
  unfold componentEstimateQ
  push_cast
  rw [← grid_weights_sum C L]
  apply Finset.sum_le_sum
  intro z _
  apply le_mul_of_one_le_right
  · simp only [CellGrid.weightQ, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat]
    positivity
  · apply one_le_real_prod
    intro e he
    exact_mod_cast (project_range U hU _).1

lemma blockIntegral_ge_one {n r m : ℕ} (E : FactorFamily n r m)
    (C : Finset (Fin n)) {K : ℝ} (hLip : ∀ e, (E e).LipOk K)
    (hlo : ∀ e x, x ∈ cube (E e).scope.card → 1 ≤ (E e).psi.toFun x) :
    1 ≤ blockIntegral E C := by
  apply le_cubeIntegral
  · have hcont : ContinuousOn (blockProduct E C) (cube n) :=
      continuousOn_finset_prod _ fun e _ =>
        (ZeroFree.continuousOn_of_lip (E e).psi (hLip e)).comp
          (ZeroFree.continuous_restrictTo _).continuousOn (fun _ hx => restrictTo_mem_cube _ hx)
    exact hcont.integrableOn_compact (ZeroFree.isCompact_cube n)
  · intro x hx
    exact one_le_real_prod _ _ fun e _ => hlo e _ (restrictTo_mem_cube _ hx)

lemma product_budget_mono {t a U : ℕ} (ht : t ≤ a) (hU : 1 ≤ U) :
    (t : ℝ) * (U : ℝ) ^ (t - 1) ≤ (a : ℝ) * (U : ℝ) ^ (a - 1) := by
  apply mul_le_mul (by exact_mod_cast ht)
    (pow_le_pow_right₀ (by exact_mod_cast hU) (by omega)) (by positivity) (by positivity)

/-- Accuracy of one actual rational component rule. The two terms are the
finite-precision oracle error and the geometric mesh error. -/
theorem componentEstimateQ_error {n r m Δ : ℕ} (E : FactorFamily n r m)
    (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ)
    (U b L T : ℕ) (hU : 1 ≤ U) (hb : 1 ≤ b) {K : ℝ} (hK : 0 ≤ K)
    (hrange : ∀ e x, x ∈ cube (E e).scope.card →
      1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ U)
    (hLip : ∀ e, (E e).LipOk K)
    (hT : (2 * Δ : ℕ) * K * (U : ℝ) ^ (2 * Δ - 1) ≤ T)
    {C : Finset (Fin n)} (hC : C ∈ blocks E) :
    |(componentEstimateQ E (fun e => (O e).query) U b L C : ℝ) - blockIntegral E C| ≤
      (2 * Δ : ℕ) * (U : ℝ) ^ (2 * Δ - 1) * (2 * (2 : ℝ) ^ (-(b : ℝ))) +
        2 * T * ((2 : ℝ) ^ L)⁻¹ := by
  have hcount := blockFactors_card_le E hdeg hocc hC
  have hbudget := product_budget_mono hcount hU
  have hbnd : ∀ e, (E e).psi.BoundBy (U : ℝ) := by
    intro e x hx
    have hr := hrange e x (mem_cube.mpr hx)
    exact abs_le.mpr ⟨by linarith [hr.1], hr.2⟩
  have hsample := componentEstimateQ_sample_error E O U b L hU hb C hrange
  have hexact := exactRule_error E hdeg hC L (Nat.cast_nonneg U) hK hbnd hLip
  have hmesh : (blockFactors E C).card * (U : ℝ) ^ ((blockFactors E C).card - 1) *
      (Real.sqrt 2 * K * ((2 : ℝ) ^ L)⁻¹) ≤ 2 * T * ((2 : ℝ) ^ L)⁻¹ := by
    have hTK : ((blockFactors E C).card : ℝ) * (U : ℝ) ^ ((blockFactors E C).card - 1) * K ≤ T := by
      have h := mul_le_mul_of_nonneg_right hbudget hK
      nlinarith [hT]
    have hsqrt : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    calc
      _ = (((blockFactors E C).card : ℝ) * (U : ℝ) ^ ((blockFactors E C).card - 1) * K) *
          (Real.sqrt 2 * ((2 : ℝ) ^ L)⁻¹) := by ring
      _ ≤ T * (Real.sqrt 2 * ((2 : ℝ) ^ L)⁻¹) :=
        mul_le_mul_of_nonneg_right hTK (by positivity)
      _ ≤ 2 * T * ((2 : ℝ) ^ L)⁻¹ := by
        have hh := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrt (Nat.cast_nonneg T))
          (by positivity : 0 ≤ ((2 : ℝ) ^ L)⁻¹)
        convert hh using 1 <;> ring
  calc
    _ ≤ |(componentEstimateQ E (fun e => (O e).query) U b L C : ℝ) - exactRule E C L| +
        |exactRule E C L - blockIntegral E C| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add
      (hsample.trans (mul_le_mul_of_nonneg_right hbudget (by positivity))) (hexact.trans hmesh)

/-- The direct low-degree algorithm approximates the original partition function.
The mesh and precision inequalities are numeric choices for the explicit program. -/
theorem outputQ_accurate {n r m Δ : ℕ} (E : FactorFamily n r m)
    (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ)
    (U b L T : ℕ) (hU : 1 ≤ U) (hb : 1 ≤ b) (hn : 0 < n) {K ε : ℝ}
    (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hrange : ∀ e x, x ∈ cube (E e).scope.card →
      1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ U)
    (hLip : ∀ e, (E e).LipOk K)
    (hT : (2 * Δ : ℕ) * K * (U : ℝ) ^ (2 * Δ - 1) ≤ T)
    (hmesh : 2 * T * ((2 : ℝ) ^ L)⁻¹ ≤ ε / (2 * n))
    (hprecision : (2 * Δ : ℕ) * (U : ℝ) ^ (2 * Δ - 1) *
      (2 * (2 : ℝ) ^ (-(b : ℝ))) ≤ ε / (2 * n)) :
    FPTAS.Accurate (outputQ E (fun e => (O e).query) U b L : ℝ) (partitionFunctionFactor E) ε := by
  have hI : ∀ C ∈ blocks E, 1 ≤ blockIntegral E C :=
    fun C _ => blockIntegral_ge_one E C hLip (fun e x hx => (hrange e x hx).1)
  have hhat : ∀ C ∈ blocks E, 1 ≤ (componentEstimateQ E (fun e => (O e).query) U b L C : ℝ) :=
    fun C _ => componentEstimateQ_ge_one E _ U b L hU C
  have herr : ∀ C ∈ blocks E,
      |(componentEstimateQ E (fun e => (O e).query) U b L C : ℝ) - blockIntegral E C| ≤ ε / n := by
    intro C hC
    apply (componentEstimateQ_error E O hdeg hocc U b L T hU hb hK hrange hLip hT hC).trans
    have h := add_le_add hprecision hmesh
    convert h using 1 <;> field_simp <;> ring
  have hlog := SmallDegree.component_accuracy (blocks E) (blockIntegral E)
    (fun C => (componentEstimateQ E (fun e => (O e).query) U b L C : ℝ)) hn
    (blocks_card_le E) hε hI hhat herr
  rw [partitionFunction_eq_prod_blocks E hdeg]
  unfold outputQ
  push_cast
  exact ⟨Finset.prod_pos (fun C hC => lt_of_lt_of_le zero_lt_one (hI C hC)),
    Finset.prod_pos (fun C hC => lt_of_lt_of_le zero_lt_one (hhat C hC)), hlog⟩

/-- The actual number of oracle calls in the uncached component/grid loops. -/
def queryCalls {n r m : ℕ} (E : FactorFamily n r m) (L : ℕ) : ℕ :=
  ∑ C ∈ blocks E, Fintype.card (CellGrid.Grid (levels C L)) * (blockFactors E C).card

theorem queryCalls_le {n r m Δ : ℕ} (E : FactorFamily n r m)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ) (L : ℕ) :
    queryCalls E L ≤ n * (2 * Δ) * 2 ^ (2 * L) := by
  calc
    queryCalls E L ≤ ∑ _C ∈ blocks E, 2 ^ (2 * L) * (2 * Δ) := by
      apply Finset.sum_le_sum
      intro C hC
      exact Nat.mul_le_mul (grid_card_le E hdeg hC L) (blockFactors_card_le E hdeg hocc hC)
    _ = (blocks E).card * (2 ^ (2 * L) * (2 * Δ)) := by simp
    _ ≤ n * (2 ^ (2 * L) * (2 * Δ)) := Nat.mul_le_mul_right _ (blocks_card_le E)
    _ = _ := by ring

/-- Effective precision selection by rational comparison and integer ceiling/logarithm. -/
def dyadicPrecision (A : ℕ) (ε : ℚ) : ℕ := max 1 (Nat.clog 2 ⌈(A : ℚ) / ε⌉₊)

lemma dyadicPrecision_pos (A : ℕ) (ε : ℚ) : 1 ≤ dyadicPrecision A ε := le_max_left _ _

theorem dyadicPrecision_error (A : ℕ) (ε : ℚ) (hε : 0 < ε) :
    (A : ℝ) * ((2 : ℝ) ^ dyadicPrecision A ε)⁻¹ ≤ (ε : ℝ) := by
  have hceil : (A : ℚ) / ε ≤ (⌈(A : ℚ) / ε⌉₊ : ℚ) := Nat.le_ceil _
  have hpow : ⌈(A : ℚ) / ε⌉₊ ≤ 2 ^ dyadicPrecision A ε :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp (le_max_right _ _)
  have hq : (A : ℚ) / (2 : ℚ) ^ dyadicPrecision A ε ≤ ε := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hpowq : (⌈(A : ℚ) / ε⌉₊ : ℚ) ≤ (2 : ℚ) ^ dyadicPrecision A ε := by exact_mod_cast hpow
    have h := (div_le_iff₀ hε).mp (hceil.trans hpowq)
    nlinarith
  have hr := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast at hr
  simpa only [div_eq_mul_inv] using hr

/-- Exponentiation of the selected logarithmic precision is at most linear in
the rational ceiling; this makes the two-dimensional grid polynomial. -/
theorem dyadicPrecision_pow_le (A : ℕ) (ε : ℚ) :
    2 ^ dyadicPrecision A ε ≤ 2 * (⌈(A : ℚ) / ε⌉₊ + 1) := by
  let N := ⌈(A : ℚ) / ε⌉₊
  change 2 ^ max 1 (Nat.clog 2 N) ≤ 2 * (N + 1)
  by_cases hN : N ≤ 1
  · rw [Nat.clog_of_right_le_one hN]
    norm_num
  · have hpos := Nat.clog_pos (by decide : 1 < 2) (show 2 ≤ N by omega)
    rw [max_eq_right hpos]
    have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (show 1 < N by omega)
    simp only [Nat.pred_eq_sub_one] at hpred
    rw [show Nat.clog 2 N = (Nat.clog 2 N - 1) + 1 by omega, pow_succ]
    nlinarith

def meshLevel (T n : ℕ) (ε : ℚ) : ℕ := dyadicPrecision (4 * T * n) ε

def answerBits (Δ U n : ℕ) (ε : ℚ) : ℕ :=
  dyadicPrecision (4 * (2 * Δ) * U ^ (2 * Δ - 1) * n) ε

/-- The complete rational direct algorithm for the nonempty-variable case. -/
def runQ {n r m : ℕ} (E : FactorFamily n r m)
    (query : (e : Fin m) → (Fin (E e).scope.card → ℚ) → ℕ → ℚ)
    (Δ U T : ℕ) (ε : ℚ) : ℚ :=
  outputQ E query U (answerBits Δ U n ε) (meshLevel T n ε)

lemma two_rpow_neg_nat (b : ℕ) : (2 : ℝ) ^ (-(b : ℝ)) = ((2 : ℝ) ^ b)⁻¹ := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]

/-- Lemma A.1 accuracy with all grid/precision choices performed by the program. -/
theorem runQ_accurate {n r m Δ : ℕ} (E : FactorFamily n r m)
    (O : (e : Fin m) → Oracle.Oracle (E e).scope.card (E e).psi.toFun)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ)
    (U T : ℕ) (hU : 1 ≤ U) (hn : 0 < n) {K : ℝ} (hK : 0 ≤ K)
    (hrange : ∀ e x, x ∈ cube (E e).scope.card →
      1 ≤ (E e).psi.toFun x ∧ (E e).psi.toFun x ≤ U)
    (hLip : ∀ e, (E e).LipOk K)
    (hT : (2 * Δ : ℕ) * K * (U : ℝ) ^ (2 * Δ - 1) ≤ T)
    (ε : ℚ) (hε : 0 < ε) :
    FPTAS.Accurate (runQ E (fun e => (O e).query) Δ U T ε : ℝ) (partitionFunctionFactor E) ε := by
  apply outputQ_accurate E O hdeg hocc U (answerBits Δ U n ε) (meshLevel T n ε) T
    hU (dyadicPrecision_pos _ _) hn hK (by exact_mod_cast hε.le) hrange hLip hT
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
    have h := dyadicPrecision_error (4 * T * n) ε hε
    simp only [meshLevel]
    convert h using 1 <;> push_cast <;> ring
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
    rw [two_rpow_neg_nat]
    have h := dyadicPrecision_error (4 * (2 * Δ) * U ^ (2 * Δ - 1) * n) ε hε
    simp only [answerBits]
    convert h using 1 <;> push_cast <;> ring

/-- A polynomial bound on the concrete algorithm's oracle calls, with a ceiling
of a rational linear function of `n/ε`. -/
theorem runQ_queryCalls_le {n r m Δ : ℕ} (E : FactorFamily n r m)
    (hdeg : FamilyPrimalDegreeLe E 1) (hocc : FamilyBoundedOccurrence E Δ) (T : ℕ) (ε : ℚ) :
    queryCalls E (meshLevel T n ε) ≤
      n * (2 * Δ) * (2 * (⌈((4 * T * n : ℕ) : ℚ) / ε⌉₊ + 1)) ^ 2 := by
  apply (queryCalls_le E hdeg hocc _).trans
  apply Nat.mul_le_mul_left
  rw [Nat.mul_comm 2 _, pow_mul]
  exact Nat.pow_le_pow_left (dyadicPrecision_pow_le (4 * T * n) ε) 2

end Paper08.LowDegreeAlgorithm
