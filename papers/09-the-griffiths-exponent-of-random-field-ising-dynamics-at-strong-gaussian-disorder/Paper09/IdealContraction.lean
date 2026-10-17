import Paper09.RFIMBlocks
import Paper09.ColorInfluence
import Paper09.UpperParameters

open Finset BigOperators Classical Real Filter
open Paper09.LatticeGeometry Paper09.BlockCovering Paper09.BlockColoring Paper09.BlockDynamics
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

namespace Paper09.IdealContraction

local instance (priority := 2000) idealVolumeDecidableEq {d n : ℕ} :
    DecidableEq ↥(volume (d := d) n) := Classical.decEq _

/-- The source good label at the actual covering scale `R=8s`. -/
def sourceGood {d : ℕ} (K β : ℝ) (s : ℕ) (h : Point d → ℝ) : Point d → Prop :=
  Percolation.goodLabel K (rho K d β) (8*s) (Percolation.initialRadius (8*s)) s h

theorem near_mem_labelCube {d s : ℕ} {y v : Point d}
    (hy : Near (8*s) y (center s v)) :
    y ∈ Percolation.latticeCube (Percolation.coarseCenter (8*s) v) (8*s) := by
  apply Percolation.mem_latticeCube.mpr
  intro j
  simpa only [center, Percolation.coarseCenter, mul_comm] using hy j

/-- Covering geometry supplies an actual source-good root for every physical
block-boundary perturbation. No good-root or influence certificate is supplied. -/
theorem boundary_source_good {d n s L : ℕ} (K β : ℝ) (h : Point d → ℝ)
    (hs : 0 < s) (hevent : SmallClusters (sourceGood K β s h) n s L)
    (i : BlockIndex (sourceGood K β s h) n s) (y : ↥(volume (d := d) n))
    (hy : y ∈ (RFIM.domainLattice (volume n)).boundary (blockSites i)) :
    ∃ v : Point d, sourceGood K β s h v ∧
      y.val ∈ Percolation.latticeCube (Percolation.coarseCenter (8*s) v) (8*s) := by
  rw [RFIMBlocks.domain_boundary_blockSites, mem_boundarySites] at hy
  obtain ⟨v, hv, hyv⟩ := block_boundary_good hs hevent i hy
  exact ⟨v, hv, near_mem_labelCube hyv⟩

/-- Actual closure coloring, transported to the finite-domain graph. -/
theorem same_color_domain_disjoint {d n s Q : ℕ} {good : Point d → Prop}
    (c : (conflictGraph good n s).Coloring (Fin Q))
    (i j : BlockIndex good n s) (hij : i ≠ j) (hc : c i = c j) :
    Disjoint (ColorInfluence.closure (RFIM.domainLattice (volume n)) (blockSites i))
      (ColorInfluence.closure (RFIM.domainLattice (volume n)) (blockSites j)) := by
  apply Finset.disjoint_left.mpr
  intro y hyi hyj
  exact Finset.disjoint_left.mp (same_color_closures_disjoint c hij hc)
    ((RFIMBlocks.mem_domain_closure i y).mp hyi)
    ((RFIMBlocks.mem_domain_closure j y).mp hyj)

theorem idealClass_stepBudget {d n s L Q : ℕ}
    (K β : ℝ) (h : Point d → ℝ) (hβ : 0 ≤ β)
    (hs : 0 < s) (hr₀ : 0 < Percolation.initialRadius (8*s))
    (hrs : Percolation.initialRadius (8*s) ≤ s)
    (hevent : SmallClusters (sourceGood K β s h) n s L)
    (c : (conflictGraph (sourceGood K β s h) n s).Coloring (Fin Q))
    (η ξ : Config ↥(volume (d := d) n)) (y : ↥(volume (d := d) n))
    (hy : η y ≠ ξ y) (hrest : ∀ z, z ≠ y → η z = ξ z) (a : Fin Q) :
    hammingWasserstein (RFIMBlocks.idealClass h β c a η) (RFIMBlocks.idealClass h β c a ξ) ≤
      stepBudget (fun i => c i) blockSites boundarySites
        (UpperParameters.rootInfluence (rho K d β) (8*s) s
          (maxBlockSize (sourceGood K β s h) n s)) a y := by
  have hM (i : BlockIndex (sourceGood K β s h) n s) :
      (blockSites i).card ≤ maxBlockSize (sourceGood K β s h) n s := by
    rw [RFIMBlocks.card_blockSites]
    exact Finset.le_sup (f := fun i : BlockIndex (sourceGood K β s h) n s => (block i).card) (mem_univ i)
  have hb := ColorInfluence.color_stepBudget (RFIM.domainLattice (volume n)) h K β
    Subtype.val Subtype.val_injective (by intro x z hxz; exact hxz)
    (fun i => c i) blockSites (same_color_domain_disjoint c)
    (8*s) (Percolation.initialRadius (8*s)) s (maxBlockSize (sourceGood K β s h) n s)
    hr₀ hrs hM η ξ y hy hrest hβ (by simp [RFIM.domainLattice])
    (boundary_source_good K β h hs hevent · y) a
  simp only [RFIMBlocks.idealClass, RFIMBlocks.volumeLaw, RFIM.freeGibbs,
    RFIMBlocks.retainedSites, classIndices, ColorInfluence.colorSites, ColorInfluence.selectedSites,
    RFIMBlocks.domain_boundary_blockSites, ColorInfluence.goodRootBudget,
    UpperParameters.rootInfluence] at hb ⊢
  convert hb using 1
  congr 3
  all_goals
    ext i
    simp

/-- Equation (3.15) for the actual ideal uniform-color conditional kernel.
The incidence counts and boundary influence are all derived from the physical
covering, actual Gibbs exploration, and source good labels. -/
theorem ideal_one_site_budget {d n s L Q : ℕ} [NeZero Q] (hQ : 0 < Q)
    (K β : ℝ) (h : Point d → ℝ) (hβ : 0 ≤ β)
    (hs : 0 < s) (hr₀ : 0 < Percolation.initialRadius (8*s))
    (hrs : Percolation.initialRadius (8*s) ≤ s)
    (hevent : SmallClusters (sourceGood K β s h) n s L)
    (c : (conflictGraph (sourceGood K β s h) n s).Coloring (Fin Q))
    (η ξ : Config ↥(volume (d := d) n)) (y : ↥(volume (d := d) n))
    (hy : η y ≠ ξ y) (hrest : ∀ z, z ≠ y → η z = ξ z) :
    hammingWasserstein
        (colorKernel (RFIMBlocks.idealClass h β c) η)
        (colorKernel (RFIMBlocks.idealClass h β c) ξ) ≤
      1 - (I (sourceGood K β s h) n s y.val : ℝ)/Q +
        UpperParameters.rootInfluence (rho K d β) (8*s) s
          (maxBlockSize (sourceGood K β s h) n s) *
          (J (sourceGood K β s h) n s y.val : ℝ)/Q := by
  exact covering_color_one_site hQ hs hevent c _ (RFIMBlocks.idealClass h β c) η ξ y
    (idealClass_stepBudget K β h hβ hs hr₀ hrs hevent c η ξ y hy hrest)

/-- The exact canonical sampled-color ideal kernel on the proved covering. -/
def canonicalKernel {d n s L : ℕ} (K β : ℝ) (h : Point d → ℝ)
    (hs : 0 < s) (hevent : SmallClusters (sourceGood K β s h) n s L) :
    Config ↥(volume (d := d) n) → FinProb (Config ↥(volume (d := d) n)) :=
  letI : NeZero (colorCount (sourceGood K β s h) n s) := ⟨(colorCount_pos hs hevent).ne'⟩
  colorKernel (RFIMBlocks.idealClass h β (coloring hs hevent))

/-- The paper's exact `I_y/Q` erasure and `H_R J_y/Q` creation budget for
the fixed canonical coloring, before any incidence gain is discarded. -/
theorem canonical_one_site_budget {d n s L : ℕ}
    (K β : ℝ) (h : Point d → ℝ) (hβ : 0 ≤ β)
    (hs : 0 < s) (hr₀ : 0 < Percolation.initialRadius (8*s))
    (hrs : Percolation.initialRadius (8*s) ≤ s)
    (hevent : SmallClusters (sourceGood K β s h) n s L)
    (η ξ : Config ↥(volume (d := d) n)) (y : ↥(volume (d := d) n))
    (hy : η y ≠ ξ y) (hrest : ∀ z, z ≠ y → η z = ξ z) :
    hammingWasserstein (canonicalKernel K β h hs hevent η) (canonicalKernel K β h hs hevent ξ) ≤
      1 - (I (sourceGood K β s h) n s y.val : ℝ)/colorCount (sourceGood K β s h) n s +
        UpperParameters.rootInfluence (rho K d β) (8*s) s
          (maxBlockSize (sourceGood K β s h) n s) *
          (J (sourceGood K β s h) n s y.val : ℝ)/colorCount (sourceGood K β s h) n s := by
  have hQ := colorCount_pos hs hevent
  letI : NeZero (colorCount (sourceGood K β s h) n s) := ⟨hQ.ne'⟩
  exact ideal_one_site_budget hQ K β h hβ hs hr₀ hrs hevent (coloring hs hevent)
    η ξ y hy hrest

/-- With the influence budget absorbed, the canonical physical covering gives
the uniform incidence gain `c/M` for every initial single-site discrepancy. -/
theorem canonical_one_site {d n s L : ℕ}
    (K β : ℝ) (h : Point d → ℝ) (hβ : 0 ≤ β)
    (hs : 0 < s) (hr₀ : 0 < Percolation.initialRadius (8*s))
    (hrs : Percolation.initialRadius (8*s) ≤ s)
    (hevent : SmallClusters (sourceGood K β s h) n s L)
    (hHJ : ∀ y ∈ volume n,
      UpperParameters.rootInfluence (rho K d β) (8*s) s
        (maxBlockSize (sourceGood K β s h) n s) *
        (J (sourceGood K β s h) n s y : ℝ) ≤ (I (sourceGood K β s h) n s y : ℝ)/2)
    (η ξ : Config ↥(volume (d := d) n)) (y : ↥(volume (d := d) n))
    (hy : η y ≠ ξ y) (hrest : ∀ z, z ≠ y → η z = ξ z) :
    hammingWasserstein (canonicalKernel K β h hs hevent η) (canonicalKernel K β h hs hevent ξ) ≤
      1 - coveringRate d / maxBlockSize (sourceGood K β s h) n s := by
  let good := sourceGood K β s h
  let Q := colorCount good n s
  let M := maxBlockSize good n s
  let H := UpperParameters.rootInfluence (rho K d β) (8*s) s M
  have hQn : 0 < Q := colorCount_pos hs hevent
  letI : NeZero Q := ⟨hQn.ne'⟩
  have hQ : (0 : ℝ) < Q := Nat.cast_pos.mpr hQn
  have hb := ideal_one_site_budget hQn K β h hβ hs hr₀ hrs hevent
    (coloring hs hevent) η ξ y hy hrest
  have hI : (0 : ℝ) < I good n s y.val := by
    exact_mod_cast (lt_of_lt_of_le (pow_pos (show 0 < 2*s+1 by omega) _)
      (covering_lower hs hevent y.property))
  have hJ : (0 : ℝ) ≤ J good n s y.val := Nat.cast_nonneg _
  have hρ := rho_pos K d β
  have hH : 0 ≤ H := by dsimp [H, UpperParameters.rootInfluence]; positivity
  have habs := ideal_step_one_site (I good n s y.val) (J good n s y.val) Q H
    hI hQ hJ hH (hHJ y.val y.property)
  have hinc := covering_incidence_ratio hs hevent y
  have heq : (I good n s y.val : ℝ)/(2*Q) = 2*((I good n s y.val : ℝ)/(4*Q)) := by ring
  have hn : 0 ≤ (I good n s y.val : ℝ)/(4*Q) := by positivity
  change hammingWasserstein _ _ ≤ 1 - coveringRate d / M
  change hammingWasserstein _ _ ≤
    1 - (I good n s y.val : ℝ)/Q + H*(J good n s y.val : ℝ)/Q at hb
  change coveringRate d / M ≤ (I good n s y.val : ℝ)/(4*Q) at hinc
  exact hb.trans (by linarith)

/-- Full pairwise ideal-step contraction from the actual one-site couplings
along shortest Hamming paths; the sole intermediate numeric premise is the
influence/overlap absorption which the source scales prove below. -/
theorem canonical_all_pair {d n s L : ℕ}
    (K β : ℝ) (h : Point d → ℝ) (hβ : 0 ≤ β)
    (hs : 0 < s) (hr₀ : 0 < Percolation.initialRadius (8*s))
    (hrs : Percolation.initialRadius (8*s) ≤ s)
    (hevent : SmallClusters (sourceGood K β s h) n s L)
    (hHJ : ∀ y ∈ volume n,
      UpperParameters.rootInfluence (rho K d β) (8*s) s
        (maxBlockSize (sourceGood K β s h) n s) *
        (J (sourceGood K β s h) n s y : ℝ) ≤ (I (sourceGood K β s h) n s y : ℝ)/2) :
    ∀ η ξ : Config ↥(volume (d := d) n),
      hammingWasserstein (canonicalKernel K β h hs hevent η) (canonicalKernel K β h hs hevent ξ) ≤
        (1 - coveringRate d / maxBlockSize (sourceGood K β s h) n s) * hammingR η ξ := by
  apply hamming_path_coupling
  intro η ξ hdist
  obtain ⟨y, hy, hrest⟩ := (hamming_eq_one_iff η ξ).mp hdist
  exact canonical_one_site K β h hβ hs hr₀ hrs hevent hHJ η ξ y hy hrest

/-- Lemma 3.5 at the source's actual rounded scales and actual quenched good
labels. The overlap/influence absorption is derived from `covering_parameters`,
so the only environmental hypothesis is the actual finite bad-cluster event. -/
theorem lemma_3_5 {d : ℕ} (hd : 2 ≤ d) (K β κ : ℝ)
    (hβ : 0 ≤ β) (hκ : 1 ≤ κ) :
    ∀ᶠ n : ℕ in atTop,
      ∃ hs : 0 < UpperParameters.sourceS κ n,
        ∀ h : Point d → ℝ,
          ∀ hevent : SmallClusters (sourceGood K β (UpperParameters.sourceS κ n) h)
            n (UpperParameters.sourceS κ n) (UpperScale.clusterCutoff κ n),
          ∀ η ξ : Config ↥(volume (d := d) n),
            hammingWasserstein (canonicalKernel K β h hs hevent η)
                (canonicalKernel K β h hs hevent ξ) ≤
              (1 - coveringRate d /
                maxBlockSize (sourceGood K β (UpperParameters.sourceS κ n) h)
                  n (UpperParameters.sourceS κ n)) * hammingR η ξ := by
  have hκp : 0 < κ := by linarith
  filter_upwards [UpperParameters.initialRadius_fits hκp,
    UpperParameters.covering_parameters d hd κ (rho K d β) hκ (rho_pos _ _ _)] with n hi hp
  refine ⟨hi.1, ?_⟩
  intro h hevent
  have hparam := hp (sourceGood K β (UpperParameters.sourceS κ n) h) hevent
  exact canonical_all_pair K β h hβ hi.1 hparam.1 hparam.2.1 hevent
    (fun y hy => (hparam.2.2.2.2 y hy).1)

end Paper09.IdealContraction
