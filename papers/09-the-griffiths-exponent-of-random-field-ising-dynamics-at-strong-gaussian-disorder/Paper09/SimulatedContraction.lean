import Paper09.IdealContraction
import Paper09.SimulatedColorInfluence
import Paper09.ActualBlockMixing

open Finset BigOperators Classical Real Filter
open Paper09.LatticeGeometry Paper09.BlockCovering Paper09.BlockColoring Paper09.BlockDynamics
open Paper09.IdealContraction
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000

namespace Paper09.SimulatedContraction

local instance (priority := 2000) simulatedVolumeDecidableEq {d n : ℕ} :
    DecidableEq ↥(volume (d := d) n) := Classical.decEq _

/-- The actual physical color phase: choose the constructed color uniformly
and run exactly its retained rate-one clocks for the common time `T`. -/
def canonicalKernel {d n s L : ℕ} (K β : ℝ) (h : Point d → ℝ)
    (hs : 0 < s) (hevent : SmallClusters (sourceGood K β s h) n s L) (T : ℝ) :
    Config ↥(volume (d := d) n) → FinProb (Config ↥(volume (d := d) n)) :=
  Censoring.colorKernel (RFIMBlocks.volumeLaw d n h β) (RFIMBlocks.volumeLaw_positive d n h β)
    (RFIMBlocks.uniformColors (colorCount (sourceGood K β s h) n s) (colorCount_pos hs hevent))
    (RFIMBlocks.retainedSites (coloring hs hevent)) T

/-- For one actual color, the only approximation charge is on its unique
affected block. The good root, closure disjointness and volume bound are
derived from the constructed covering. -/
theorem physicalClass_stepBudget {d n s L Q : ℕ}
    (K β : ℝ) (h : Point d → ℝ) (hβ : 0 ≤ β)
    (hs : 0 < s) (hr₀ : 0 < Percolation.initialRadius (8*s))
    (hrs : Percolation.initialRadius (8*s) ≤ s)
    (hevent : SmallClusters (sourceGood K β s h) n s L)
    (c : (conflictGraph (sourceGood K β s h) n s).Coloring (Fin Q))
    (T δ : ℝ) (hδ : 0 ≤ δ)
    (hlocal : ∀ (i : BlockIndex (sourceGood K β s h) n s) η,
      tvDist (Censoring.siteTransition (RFIMBlocks.volumeLaw d n h β)
        (RFIMBlocks.volumeLaw_positive d n h β) (blockSites i) T η)
        (BlockKernels.blockHeatBath (RFIMBlocks.volumeLaw d n h β)
          (RFIMBlocks.volumeLaw_positive d n h β) (blockSites i) η) ≤ δ)
    (η ξ : Config ↥(volume (d := d) n)) (y : ↥(volume (d := d) n))
    (hy : η y ≠ ξ y) (hrest : ∀ z, z ≠ y → η z = ξ z) (a : Fin Q) :
    hammingWasserstein (RFIMBlocks.physicalClass h β c T a η)
        (RFIMBlocks.physicalClass h β c T a ξ) ≤
      stepBudget (fun i => c i) blockSites boundarySites
        (UpperParameters.rootInfluence (rho K d β) (8*s) s
          (maxBlockSize (sourceGood K β s h) n s)) a y +
      (2 * (maxBlockSize (sourceGood K β s h) n s : ℝ) * δ) *
        ((∑ i, if c i = a ∧ y ∈ blockSites i then (1:ℝ) else 0) +
          (∑ i, if c i = a ∧ y ∈ boundarySites i then (1:ℝ) else 0)) := by
  have hM (i : BlockIndex (sourceGood K β s h) n s) :
      (blockSites i).card ≤ maxBlockSize (sourceGood K β s h) n s := by
    rw [RFIMBlocks.card_blockSites]
    exact Finset.le_sup (f := fun i : BlockIndex (sourceGood K β s h) n s => (block i).card) (mem_univ i)
  have hb := SimulatedColorInfluence.simulated_color_update_budget
    (RFIM.domainLattice (volume n)) h K β Subtype.val Subtype.val_injective
    (by intro x z hxz; exact hxz) (classIndices c a) blockSites
    (RFIMBlocks.class_domain_closures_disjoint c a)
    (8*s) (Percolation.initialRadius (8*s)) s (maxBlockSize (sourceGood K β s h) n s)
    hr₀ hrs (fun i _ => hM i) δ hδ η ξ y hy hrest hβ (by simp [RFIM.domainLattice])
    (fun i _ => boundary_source_good K β h hs hevent i y) T (fun i _ => hlocal i)
  simp only [RFIMBlocks.physicalClass, RFIMBlocks.volumeLaw, RFIM.freeGibbs,
    RFIMBlocks.retainedSites, ColorInfluence.selectedSites, classIndices,
    RFIMBlocks.domain_boundary_blockSites, ColorInfluence.goodRootBudget,
    UpperParameters.rootInfluence, stepBudget, Finset.sum_filter, ite_and] at hb ⊢
  convert hb using 1 <;> congr! 8

/-- Physical one-discrepancy contraction after the proved simulation budget
and covering incidence gain are combined. -/
theorem canonical_one_site {d n s L : ℕ}
    (K β : ℝ) (h : Point d → ℝ) (hβ : 0 ≤ β)
    (hs : 0 < s) (hr₀ : 0 < Percolation.initialRadius (8*s))
    (hrs : Percolation.initialRadius (8*s) ≤ s)
    (hevent : SmallClusters (sourceGood K β s h) n s L)
    (hM : 1 ≤ maxBlockSize (sourceGood K β s h) n s)
    (hHJ : ∀ y ∈ volume n,
      UpperParameters.rootInfluence (rho K d β) (8*s) s
        (maxBlockSize (sourceGood K β s h) n s) *
        (J (sourceGood K β s h) n s y : ℝ) ≤ (I (sourceGood K β s h) n s y : ℝ)/2)
    (hIJ : ∀ y ∈ volume n, I (sourceGood K β s h) n s y +
      J (sourceGood K β s h) n s y ≤ 4*I (sourceGood K β s h) n s y)
    (T : ℝ)
    (hlocal : ∀ (i : BlockIndex (sourceGood K β s h) n s) η,
      tvDist (Censoring.siteTransition (RFIMBlocks.volumeLaw d n h β)
        (RFIMBlocks.volumeLaw_positive d n h β) (blockSites i) T η)
        (BlockKernels.blockHeatBath (RFIMBlocks.volumeLaw d n h β)
          (RFIMBlocks.volumeLaw_positive d n h β) (blockSites i) η) ≤
        (1/64:ℝ)/(maxBlockSize (sourceGood K β s h) n s:ℝ)^2)
    (η ξ : Config ↥(volume (d := d) n)) (y : ↥(volume (d := d) n))
    (hy : η y ≠ ξ y) (hrest : ∀ z, z ≠ y → η z = ξ z) :
    hammingWasserstein (canonicalKernel K β h hs hevent T η)
        (canonicalKernel K β h hs hevent T ξ) ≤
      1 - coveringRate d / maxBlockSize (sourceGood K β s h) n s := by
  let good := sourceGood K β s h
  let Q := colorCount good n s
  let M := maxBlockSize good n s
  let H := UpperParameters.rootInfluence (rho K d β) (8*s) s M
  have hQn : 0 < Q := colorCount_pos hs hevent
  letI : NeZero Q := ⟨hQn.ne'⟩
  have hQ : (0:ℝ) < Q := Nat.cast_pos.mpr hQn
  have hI : (0:ℝ) < I good n s y.val := by
    exact_mod_cast (lt_of_lt_of_le (pow_pos (show 0 < 2*s+1 by omega) _)
      (covering_lower hs hevent y.property))
  have hIJ' : (I good n s y.val:ℝ)+(J good n s y.val:ℝ) ≤ 4*(I good n s y.val:ℝ) := by
    exact_mod_cast hIJ y.val y.property
  have hM' : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hδ : 0 ≤ (1/64:ℝ)/(M:ℝ)^2 := by positivity
  have hclass := physicalClass_stepBudget K β h hβ hs hr₀ hrs hevent (coloring hs hevent)
    T ((1/64:ℝ)/(M:ℝ)^2) hδ hlocal η ξ y hy hrest
  have hb := simulated_colorKernel_one_site hQn (fun i => (coloring hs hevent) i)
    blockSites boundarySites H (2*(M:ℝ)*((1/64:ℝ)/(M:ℝ)^2))
    (RFIMBlocks.physicalClass h β (coloring hs hevent) T) η ξ y hclass
  simp only [blockSites_count, boundarySites_count] at hb
  have hρ : 0 < rho K d β := rho_pos _ _ _
  have hH : 0 ≤ H := by dsimp [H, UpperParameters.rootInfluence]; positivity
  have habs := simulated_budget_absorbed (I good n s y.val) (J good n s y.val) Q H M (1/64)
    hI (by positivity) hQ hM' (by norm_num) (by norm_num) hH (hHJ y.val y.property) hIJ'
  have hinc := covering_incidence_ratio hs hevent y
  rw [canonicalKernel, RFIMBlocks.physical_mixture_eq hQn,
    RFIMBlocks.physical_mixture_eq hQn]
  exact hb.trans (habs.trans (sub_le_sub_left hinc 1))

/-- Lemma 3.6 for the actual finite-volume RFIM and source covering. The
constant is uniform in the field and volume. The only environmental premises
are the real small-bad-cluster event and the real maximum-field event; local
mixing, good roots, overlap absorption and all color budgets are discharged. -/
theorem lemma_3_6 (d : ℕ) (K β σ κ : ℝ) (hd : 2 ≤ d) (hβ : 0 < β)
    (hσ : 0 ≤ σ) (hκ : 1 ≤ κ) :
    ∃ C : ℝ, 1 ≤ C ∧ 1 ≤ C*coveringRate d ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ hs : 0 < UpperParameters.sourceS κ n,
          ∀ (h : Point d → ℝ)
            (hevent : SmallClusters (sourceGood K β (UpperParameters.sourceS κ n) h)
              n (UpperParameters.sourceS κ n) (UpperScale.clusterCutoff κ n)),
            (∀ x ∈ volume n, |h x| ≤ σ*sqrt (8*log (((2*n+1)^d:ℕ):ℝ))) →
            let s := UpperParameters.sourceS κ n
            let M := maxBlockSize (sourceGood K β s h) n s
            let T := UpperScale.stepTime d C (8*s) (UpperScale.clusterCutoff κ n) M (((2*n+1)^d:ℕ):ℝ)
            0 ≤ T ∧ ∀ η ξ : Config ↥(volume (d := d) n),
              hammingWasserstein (canonicalKernel K β h hs hevent T η)
                  (canonicalKernel K β h hs hevent T ξ) ≤
                (1-coveringRate d/M)*hammingR η ξ := by
  obtain ⟨C₀,hC₀,hmix⟩ := RFIM.actual_block_mixing d β σ (1/64) hd hβ hσ
    (by norm_num) (by norm_num)
  let C := max 1 (max C₀ (1/coveringRate d))
  have hC : 1 ≤ C := le_max_left _ _
  have hC₀C : C₀ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hrate : 0 < coveringRate d := coveringRate_pos d
  have hCr : 1 ≤ C*coveringRate d := by
    have hh : 1/coveringRate d ≤ C := (le_max_right _ _).trans (le_max_right _ _)
    exact (div_le_iff₀ hrate).mp hh
  refine ⟨C,hC,hCr,?_⟩
  have hκp : 0 < κ := by linarith
  filter_upwards [UpperParameters.initialRadius_fits hκp,
    UpperParameters.covering_parameters d hd κ (rho K d β) hκ (rho_pos _ _ _),
    (UpperScale.clusterCutoff_tendsto hκp).eventually (eventually_ge_atTop 1),
    eventually_ge_atTop 1] with n hinit hparam hLn hn
  refine ⟨hinit.1,?_⟩
  intro h hevent hfield
  let s := UpperParameters.sourceS κ n
  let L := UpperScale.clusterCutoff κ n
  let good := sourceGood K β s h
  let M := maxBlockSize good n s
  let N : ℝ := ((2*n+1)^d:ℕ)
  let T := UpperScale.stepTime d C (8*s) L M N
  have hpar := hparam good hevent
  have hL : (1:ℝ) ≤ L := hLn
  have hLn' : 1 ≤ L := by exact_mod_cast hLn
  have hsp : 0 < s := hinit.1
  have hR : (1:ℝ) ≤ (8*s:ℕ) := by exact_mod_cast (show 1 ≤ 8*s by omega)
  have hM : (1:ℝ) ≤ M := by exact_mod_cast hpar.2.2.1
  have hN : 2 ≤ N := by
    have hh : 2 ≤ (2*n+1)^d := (show 2 ≤ 2*n+1 by omega).trans
      (le_self_pow (show 1 ≤ 2*n+1 by omega) (by omega : d ≠ 0))
    dsimp [N]
    exact_mod_cast hh
  have hlocal' (i : BlockIndex good n s) := hmix C hC₀C (volume n) (block i)
    (block_subset_volume i) h L ((8*s:ℕ):ℝ) M N hL hR hM hN
    (by exact_mod_cast (Finset.le_sup (f := fun i : BlockIndex good n s => (block i).card) (mem_univ i)))
    (by exact_mod_cast (block_size_bound hinit.1 hLn' hevent i)) hfield
  have hlocal : ∀ (i : BlockIndex good n s) η,
      tvDist (Censoring.siteTransition (RFIMBlocks.volumeLaw d n h β)
        (RFIMBlocks.volumeLaw_positive d n h β) (blockSites i) T η)
        (BlockKernels.blockHeatBath (RFIMBlocks.volumeLaw d n h β)
          (RFIMBlocks.volumeLaw_positive d n h β) (blockSites i) η) ≤ (1/64:ℝ)/(M:ℝ)^2 := by
    intro i η
    have hsites : RFIM.ambientBlockSites (volume n) (block i) = blockSites i := by
      ext x
      simp only [RFIM.mem_ambientBlockSites, mem_blockSites]
    have hb := (hlocal' i).2 η
    rw [hsites] at hb
    simpa only [T, UpperScale.stepTime, RFIMBlocks.volumeLaw,
      Nat.cast_mul, Nat.cast_ofNat] using hb
  have hlogM : 0 ≤ log (M:ℝ) := Real.log_nonneg hM
  have hT : 0 ≤ T := by dsimp [T, UpperScale.stepTime]; positivity
  refine ⟨hT,?_⟩
  apply hamming_path_coupling
  intro η ξ hdist
  obtain ⟨y,hy,hrest⟩ := (hamming_eq_one_iff η ξ).mp hdist
  exact canonical_one_site K β h hβ.le hinit.1 hpar.1 hpar.2.1 hevent hpar.2.2.1
    (fun y hy => (hpar.2.2.2.2 y hy).1)
    (fun y hy => (hpar.2.2.2.2 y hy).2.1) T hlocal η ξ y hy hrest

/-- The one-discrepancy version of the fully physical source-scale result. -/
theorem source_one_site (d : ℕ) (K β σ κ : ℝ) (hd : 2 ≤ d) (hβ : 0 < β)
    (hσ : 0 ≤ σ) (hκ : 1 ≤ κ) :
    ∃ C : ℝ, 1 ≤ C ∧ 1 ≤ C*coveringRate d ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ hs : 0 < UpperParameters.sourceS κ n,
          ∀ (h : Point d → ℝ)
            (hevent : SmallClusters (sourceGood K β (UpperParameters.sourceS κ n) h)
              n (UpperParameters.sourceS κ n) (UpperScale.clusterCutoff κ n)),
            (∀ x ∈ volume n, |h x| ≤ σ*sqrt (8*log (((2*n+1)^d:ℕ):ℝ))) →
            let s := UpperParameters.sourceS κ n
            let M := maxBlockSize (sourceGood K β s h) n s
            let T := UpperScale.stepTime d C (8*s) (UpperScale.clusterCutoff κ n) M (((2*n+1)^d:ℕ):ℝ)
            0 ≤ T ∧ ∀ (η ξ : Config ↥(volume (d := d) n)) (y : ↥(volume (d := d) n)),
              η y ≠ ξ y → (∀ z, z ≠ y → η z = ξ z) →
              hammingWasserstein (canonicalKernel K β h hs hevent T η)
                (canonicalKernel K β h hs hevent T ξ) ≤ 1-coveringRate d/M := by
  obtain ⟨C,hC,hCr,hsource⟩ := lemma_3_6 d K β σ κ hd hβ hσ hκ
  refine ⟨C,hC,hCr,?_⟩
  filter_upwards [hsource] with n hn
  obtain ⟨hs,hh⟩ := hn
  refine ⟨hs,?_⟩
  intro h hevent hfield
  obtain ⟨hT,hW⟩ := hh h hevent hfield
  refine ⟨hT,?_⟩
  intro η ξ y hy hrest
  have hdist : hammingR η ξ = 1 := by
    simp only [hammingR, (hamming_eq_one_iff η ξ).mpr ⟨y,hy,hrest⟩, Nat.cast_one]
  simpa only [hdist,mul_one] using hW η ξ

end Paper09.SimulatedContraction
