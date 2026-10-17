/-
Copyright (c) 2026. Physical finite-volume block kernels and their geometry.
-/
import Paper09.RFIM
import Paper09.BlockDynamics
import Paper09.BlockKernels
import Paper09.Censoring

open Finset BigOperators Classical Real
open Paper09.LatticeGeometry Paper09.BlockCovering Paper09.BlockColoring Paper09.BlockDynamics
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
attribute [local instance] Classical.propDecidable

namespace Paper09.RFIMBlocks

local instance (priority := 2000) blockSiteDecEq {d n : ℕ} :
    DecidableEq ↥(volume (d := d) n) := Classical.decEq _

/-- Both developments use the identical physical box `[-n,n]^d`. -/
theorem volume_eq_volumeBox (d n : ℕ) : volume (d := d) n = RFIM.volumeBox d n := by
  ext x
  simp [volume,Near,RFIM.mem_volumeBox]

/-- Actual free-boundary Gibbs law on the covering's finite site space. -/
def volumeLaw (d n : ℕ) (h : Point d → ℝ) (β : ℝ) :
    FinProb (Config ↥(volume (d := d) n)) := RFIM.freeGibbs (volume n) h β

theorem volumeLaw_positive (d n : ℕ) (h : Point d → ℝ) (β : ℝ)
    (η : Config ↥(volume (d := d) n)) : 0 < (volumeLaw d n h β).w η := by
  exact div_pos (isingWeight_pos _ _ _ _ _ _ _) (isingZ_pos _ _ _ _ _ _)

/-- Lifting actual blocks to the finite spin type preserves their size. -/
theorem card_blockSites {d : ℕ} {good : Point d → Prop} {n s : ℕ}
    (i : BlockIndex good n s) : (blockSites i).card = (block i).card := by
  have himage : (blockSites i).image Subtype.val = block i := by
    ext x
    constructor
    · rintro hx
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
      exact (mem_blockSites i z).mp hz
    · intro hx
      exact mem_image.mpr ⟨⟨x,block_subset_volume i hx⟩,(mem_blockSites i _).mpr hx,rfl⟩
  rw [← himage,card_image_of_injective _ Subtype.val_injective]

/-- Relative graph boundary equals the actual lattice boundary in the box. -/
theorem domain_boundary_blockSites {d : ℕ} {good : Point d → Prop} {n s : ℕ}
    (i : BlockIndex good n s) :
    (RFIM.domainLattice (volume n)).boundary (blockSites i) = boundarySites i := by
  ext y
  rw [Lattice.mem_boundary,mem_boundarySites,BlockCovering.mem_boundary]
  constructor
  · rintro ⟨hy,x,hx,hxy⟩
    exact ⟨y.property,fun hh => hy ((mem_blockSites i y).mpr hh),
      x.val,(mem_blockSites i x).mp hx,hxy⟩
  · rintro ⟨_,hy,x,hx,hxy⟩
    exact ⟨fun hh => hy ((mem_blockSites i y).mp hh),
      ⟨x,block_subset_volume i hx⟩,(mem_blockSites i _).mpr hx,hxy⟩

/-- Actual graph closure membership is the covering's physical closure. -/
theorem mem_domain_closure {d : ℕ} {good : Point d → Prop} {n s : ℕ}
    (i : BlockIndex good n s) (y : ↥(volume (d := d) n)) :
    y ∈ blockSites i ∪ (RFIM.domainLattice (volume n)).boundary (blockSites i) ↔
      y.val ∈ BlockColoring.closure i := by
  rw [domain_boundary_blockSites]
  simp only [Finset.mem_union,mem_blockSites,mem_boundarySites,BlockColoring.closure]

/-- The constructed coloring yields disjoint actual graph closures on the
finite-domain site type, with no separate geometric certificate. -/
theorem class_domain_closures_disjoint {d : ℕ} {good : Point d → Prop} {n s : ℕ}
    {α : Type*} (c : (conflictGraph good n s).Coloring α) (a : α) :
    (classIndices c a).toSet.PairwiseDisjoint
      (fun i => blockSites i ∪ (RFIM.domainLattice (volume n)).boundary (blockSites i)) := by
  intro i hi j hj hne
  apply Finset.disjoint_left.mpr
  intro y hyi hyj
  exact Finset.disjoint_left.mp
    (same_color_closures_disjoint c hne
      ((mem_classIndices.mp hi).trans (mem_classIndices.mp hj).symm))
    ((mem_domain_closure i y).mp hyi) ((mem_domain_closure j y).mp hyj)

/-- The exact set of rate-one clocks retained for one selected color. -/
def retainedSites {d : ℕ} {good : Point d → Prop} {n s : ℕ} {α : Type*}
    (c : (conflictGraph good n s).Coloring α) (a : α) : Finset ↥(volume (d := d) n) :=
  (classIndices c a).biUnion blockSites

@[simp] theorem mem_retainedSites {d : ℕ} {good : Point d → Prop} {n s : ℕ} {α : Type*}
    (c : (conflictGraph good n s).Coloring α) (a : α) (x : ↥(volume (d := d) n)) :
    x ∈ retainedSites c a ↔ x.val ∈ classSites c a := by
  simp [retainedSites,mem_classSites,mem_biUnion]

/-- One ideal color phase is the genuine joint conditional Gibbs resampling. -/
def idealClass {d : ℕ} {good : Point d → Prop} {n s : ℕ} {α : Type*}
    (h : Point d → ℝ) (β : ℝ) (c : (conflictGraph good n s).Coloring α) (a : α) :=
  BlockKernels.blockHeatBath (volumeLaw d n h β) (volumeLaw_positive d n h β) (retainedSites c a)

/-- One physical color phase runs retained clocks for the same physical time T. -/
def physicalClass {d : ℕ} {good : Point d → Prop} {n s : ℕ} {α : Type*}
    (h : Point d → ℝ) (β : ℝ) (c : (conflictGraph good n s).Coloring α) (T : ℝ) (a : α) :=
  Censoring.siteTransition (volumeLaw d n h β) (volumeLaw_positive d n h β) (retainedSites c a) T

/-- The actual uniform random choice among Q colors. -/
def uniformColors (Q : ℕ) (hQ : 0 < Q) : FinProb (Fin Q) where
  w _ := 1/(Q:ℝ)
  nonneg _ := by positivity
  sum_one := by
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp

/-- The physical mixture used by censoring is exactly uniform color averaging. -/
theorem physical_mixture_eq {d : ℕ} {good : Point d → Prop} {n s Q : ℕ} [NeZero Q]
    (hQ : 0 < Q) (h : Point d → ℝ) (β : ℝ)
    (c : (conflictGraph good n s).Coloring (Fin Q)) (T : ℝ) (η : Config ↥(volume (d := d) n)) :
    Censoring.colorKernel (volumeLaw d n h β) (volumeLaw_positive d n h β)
      (uniformColors Q hQ) (retainedSites c) T η =
      BlockDynamics.colorKernel (physicalClass h β c T) η := by
  apply FinProb.ext_weights
  intro ξ
  change (∑ a : Fin Q, (1/(Q:ℝ)) * (physicalClass h β c T a η).w ξ) =
    (∑ a : Fin Q, (physicalClass h β c T a η).w ξ) / Fintype.card (Fin Q)
  simp only [Fintype.card_fin,div_eq_mul_inv,one_mul,mul_one,← mul_sum,mul_comm]

/-- The ideal Gibbs law is preserved by every actual color phase. -/
theorem idealClass_stationary {d : ℕ} {good : Point d → Prop} {n s : ℕ} {α : Type*}
    (h : Point d → ℝ) (β : ℝ) (c : (conflictGraph good n s).Coloring α) (a : α) :
    (volumeLaw d n h β).bind (idealClass h β c a) = volumeLaw d n h β :=
  BlockKernels.blockHeatBath_stationary _ _ _

end Paper09.RFIMBlocks
