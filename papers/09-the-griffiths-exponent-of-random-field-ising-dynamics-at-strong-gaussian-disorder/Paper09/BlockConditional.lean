import Paper09.IslandGap
import Paper09.BlockKernels

open Finset BigOperators Classical Real
open Paper09.Disagreement Paper09.BlockKernels
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1200000

namespace Paper09.RFIM

local instance (priority := 2000) blockConditionalPointDecEq (d : ℕ) :
    DecidableEq (Point d) := Classical.decEq _
local instance (priority := 2000) blockConditionalSiteDecEq {d : ℕ}
    (A : Finset (Point d)) : DecidableEq ↥A := Classical.decEq _
local instance (priority := 2000) blockConditionalSumDecEq {I O : Type*} :
    DecidableEq (I ⊕ O) := Classical.decEq _
local instance (priority := 3000) blockConditionalSubtypeDecEq {V : Type*}
    (B : Finset V) : DecidableEq ↥B := Classical.decEq _

/-- A physical block, as a finite set of sites in the ambient state space. -/
def ambientBlockSites {d : ℕ} (A B : Finset (Point d)) : Finset ↥A :=
  univ.filter fun x => x.val ∈ B

@[simp] theorem mem_ambientBlockSites {d : ℕ} (A B : Finset (Point d)) (x : ↥A) :
    x ∈ ambientBlockSites A B ↔ x.val ∈ B := by simp [ambientBlockSites]

/-- The block's nested ambient subtype and its physical site subtype agree. -/
def blockSiteEquiv {d : ℕ} (A B : Finset (Point d)) (hBA : B ⊆ A) :
    ↥(ambientBlockSites A B) ≃ ↥B where
  toFun x := ⟨x.val.val, (mem_ambientBlockSites A B x.val).mp x.property⟩
  invFun x := ⟨⟨x.val, hBA x.property⟩, (mem_ambientBlockSites A B _).mpr x.property⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

/-- Freeze every ambient site outside the block, replacing exactly its internal spins. -/
def blockExtend {d : ℕ} (A B : Finset (Point d)) (hBA : B ⊆ A)
    (τ : Config ↥A) (σ : Config ↥B) : Config ↥A :=
  fun x => if hx : x.val ∈ B then σ ⟨x.val, hx⟩ else τ x

@[simp] theorem blockExtend_inside {d : ℕ} (A B : Finset (Point d)) (hBA : B ⊆ A)
    (τ : Config ↥A) (σ : Config ↥B) (x : ↥B) :
    blockExtend A B hBA τ σ ⟨x.val, hBA x.property⟩ = σ x := by
  simp [blockExtend, x.property]

@[simp] theorem blockExtend_outside {d : ℕ} (A B : Finset (Point d)) (hBA : B ⊆ A)
    (τ : Config ↥A) (σ : Config ↥B) (x : ↥A) (hx : x.val ∉ B) :
    blockExtend A B hBA τ σ x = τ x := by simp [blockExtend, hx]

/-- Only frozen neighbors which belong to the finite ambient domain contribute.
There is no interaction with sites outside the free-boundary ambient domain. -/
def blockLocalField {d : ℕ} (A B : Finset (Point d)) (h : Point d → ℝ)
    (β : ℝ) (τ : Config ↥A) (x : ↥B) : ℝ :=
  h x.val + β * ∑ y : ↥(A \ B),
    if LatticeGeometry.Adj x.val y.val then
      spinVal (τ ⟨y.val, (mem_sdiff.mp y.property).1⟩) else 0

/-- The actual Gibbs law of a subdomain after freezing its finite ambient exterior. -/
def blockLocalGibbs {d : ℕ} (A B : Finset (Point d)) (h : Point d → ℝ)
    (β : ℝ) (τ : Config ↥A) : FinProb (Config ↥B) :=
  gibbs (domainLattice B) (blockLocalField A B h β τ) β univ ∅ (fun _ => 0)

theorem blockLocalGibbs_positive {d : ℕ} (A B : Finset (Point d)) (h : Point d → ℝ)
    (β : ℝ) (τ : Config ↥A) (σ : Config ↥B) :
    0 < (blockLocalGibbs A B h β τ).w σ :=
  gibbs_positive _ _ _ _ _ _ _

theorem blockExtend_split {d : ℕ} (A B : Finset (Point d)) (hBA : B ⊆ A)
    (τ : Config ↥A) (σ : Config ↥B) :
    (Relabel.configEquiv (islandSplit A B hBA).symm).symm
      (Sum.elim σ (fun o : ↥(A \ B) => τ ⟨o.val, (mem_sdiff.mp o.property).1⟩)) =
      blockExtend A B hBA τ σ := by
  funext x
  change (Sum.elim σ (fun o : ↥(A \ B) => τ ⟨o.val, (mem_sdiff.mp o.property).1⟩))
      ((islandSplit A B hBA).symm x) = _
  by_cases hx : x.val ∈ B <;> simp [islandSplit, blockExtend, hx]

/-- The restricted sum-coordinate Hamiltonian is precisely the physical block
Hamiltonian with the finite ambient conditional field. -/
theorem sumInteriorGibbs_eq_blockLocalGibbs {d : ℕ} (A B : Finset (Point d))
    (hBA : B ⊆ A) (h : Point d → ℝ) (β : ℝ) (τ : Config ↥A) :
    sumInteriorGibbs (Relabel.lattice (domainLattice A) (islandSplit A B hBA).symm)
      (fun s => h ((islandSplit A B hBA) s).val) β
      (fun o : ↥(A \ B) => τ ⟨o.val, (mem_sdiff.mp o.property).1⟩) =
      blockLocalGibbs A B h β τ := by
  let e := islandSplit A B hBA
  let Λ := Relabel.lattice (domainLattice A) e.symm
  have ht := Relabel.gibbs_transport (domainLattice B) Λ.sumLeft (Equiv.refl _) (fun _ _ => Iff.rfl)
    (blockLocalField A B h β τ)
    (Λ.sumConditionalField (fun s => h (e s).val) β
      (fun o : ↥(A \ B) => τ ⟨o.val, (mem_sdiff.mp o.property).1⟩)) (by
      intro x
      dsimp [Λ, e, Lattice.sumConditionalField, Relabel.lattice, islandSplit,
        domainLattice, blockLocalField]
      congr 2
      apply sum_congr rfl
      intro o ho
      congr 1) β
  change gibbs Λ.sumLeft _ β univ ∅ _ = _
  rw [ht]
  apply FinProb.ext_weights
  intro σ
  rfl

/-- Actual ambient Gibbs weights restricted to one frozen-exterior fiber are
proportional to the actual local Gibbs weights. The coefficient is obtained
from the joint law's true marginal, rather than being assumed. -/
theorem freeGibbs_block_factorization {d : ℕ} (A B : Finset (Point d))
    (hBA : B ⊆ A) (h : Point d → ℝ) (β : ℝ) (τ : Config ↥A) :
    ∃ c : ℝ, ∀ σ : Config ↥B,
      (freeGibbs A h β).w (blockExtend A B hBA τ σ) =
        c * (blockLocalGibbs A B h β τ).w σ := by
  let e := islandSplit A B hBA
  let Λ := Relabel.lattice (domainLattice A) e.symm
  let hs : ↥B ⊕ ↥(A \ B) → ℝ := fun s => h (e s).val
  let τo : Config ↥(A \ B) := fun o => τ ⟨o.val, (mem_sdiff.mp o.property).1⟩
  let ps := gibbs Λ hs β univ ∅ (fun _ => 0)
  let q := ps.reindex (Equiv.sumArrowEquivProdArrow ↥B ↥(A \ B) Spin)
  have hp : ps = (freeGibbs A h β).reindex (Relabel.configEquiv e.symm) := by
    exact Relabel.gibbs_transport (domainLattice A) Λ e.symm
      (by intro x y; dsimp [Λ, Relabel.lattice]; simp) (fun x => h x.val) hs
      (by intro x; dsimp [hs]; rw [e.apply_symm_apply]) β
  refine ⟨q.exteriorMarginal.w τo, ?_⟩
  intro σ
  have hj := FinProb.joint_eq_marginal_mul_conditional q
    (blockLocalGibbs A B h β τ) σ τo
  have hcond : (q.interiorConditional (blockLocalGibbs A B h β τ) τo).w σ =
      (blockLocalGibbs A B h β τ).w σ := by
    rw [show (q.interiorConditional (blockLocalGibbs A B h β τ) τo).w σ =
        (sumInteriorGibbs Λ hs β τo).w σ from
      gibbs_sum_conditional_w Λ hs β _ τo σ]
    rw [sumInteriorGibbs_eq_blockLocalGibbs A B hBA h β τ]
  rw [hcond] at hj
  have hweight : q.w (σ, τo) = (freeGibbs A h β).w (blockExtend A B hBA τ σ) := by
    change ps.w (Sum.elim σ τo) = _
    rw [hp]
    change (freeGibbs A h β).w ((Relabel.configEquiv e.symm).symm (Sum.elim σ τo)) = _
    rw [blockExtend_split]
  exact hweight.symm.trans hj

theorem blockExtend_eq_embedConfig {d : ℕ} (A B : Finset (Point d)) (hBA : B ⊆ A)
    (τ : Config ↥A) (σ : Config ↥B) :
    embedConfig (ambientBlockSites A B) τ
      ((Relabel.configEquiv (blockSiteEquiv A B hBA)).symm σ) =
      blockExtend A B hBA τ σ := by
  funext x
  by_cases hx : x.val ∈ B
  · have hxU : x ∈ ambientBlockSites A B := (mem_ambientBlockSites A B x).mpr hx
    simp [embedConfig, blockExtend, hxU, hx, Relabel.configEquiv, blockSiteEquiv]
  · have hxU : x ∉ ambientBlockSites A B := (mem_ambientBlockSites A B x).not.mpr hx
    simp [embedConfig, blockExtend, hxU, hx]

/-- The true block conditional law, in physical block coordinates, is the
finite-domain Gibbs law with exactly the frozen ambient neighbor field. -/
theorem localConditional_eq_blockLocalGibbs {d : ℕ} (A B : Finset (Point d))
    (hBA : B ⊆ A) (h : Point d → ℝ) (β : ℝ) (τ : Config ↥A) :
    (localConditional (freeGibbs A h β)
      (gibbs_positive (domainLattice A) (fun x : ↥A => h x.val) β univ ∅ (fun _ => 0))
      (ambientBlockSites A B) τ).reindex (Relabel.configEquiv (blockSiteEquiv A B hBA)) =
      blockLocalGibbs A B h β τ := by
  let p := freeGibbs A h β
  let hp : ∀ η, 0 < p.w η := gibbs_positive _ _ _ _ _ _
  let U := ambientBlockSites A B
  let E := Relabel.configEquiv (blockSiteEquiv A B hBA)
  let q := localConditional p hp U τ
  let qr := q.reindex E
  let μ := blockLocalGibbs A B h β τ
  obtain ⟨c, hc⟩ := freeGibbs_block_factorization A B hBA h β τ
  have hw (σ : Config ↥B) :
      qr.w σ = (c / assignmentMass p (univ \ U) τ) * μ.w σ := by
    change q.w (E.symm σ) = _
    rw [localConditional_w, blockExtend_eq_embedConfig A B hBA τ σ, hc]
    ring
  have hnorm : c / assignmentMass p (univ \ U) τ = 1 := by
    calc
      _ = (c / assignmentMass p (univ \ U) τ) * ∑ σ, μ.w σ := by rw [μ.sum_one, mul_one]
      _ = ∑ σ, qr.w σ := by simp_rw [hw]; rw [mul_sum]
      _ = 1 := qr.sum_one
  apply FinProb.ext_weights
  intro σ
  change qr.w σ = μ.w σ
  rw [hw, hnorm, one_mul]

/-- Relabeling a finite law and then mapping it is the same as composing
the map with the relabeling equivalence. -/
theorem reindex_map_comp {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (p : FinProb X) (e : X ≃ Y) (f : Y → Z) :
    (p.reindex e).map f = p.map (fun x => f (e x)) := by
  apply FinProb.ext_weights
  intro z
  change (∑ y, if f y = z then p.w (e.symm y) else 0) = _
  have hs := e.symm.sum_comp (fun x => if f (e x) = z then p.w x else 0)
  simpa only [e.apply_symm_apply] using hs

/-- A block heat-bath step is exactly a sample from the genuine finite
subdomain Gibbs law, extended by the frozen ambient spins. -/
theorem blockHeatBath_eq_localGibbs_map {d : ℕ} (A B : Finset (Point d))
    (hBA : B ⊆ A) (h : Point d → ℝ) (β : ℝ) (τ : Config ↥A) :
    blockHeatBath (freeGibbs A h β)
      (gibbs_positive (domainLattice A) (fun x : ↥A => h x.val) β univ ∅ (fun _ => 0))
      (ambientBlockSites A B) τ =
      (blockLocalGibbs A B h β τ).map (blockExtend A B hBA τ) := by
  rw [← localConditional_eq_blockLocalGibbs A B hBA h β τ, reindex_map_comp]
  have he (σ : Config ↥(ambientBlockSites A B)) :
      blockExtend A B hBA τ ((Relabel.configEquiv (blockSiteEquiv A B hBA)) σ) =
        embedConfig (ambientBlockSites A B) τ σ := by
    rw [← blockExtend_eq_embedConfig]
    simp only [Equiv.symm_apply_apply]
  simp_rw [he]
  exact (localConditional_embed _ _ _ _).symm

/-- The local effective field increases the physical field bound by at most
the degree times `β`, uniformly in every frozen ambient configuration. -/
theorem blockLocalField_abs_le {d : ℕ} (A B : Finset (Point d))
    (h : Point d → ℝ) (β H : ℝ) (hβ : 0 ≤ β)
    (hh : ∀ x ∈ B, |h x| ≤ H) (τ : Config ↥A) (x : ↥B) :
    |blockLocalField A B h β τ x| ≤ H + 2 * (d : ℝ) * β := by
  let E : Finset ↥(A \ B) := univ.filter (fun y => LatticeGeometry.Adj x.val y.val)
  have hc : E.card ≤ 2 * d := by
    calc
      E.card = (E.image Subtype.val).card := (card_image_of_injective E Subtype.val_injective).symm
      _ ≤ (LatticeGeometry.neighbors x.val).card := by
        apply card_le_card
        intro y hy
        obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
        exact LatticeGeometry.mem_neighbors.mpr (mem_filter.mp hz).2
      _ ≤ 2 * d := LatticeGeometry.card_neighbors_le x.val
  have hs : |∑ y : ↥(A \ B), if LatticeGeometry.Adj x.val y.val then
      spinVal (τ ⟨y.val, (mem_sdiff.mp y.property).1⟩) else 0| ≤ (E.card : ℝ) := by
    calc
      _ ≤ ∑ y : ↥(A \ B), |if LatticeGeometry.Adj x.val y.val then
          spinVal (τ ⟨y.val, (mem_sdiff.mp y.property).1⟩) else 0| := abs_sum_le_sum_abs _ _
      _ = ∑ y : ↥(A \ B), if LatticeGeometry.Adj x.val y.val then (1 : ℝ) else 0 := by
        apply sum_congr rfl
        intro y _
        split_ifs <;> simp
      _ = _ := by rw [← Finset.sum_boole]
  have hs' : |∑ y : ↥(A \ B), if LatticeGeometry.Adj x.val y.val then
      spinVal (τ ⟨y.val, (mem_sdiff.mp y.property).1⟩) else 0| ≤ 2 * (d : ℝ) :=
    hs.trans (by exact_mod_cast hc)
  unfold blockLocalField
  calc
    _ ≤ |h x.val| + |β * ∑ y : ↥(A \ B), if LatticeGeometry.Adj x.val y.val then
        spinVal (τ ⟨y.val, (mem_sdiff.mp y.property).1⟩) else 0| := abs_add_le _ _
    _ = |h x.val| + β * |∑ y : ↥(A \ B), if LatticeGeometry.Adj x.val y.val then
        spinVal (τ ⟨y.val, (mem_sdiff.mp y.property).1⟩) else 0| := by rw [abs_mul, abs_of_nonneg hβ]
    _ ≤ H + β * (2 * (d : ℝ)) := add_le_add (hh x.val x.property)
      (mul_le_mul_of_nonneg_left hs' hβ)
    _ = _ := by ring

/-- The actual binary heat-bath probability is preserved by the finite-domain
conditional Gibbs identification. This gives the required generator ratios. -/
theorem freeGibbs_block_heatBathRatio {d : ℕ} (A B : Finset (Point d))
    (hBA : B ⊆ A) (h : Point d → ℝ) (β : ℝ) (τ : Config ↥A)
    (σ σ' : Config ↥B) :
    (freeGibbs A h β).w (blockExtend A B hBA τ σ') /
      ((freeGibbs A h β).w (blockExtend A B hBA τ σ) +
        (freeGibbs A h β).w (blockExtend A B hBA τ σ')) =
      (blockLocalGibbs A B h β τ).w σ' /
        ((blockLocalGibbs A B h β τ).w σ + (blockLocalGibbs A B h β τ).w σ') := by
  obtain ⟨c, hc⟩ := freeGibbs_block_factorization A B hBA h β τ
  have hcne : c ≠ 0 := by
    intro hz
    have hp := gibbs_positive (domainLattice A) (fun x : ↥A => h x.val) β univ ∅
      (fun _ => 0) (blockExtend A B hBA τ σ)
    change 0 < (freeGibbs A h β).w _ at hp
    rw [hc σ, hz, zero_mul] at hp
    exact (lt_irrefl 0) hp
  rw [hc σ, hc σ', ← mul_add, mul_div_mul_left _ _ hcne]

end Paper09.RFIM
