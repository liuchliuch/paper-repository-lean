import Paper09.LatticeGeometry
import Paper09.Dynamics
import Paper09.Gaussian
import Paper09.LocalGap
import Mathlib.Data.Fintype.Pi
import Mathlib.Probability.ProductMeasure

open Finset BigOperators Real Filter Classical
open scoped Topology

noncomputable section
set_option maxHeartbeats 200000
attribute [local instance] Classical.propDecidable

namespace Paper09.RFIM

abbrev Point := LatticeGeometry.Point

-- Keep the concrete function-space Fintype instances consistent with the
-- classical finite Gibbs API. Its weights depend on an enumeration of states.
local instance pointDecidableEq (d : ℕ) : DecidableEq (Point d) := Classical.decEq _
local instance siteDecidableEq {d : ℕ} (A : Finset (Point d)) : DecidableEq ↥A :=
  Classical.decEq _

/-- The nearest-neighbor graph on the actual finite domain `A ⊂ ℤᵈ`. -/
def domainLattice {d : ℕ} (A : Finset (Point d)) : Lattice ↥A where
  adj x y := LatticeGeometry.Adj x.val y.val
  symm := LatticeGeometry.adj_symm
  irrefl x := LatticeGeometry.adj_irrefl x.val
  maxDegree := 2 * d
  degree_le x := by
    classical
    let s : Finset ↥A := @Finset.filter ↥A
      (fun y => LatticeGeometry.Adj x.val y.val)
      (fun _ => Classical.propDecidable _) univ
    have hs : s.image Subtype.val ⊆ LatticeGeometry.neighbors x.val := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
      apply LatticeGeometry.mem_neighbors.mpr
      simpa only [s, Finset.mem_filter, mem_univ, true_and] using hz
    change s.card ≤ 2 * d
    calc s.card = (s.image Subtype.val).card :=
        (card_image_of_injective s Subtype.val_injective).symm
      _ ≤ (LatticeGeometry.neighbors x.val).card := card_le_card hs
      _ ≤ 2 * d := LatticeGeometry.card_neighbors_le x.val

/-- The actual external vertex boundary in the infinite lattice. -/
def externalBoundary {d : ℕ} (A : Finset (Point d)) : Finset (Point d) :=
  (A.biUnion LatticeGeometry.neighbors) \ A

theorem mem_externalBoundary {d : ℕ} {A : Finset (Point d)} {y : Point d} :
    y ∈ externalBoundary A ↔ y ∉ A ∧ ∃ x ∈ A, LatticeGeometry.Adj x y := by
  simp only [externalBoundary, mem_sdiff, mem_biUnion, LatticeGeometry.mem_neighbors]
  tauto

/-- A pinned exterior contributes its nearest-neighbor interactions to the
one-site field. Every boundary edge is counted once, exactly as in the paper. -/
def effectiveField {d : ℕ} (A : Finset (Point d)) (h : Point d → ℝ)
    (β : ℝ) (ζ : Point d → Spin) (x : ↥A) : ℝ :=
  h x.val + β * ∑ y ∈ externalBoundary A,
    if LatticeGeometry.Adj x.val y then spinVal (ζ y) else 0

/-- The finite-domain Ising Gibbs law with arbitrary fixed exterior spins.
Its state space consists only of the spins in `A`. -/
def pinnedGibbs {d : ℕ} (A : Finset (Point d)) (h : Point d → ℝ)
    (β : ℝ) (ζ : Point d → Spin) : FinProb (↥A → Spin) :=
  gibbs (V := ↥A) (domainLattice A) (effectiveField A h β ζ) β
    (univ : Finset ↥A) (∅ : Finset ↥A) (fun _ : ↥A => 0)

/-- The free-boundary Ising measure (1.2). -/
def freeGibbs {d : ℕ} (A : Finset (Point d)) (h : Point d → ℝ)
    (β : ℝ) : FinProb (↥A → Spin) :=
  gibbs (V := ↥A) (domainLattice A) (fun x : ↥A => h x.val) β
    (univ : Finset ↥A) (∅ : Finset ↥A) (fun _ : ↥A => 0)

/-- Pure boxes `B_m = [1,m]^d ∩ ℤ^d`. -/
def pureBox (d m : ℕ) : Finset (Point d) :=
  Fintype.piFinset (fun _ : Fin d => Icc (1 : ℤ) (m : ℤ))

/-- The free-boundary volume `Λ_n = [-n,n]^d ∩ ℤ^d`. -/
def volumeBox (d n : ℕ) : Finset (Point d) :=
  Fintype.piFinset (fun _ : Fin d => Icc (-(n : ℤ)) (n : ℤ))

@[simp] theorem mem_pureBox {d m : ℕ} {x : Point d} :
    x ∈ pureBox d m ↔ ∀ j, 1 ≤ x j ∧ x j ≤ m := by
  simp [pureBox, Fintype.mem_piFinset]

@[simp] theorem mem_volumeBox {d n : ℕ} {x : Point d} :
    x ∈ volumeBox d n ↔ ∀ j, -(n : ℤ) ≤ x j ∧ x j ≤ n := by
  simp [volumeBox, Fintype.mem_piFinset]

/-- The genuine zero-field, pinned pure-box gap. -/
def pureBoxGap (d m : ℕ) (β : ℝ) (ζ : Point d → Spin) : ℝ :=
  spectralGap (pinnedGibbs (pureBox d m) (fun _ => 0) β ζ)

/-- Assumption 1.1 with its actual sequence, boundary conditions, eventual
quantifier, and consecutive-ratio condition. No lower-bound conclusion is
stored in this assumption. -/
structure SurfaceSlowPureBoxes (d : ℕ) (β : ℝ) : Prop where
  exists_slow_sequence : ∃ (c₀ : ℝ) (m : ℕ → ℕ),
    0 < c₀ ∧ StrictMono m ∧
    Tendsto (fun k => (m (k + 1) : ℝ) / (m k : ℝ)) atTop (𝓝 1) ∧
    ∀ᶠ k in atTop, ∃ ζ : Point d → Spin,
      pureBoxGap d (m k) β ζ ≤ exp (-c₀ * (m k : ℝ) ^ (d - 1))

/-- The actual relaxation time for the free-boundary RFIM in `Λ_n`. -/
def relaxationTime (d n : ℕ) (β : ℝ) (h : Point d → ℝ) : ℝ :=
  tRel (freeGibbs (volumeBox d n) h β)

/-- Independent centered Gaussian environment on the full infinite lattice. -/
def environmentLaw (d : ℕ) (σ : ℝ) : MeasureTheory.Measure (Point d → ℝ) :=
  MeasureTheory.Measure.infinitePi (fun _ : Point d => Gaussian.law σ)

/-- Assumption 1.2 uses the actual Gaussian small-ball probability. -/
def StrongGaussianDisorder (d : ℕ) (β σ : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ rho K d β < 1 / (40 * d) ∧
    (Gaussian.law σ).real {x : ℝ | |x| ≤ K} < 1 / (40 * d)

@[simp] theorem card_pureBox (d m : ℕ) : (pureBox d m).card = m ^ d := by
  simp [pureBox, Fintype.card_piFinset, Int.card_Icc]

@[simp] theorem card_volumeBox (d n : ℕ) : (volumeBox d n).card = (2 * n + 1) ^ d := by
  simp [volumeBox, Fintype.card_piFinset, Int.card_Icc]
  congr 1
  omega

/-- The explicit threshold (1.7) proves the actual Gaussian version of
Assumption 1.2 for every positive inverse temperature. -/
theorem strongGaussianDisorder_of_sigma_ge {d : ℕ} {β σ : ℝ}
    (hd : 1 ≤ d) (hβ : 0 < β) (hσ : sigma0 d β ≤ σ) :
    StrongGaussianDisorder d β σ := by
  exact Gaussian.strong_disorder d β σ (by exact_mod_cast hd) hβ hσ

/-- Uniform local estimate (A.2) for the exact infinite-lattice pinned model. -/
theorem pinned_local_gap (d : ℕ) (β : ℝ) (hd : 2 ≤ d) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset (Point d)), A.Nonempty →
      ∀ (h : Point d → ℝ) (ζ : Point d → Spin),
      C⁻¹ * exp (-C * (A.card : ℝ) ^ exponentA d) ≤
        spectralGap (pinnedGibbs A h β ζ) := by
  obtain ⟨C, hC, hbound⟩ := lemma_A_2_local_gap d β hd hβ
  refine ⟨C, hC, ?_⟩
  intro A hA h ζ
  exact hbound A hA (domainLattice A) (fun _ _ => Iff.rfl)
    (effectiveField A h β ζ) ∅ (fun _ => 0)

/-- A shell face has one coordinate just outside the box and all other
coordinates inside. -/
def boxFace (d m : ℕ) (j : Fin d) : Finset (Point d) :=
  Fintype.piFinset (fun k : Fin d =>
    if k = j then ({0, (m : ℤ) + 1} : Finset ℤ) else Icc (1 : ℤ) (m : ℤ))

theorem externalBoundary_pureBox_subset_faces (d m : ℕ) :
    externalBoundary (pureBox d m) ⊆ univ.biUnion (boxFace d m) := by
  intro y hy
  obtain ⟨hyB, x, hx, j, hstep, hother⟩ := mem_externalBoundary.mp hy
  have hxcoord := mem_pureBox.mp hx
  have hyj : y j = 0 ∨ y j = (m : ℤ) + 1 := by
    have hnot : ¬(1 ≤ y j ∧ y j ≤ m) := by
      intro hinside
      apply hyB
      apply mem_pureBox.mpr
      intro k
      by_cases hk : k = j
      · simpa [hk] using hinside
      · simpa [← hother k hk] using hxcoord k
    have hxi := hxcoord j
    rcases hstep with hs | hs <;> omega
  apply mem_biUnion.mpr
  refine ⟨j, mem_univ _, ?_⟩
  apply Fintype.mem_piFinset.mpr
  intro k
  by_cases hk : k = j
  · subst k
    simpa [boxFace] using hyj
  · simp only [if_neg hk, mem_Icc]
    simpa [← hother k hk] using hxcoord k

theorem card_boxFace (d m : ℕ) (j : Fin d) :
    (boxFace d m j).card = 2 * m ^ (d - 1) := by
  rw [boxFace, Fintype.card_piFinset]
  have hm : (0 : ℤ) ≠ (m : ℤ) + 1 := by omega
  have hfactor : ∀ k : Fin d,
      (if k = j then ({0, (m : ℤ) + 1} : Finset ℤ) else Icc (1 : ℤ) (m : ℤ)).card =
        if k = j then 2 else m := by
    intro k
    split_ifs <;> simp [hm, Int.card_Icc]
  simp_rw [hfactor]
  rw [← mul_prod_erase (univ : Finset (Fin d)) (fun k => if k = j then 2 else m)
    (mem_univ j)]
  simp only [if_pos rfl]
  congr 1
  calc
    (∏ k ∈ (univ : Finset (Fin d)).erase j, if k = j then 2 else m) =
        ∏ _k ∈ (univ : Finset (Fin d)).erase j, m := by
      apply prod_congr rfl
      intro k hk
      simp [(mem_erase.mp hk).1]
    _ = m ^ (d - 1) := by simp

theorem card_externalBoundary_pureBox_le (d m : ℕ) :
    (externalBoundary (pureBox d m)).card ≤ 2 * d * m ^ (d - 1) := by
  calc
    _ ≤ (univ.biUnion (boxFace d m)).card :=
      card_le_card (externalBoundary_pureBox_subset_faces d m)
    _ ≤ ∑ j : Fin d, (boxFace d m j).card := card_biUnion_le
    _ = 2 * d * m ^ (d - 1) := by simp [card_boxFace]; ring

end Paper09.RFIM
