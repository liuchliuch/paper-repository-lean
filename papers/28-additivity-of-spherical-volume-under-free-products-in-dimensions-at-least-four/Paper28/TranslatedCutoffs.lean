import Paper28.StabilizerBumps

/-! Explicit translates of the stabilizer-invariant smooth cutoffs. Full
group indices are retained; finite stabilizer duplication is harmless after
normalizing the sum and avoids any arbitrary coset representative choice. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Metric
variable {G J : Type*} [Group G] [DecidableEq G] [Fintype J]
variable (c : J → CoordinateHilbert G) [∀ j, Fintype (regularStabilizer (c j))]
variable (b : ∀ j, ContDiffBump (c j))

def translatedCutoff (i : J×G) (u : CoordinateHilbert G) : ℝ :=
  averagedBump (regularStabilizer (c i.1)) (b i.1) (leftRegular i.2⁻¹ u)

theorem leftRegular_inv_dist (γ : G) (u z : CoordinateHilbert G) :
    dist (leftRegular γ⁻¹ u) z = dist u (leftRegular γ z) := by
  have h := (leftRegular γ).isometry.dist_eq (leftRegular γ⁻¹ u) z
  rw [← leftRegular_mul,mul_inv_cancel,leftRegular_one] at h
  exact h.symm

theorem translatedCutoff_nonneg (i : J×G) (u : CoordinateHilbert G) :
    0 ≤ translatedCutoff c b i u := averagedBump_nonneg _ _ _

theorem translatedCutoff_contDiff (i : J×G) (n : ℕ∞) : ContDiff ℝ n (translatedCutoff c b i) :=
  (averagedBump_contDiff _ _ n).comp (leftRegular i.2⁻¹).toContinuousLinearEquiv.contDiff

/-- The whole translate family is equivariant by an actual permutation of
its full group index. No representative independence is assumed. -/
theorem translatedCutoff_equivariant (j : J) (γ δ : G) (u : CoordinateHilbert G) :
    translatedCutoff c b (j,δ*γ) (leftRegular δ u) = translatedCutoff c b (j,γ) u := by
  unfold translatedCutoff
  rw [← leftRegular_mul]
  simp only [mul_inv_rev,mul_assoc,inv_mul_cancel,mul_one]

/-- Every nonzero cutoff lies in the corresponding translated chart ball. -/
theorem translatedCutoff_support (i : J×G) (u : CoordinateHilbert G)
    (hu : translatedCutoff c b i u ≠ 0) : dist u (leftRegular i.2 (c i.1)) < (b i.1).rOut := by
  by_contra h
  apply hu
  apply averagedBump_zero
  · intro h
    exact h.property
  · rw [leftRegular_inv_dist]
    exact not_lt.mp h

/-- A single finite set of translate indices contains the supports of all
cutoffs throughout an ambient neighborhood of every unit vector. -/
theorem translatedCutoff_local_finite (hRadius : ∀ j, (b j).rOut < (1/4 : ℝ))
    (hUnit : ∀ j, ‖c j‖ = 1) (u : CoordinateHilbert G) (hu : ‖u‖ = 1) :
    ∃ s : Finset (J×G), ∀ v, dist u v < (1/2 : ℝ) → ∀ i ∉ s, translatedCutoff c b i v = 0 := by
  classical
  let B := Finset.univ.biUnion (fun j : J =>
    (regular_near_translates_finite u (c j) hu (hUnit j)).toFinset)
  refine ⟨Finset.univ ×ˢ B,?_⟩
  intro v hv i hi
  by_contra hβ
  have hclose := translatedCutoff_support c b i v hβ
  have ht := dist_triangle u v (leftRegular i.2 (c i.1))
  have hn : dist u (leftRegular i.2 (c i.1)) < 1 := by linarith [hRadius i.1]
  have hb : i.2 ∈ B := Finset.mem_biUnion.mpr
    ⟨i.1,Finset.mem_univ i.1,by simpa only [Set.Finite.mem_toFinset,Set.mem_setOf_eq] using hn⟩
  exact hi (Finset.mem_product.mpr ⟨Finset.mem_univ i.1,hb⟩)

end Paper28
