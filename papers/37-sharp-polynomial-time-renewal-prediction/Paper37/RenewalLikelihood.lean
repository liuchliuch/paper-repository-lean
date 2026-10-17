import Paper37.RenewalModel
import Mathlib.Data.List.Nodup

namespace Paper37.Renewal
open scoped BigOperators

/-- Completed gap lengths minus one, as in the law's indexing convention. -/
def gapsFrom (a : ℕ) : List Bool → List ℕ
  | [] => []
  | false::x => gapsFrom (a+1) x
  | true::x => a :: gapsFrom 0 x

/-- The ordinary likelihood retains exactly the terminal censoring factor. -/
theorem ordinary_completed_gaps (μ : Law) (a : ℕ) (x : List Bool) :
    ordinary μ a x = ((gapsFrom a x).map μ.mass).prod * tail μ (ageFrom a x) := by
  induction x generalizing a with
  | nil => simp [ordinary, gapsFrom, ageFrom]
  | cons b x ih => cases b with
    | false => exact ih (a+1)
    | true => simp only [ordinary, gapsFrom, ageFrom, List.map_cons, List.prod_cons,
        ih 0, mul_assoc]

/-- Exact block likelihood with its left and right stationary boundary factors,
source (B.9). Here the first renewal is at position `j+1`. -/
theorem blockMass_two_boundaries (μ : Law) (j : ℕ) (x : List Bool) :
    blockMass μ (List.replicate j false ++ true::x) =
      tail μ j / mean μ * ((gapsFrom 0 x).map μ.mass).prod *
        tail μ (ageFrom 0 x) := by
  rw [blockMass_first_renewal, ordinary_completed_gaps]
  ring

lemma initial_wait_le_one (μ : Law) (j : ℕ) : tail μ j / mean μ ≤ 1 := by
  apply (div_le_one (mean_pos μ)).mpr
  exact (tail_le_one μ j).trans (mean_ge_one μ)

/-- Dropping both genuine probability boundary factors gives the completed-gap
likelihood product, as used by the envelope construction. -/
theorem blockMass_le_completed_gap_likelihood (μ : Law) (j : ℕ) (x : List Bool) :
    blockMass μ (List.replicate j false ++ true::x) ≤
      ((gapsFrom 0 x).map μ.mass).prod := by
  rw [blockMass_two_boundaries]
  have hprod : ∀ ds : List ℕ, 0 ≤ (ds.map μ.mass).prod := by
    intro ds
    induction ds with
    | nil => simp
    | cons d ds ih => exact mul_nonneg (μ.nonneg d) ih
  have hp := hprod (gapsFrom 0 x)
  calc
    _ ≤ 1 * ((gapsFrom 0 x).map μ.mass).prod * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right (initial_wait_le_one μ j) hp)
        (tail_le_one μ _) (tail_nonneg μ _) (by simpa using hp)
    _ = _ := by ring

/-- A renewal at a fixed location factors the subsequent ordinary block. -/
theorem ordinary_regeneration (μ : Law) (a : ℕ) (x y : List Bool) :
    ordinary μ a (x ++ true::y) = ordinary μ a (x ++ [true]) * ordinary μ 0 y := by
  induction x generalizing a with
  | nil => simp [ordinary, tail_zero]
  | cons b x ih => cases b with
    | false => exact ih (a+1)
    | true => simpa only [List.cons_append, ordinary, ih 0, mul_assoc]

theorem stationaryNumerator_regeneration (μ : Law) (a : ℕ) (x y : List Bool) :
    stationaryNumerator μ a (x ++ true::y) =
      stationaryNumerator μ a (x ++ [true]) * ordinary μ 0 y := by
  induction x generalizing a with
  | nil => simp [stationaryNumerator, ordinary, tail_zero]
  | cons b x ih => cases b with
    | false => exact ih (a+1)
    | true =>
      change tail μ a * ordinary μ 0 (x ++ true::y) =
        (tail μ a * ordinary μ 0 (x ++ [true])) * ordinary μ 0 y
      rw [ordinary_regeneration μ 0 x y]
      ring

/-- Regeneration is established for the constructed stationary block masses,
not supplied as a property of an abstract risk interface. -/
theorem blockMass_regeneration (μ : Law) (x y : List Bool) :
    blockMass μ (x ++ true::y) = blockMass μ (x ++ [true]) * ordinary μ 0 y := by
  unfold blockMass
  rw [stationaryNumerator_regeneration]
  ring

/-- The binary enumeration has no duplicates, so `wordSum` is a probability
sum over exactly the length-indexed source alphabet. -/
lemma words_nodup (n : ℕ) : (words n).Nodup := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    apply List.Nodup.append
    · exact ih.map (fun x y h => (List.cons.inj h).2)
    · exact ih.map (fun x y h => (List.cons.inj h).2)
    · intro z hz0 hz1
      obtain ⟨x, hx, h0⟩ := List.mem_map.mp hz0
      obtain ⟨y, hy, h1⟩ := List.mem_map.mp hz1
      have := (List.cons.inj (h0.trans h1.symm)).1
      cases this

end Paper37.Renewal
