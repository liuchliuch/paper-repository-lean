import P31.LpEstimates
import P31.Path

/-! The actual coordinate ℓₚ form of the transport and path lemmas. -/
noncomputable section
namespace P31
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

/-- Comparing consecutive true minima of the actual shifted-power objectives
transports the next minimizer into the preceding radius, as in Lemma 4.1. -/
theorem vector_minimizer_transport {p α : ℝ} (hp : 1 < p) (hα : 0 < α)
    (F : (ι → ℝ) → ℝ) (center oldMin newMin : ι → ℝ)
    (hold : ∀ y, F oldMin ≤ F y)
    (hnew : ∀ y, F newMin + α * powerAtom p center newMin ≤
      F y + α * powerAtom p center y) :
    lpNorm p (newMin-center) ≤ lpNorm p (oldMin-center) := by
  have h1 := hold newMin
  have h2 := hnew oldMin
  have hatom : powerAtom p center newMin ≤ powerAtom p center oldMin := by nlinarith
  exact (powerAtom_sublevel_iff (by linarith : 0 < p) center newMin oldMin).mp hatom

/-- Lemma 4.2, instantiated on genuine finite-coordinate ℓₚ, with `U = 3`. -/
theorem vector_path_bound {p : ℝ} (hp : 1 ≤ p)
    (x exactMin : ℕ → ι → ℝ) (R : ℝ) (S : ℕ) (hR : 0 ≤ R)
    (hTransport : ∀ s, 1 ≤ s → s ≤ S →
      lpNorm p (exactMin s - x (s-1)) ≤ R / 2 ^ (s-1))
    (hContract : ∀ s, 1 ≤ s → s ≤ S →
      lpNorm p (x s - exactMin s) ≤ R / 2 ^ s)
    (i : ℕ) (hi : 1 ≤ i) (hiS : i ≤ S) :
    lpNorm p (exactMin S - x (i-1)) ≤ 3 * (R / 2 ^ (i-1)) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  let lift : (ι → ℝ) → PiLp (ENNReal.ofReal p) (fun _ : ι => ℝ) := WithLp.toLp _
  have hn (u v : ι → ℝ) : ‖lift u - lift v‖ = lpNorm p (u-v) := by
    change ‖WithLp.toLp (ENNReal.ofReal p) (u-v)‖ = lpNorm p (u-v)
    exact (lpNorm_eq_piLp_norm p (lt_of_lt_of_le zero_lt_one hp) (u-v)).symm
  have hT : ∀ s, 1 ≤ s → s ≤ S →
      ‖lift (exactMin s) - lift (x (s-1))‖ ≤ geometricRadius R 2 (s-1) := by
    intro s hs hsS
    rw [hn]
    exact hTransport s hs hsS
  have hC : ∀ s, 1 ≤ s → s ≤ S →
      ‖lift (x s) - lift (exactMin s)‖ ≤ geometricRadius R 2 s := by
    intro s hs hsS
    rw [hn]
    exact hContract s hs hsS
  have hh := geometric_path_bound_two (fun n => lift (x n)) (fun n => lift (exactMin n))
    R S hR hT hC i hi hiS
  simpa only [hn] using hh

end P31
