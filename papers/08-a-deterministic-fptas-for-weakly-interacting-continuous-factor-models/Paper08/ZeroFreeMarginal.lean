import Paper08.ZeroFreePhase
import Paper08.CubeMarginal
import Paper08.CubeNormLoss

/-! # Actual marginal non-cancellation from smaller-set phase control -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Paper08.ZeroFreeInduction
open Integral CubeMarginal ComplexSector

variable {n m r c : ℕ} {q θ : ℝ} {z : ℂ}

def Model.partial (M : Model n m r c q) (S : Finset (Fin n)) (z : ℂ)
    (x : Fin n → ℝ) : ℂ := avg S (M.exponential z) x

lemma Model.continuous_partial (M : Model n m r c q) (S : Finset (Fin n)) (z : ℂ) :
    ContinuousOn (M.partial S z) (cube n) :=
  continuousOn_avg S (M.continuous_exponential z)

/-- The phase conclusion at a given set of integrated coordinates. -/
def CoordinatePhase (M : Model n m r c q) (S : Finset (Fin n)) (z : ℂ) (θ : ℝ) : Prop :=
  ∀ x ∈ cube n, ∀ j ∉ S, ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
    Phase (M.partial S z (Function.update x j a))
      (M.partial S z (Function.update x j b)) θ

/-- Uniform simultaneous induction statement. Its quantification over all
 original-promise models is what permits genuine interpolation models. -/
def Good (n m r c : ℕ) (q : ℝ) (z : ℂ) (θ : ℝ) (k : ℕ) : Prop :=
  ∀ M : Model n m r c q, ∀ S : Finset (Fin n), S.card ≤ k →
    (∀ x ∈ cube n, M.partial S z x ≠ 0) ∧ CoordinatePhase M S z θ

lemma overwrite_singleton (j : Fin n) (x : Fin n → ℝ) (y : (↥({j} : Finset (Fin n))) → ℝ) :
    overwrite {j} x y = Function.update x j (y ⟨j, by simp⟩) := by
  funext i
  by_cases hi : i = j
  · subst i; simp [overwrite]
  · simp [overwrite, hi, Function.update_of_ne hi]

lemma phase_singleton_section (M : Model n m r c q) (U : Finset (Fin n))
    (hphase : CoordinatePhase M U z θ) {x : Fin n → ℝ} (hx : x ∈ cube n)
    (j : Fin n) (hj : j ∉ U) :
    ∀ᵐ y ∂MultiMoments.unitMeasure (↥({j} : Finset (Fin n))),
      Phase (M.partial U z x) (M.partial U z (overwrite {j} x y)) θ := by
  filter_upwards [ae_mem_box (↥({j} : Finset (Fin n)))] with y hy
  rw [overwrite_singleton]
  have ha : x j ∈ Set.Icc (0 : ℝ) 1 := mem_cube.mp hx j
  have hb : y ⟨j, by simp⟩ ∈ Set.Icc (0 : ℝ) 1 := mem_box.mp hy _
  simpa only [Function.update_eq_self] using hphase x hx j hj (x j) ha _ hb

/-- One actual coordinate integral is nonzero, using only non-vanishing and
 phase control for the already smaller marginal. -/
lemma Model.partial_insert_nonzero (M : Model n m r c q) (U : Finset (Fin n))
    (hnz : ∀ x ∈ cube n, M.partial U z x ≠ 0) (hphase : CoordinatePhase M U z θ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (j : Fin n) (hj : j ∉ U)
    {x : Fin n → ℝ} (hx : x ∈ cube n) : M.partial (insert j U) z x ≠ 0 := by
  have hInt := integrable_section {j} (M.continuous_partial U z) hx
  have hA := phase_singleton_section M U hphase hx j hj
  have hnzae : ∀ᵐ y ∂MultiMoments.unitMeasure (↥({j} : Finset (Fin n))),
      M.partial U z (overwrite {j} x y) ≠ 0 :=
    (ae_mem_box _).mono fun y hy => hnz _ (overwrite_mem_cube {j} hx hy)
  have h := (integral_nonzero hInt (hnz x hx) hnzae hA hθ0 hθ1).2
  change avg {j} (avg U (M.exponential z)) x ≠ 0 at h
  rw [← avg_insert U j hj (M.continuous_exponential z) hx] at h
  exact h

/-- The quantitative step used in the actual norm-loss iteration. -/
lemma Model.partial_step_lower (M : Model n m r c q) (U : Finset (Fin n))
    (hnz : ∀ x ∈ cube n, M.partial U z x ≠ 0) (hphase : CoordinatePhase M U z θ)
    (hθ1 : θ ≤ 1) (j : Fin n) (hj : j ∉ U)
    {x : Fin n → ℝ} (hx : x ∈ cube n) :
    Real.cos θ * realAvg {j} (fun y => ‖M.partial U z y‖) x ≤
      ‖M.partial (insert j U) z x‖ := by
  have hInt := integrable_section {j} (M.continuous_partial U z) hx
  have hA := phase_singleton_section M U hphase hx j hj
  have h := integral_projection_bound hInt (hnz x hx) hA hθ1
  change Real.cos θ * realAvg {j} (fun y => ‖M.partial U z y‖) x ≤
    ‖avg {j} (M.partial U z) x‖ at h
  change Real.cos θ * realAvg {j} (fun y => ‖M.partial U z y‖) x ≤
    ‖avg {j} (avg U (M.exponential z)) x‖ at h
  rw [← avg_insert U j hj (M.continuous_exponential z) hx] at h
  exact h

/-- Non-vanishing at the next cardinality is proved uniformly before any
 phase estimate at that cardinality is used. -/
lemma nonzero_succ {k : ℕ} (ih : Good n m r c q z θ k)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (M : Model n m r c q)
    (S : Finset (Fin n)) (hS : S.card ≤ k + 1) :
    ∀ x ∈ cube n, M.partial S z x ≠ 0 := by
  by_cases hempty : S = ∅
  · subst S
    intro x hx
    simpa [Model.partial] using M.exponential_ne_zero z x
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hcard : (S.erase j).card ≤ k := by rw [Finset.card_erase_of_mem hj]; omega
    obtain ⟨hnz, hphase⟩ := ih M (S.erase j) hcard
    intro x hx
    have h := M.partial_insert_nonzero (S.erase j) hnz hphase hθ0 hθ1 j
      (Finset.notMem_erase j S) hx
    simpa only [Finset.insert_erase hj] using h

/-- All norm-loss step premises are derived from strictly smaller marginals,
 rather than supplied as input properties of the original model. -/
lemma stepLower_of_good {k : ℕ} (ih : Good n m r c q z θ k)
    (hθ1 : θ ≤ 1) (M : Model n m r c q) (S : Finset (Fin n)) (hS : S.card ≤ k+1) :
    CubeNormLoss.StepLower S (M.exponential z) (Real.cos θ) := by
  intro U hUS j hjS hjU x hx
  have hcard : U.card ≤ k := by
    have hproper : U.card < S.card := Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨hUS, by intro h; subst U; exact hjU hjS⟩)
    omega
  obtain ⟨hnz, hphase⟩ := ih M U hcard
  exact M.partial_step_lower U hnz hphase hθ1 j hjU hx

end Paper08.ZeroFreeInduction
