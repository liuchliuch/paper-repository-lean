import Paper09.Coupling
import Paper09.DisagreementMarks
import Paper09.GibbsShell
import Paper09.BadClusters
import Mathlib.Tactic

open Finset BigOperators Classical Real
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000

namespace Paper09.Disagreement

variable {V : Type*} [Fintype V]

/-- A revealed assignment on an arbitrary set of sites. -/
def agrees (E : Finset V) (τ η : Config V) : Prop := ∀ x ∈ E, η x = τ x

def assignmentMass (p : FinProb (Config V)) (E : Finset V) (τ : Config V) : ℝ :=
  ∑ η, if agrees E τ η then p.w η else 0

theorem assignmentMass_pos (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (E : Finset V) (τ : Config V) : 0 < assignmentMass p E τ := by
  have ha : agrees E τ τ := fun _ _ => rfl
  have hle : (if agrees E τ τ then p.w τ else 0) ≤
      ∑ η, if agrees E τ η then p.w η else 0 := by
    apply single_le_sum (s := (univ : Finset (Config V)))
      (f := fun η => if agrees E τ η then p.w η else 0) _ (mem_univ τ)
    intro η _
    by_cases hη : agrees E τ η <;> simp only [hη, if_true, if_false]
    · exact p.nonneg η
    · exact le_rfl
  rw [if_pos ha] at hle
  exact lt_of_lt_of_le (hp τ) hle

/-- The genuine conditional law given the revealed spin values. Positivity of
Gibbs weights ensures that every assignment being conditioned on is possible. -/
def condition (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (E : Finset V) (τ : Config V) : FinProb (Config V) where
  w η := (if agrees E τ η then p.w η else 0) / assignmentMass p E τ
  nonneg η := div_nonneg (by
    by_cases hη : agrees E τ η <;> simp only [hη, if_true, if_false]
    · exact p.nonneg η
    · exact le_rfl) (assignmentMass_pos p hp E τ).le
  sum_one := by
    rw [← sum_div]
    exact div_self (assignmentMass_pos p hp E τ).ne'

theorem condition_empty (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (τ : Config V) : condition p hp ∅ τ = p := by
  have he : assignmentMass p ∅ τ = 1 := by simp [assignmentMass, agrees, p.sum_one]
  cases p
  simp_all [condition, agrees]

theorem condition_support (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (E : Finset V) (τ η : Config V) (hη : (condition p hp E τ).w η ≠ 0) :
    agrees E τ η := by
  by_contra hn
  exact hη (by simp [condition, hn])

theorem condition_expect (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (E : Finset V) (τ : Config V) (f : Config V → ℝ) :
    (condition p hp E τ).expect f =
      p.expect (fun η => (if agrees E τ η then 1 else 0) * f η) / assignmentMass p E τ := by
  simp only [condition, FinProb.expect]
  rw [sum_div]
  apply sum_congr rfl
  intro η _
  split_ifs <;> ring

theorem agrees_flip (E : Finset V) (τ η : Config V) (x : V) (hx : x ∉ E) :
    agrees E τ (spinFlip x η) ↔ agrees E τ η := by
  unfold agrees
  have he (z : V) (hz : z ∈ E) : spinFlip x η z = η z :=
    spinFlip_of_ne (fun h : z = x => by subst z; exact hx hz) η
  constructor <;> intro h z hz
  · simpa only [he z hz] using h z hz
  · simpa only [he z hz] using h z hz

/-- Averaging the actual full conditional bound gives the bound under every
partial assignment which does not reveal the sampled coordinate. -/
theorem partial_defect_bound (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (E : Finset V) (τ ζ : Config V) (x : V) (hx : x ∉ E) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hfull : defectConditionalBound p ζ x ρ) :
    (condition p hp E τ).expect (fun η => defectIndicator ζ η x) ≤ ρ := by
  have hw := weighted_defect_bound p ζ x ρ hρ hfull
    (fun η => if agrees E τ η then 1 else 0)
    (fun η => by dsimp only; split_ifs <;> norm_num)
    (fun η => by simp only [agrees_flip E τ η x hx])
  have he : p.expect (fun η => if agrees E τ η then 1 else 0) = assignmentMass p E τ := by
    unfold FinProb.expect assignmentMass
    apply sum_congr rfl
    intro η _
    by_cases hη : agrees E τ η <;> simp [hη]
  rw [he] at hw
  rw [condition_expect]
  apply (div_le_iff₀ (assignmentMass_pos p hp E τ)).mpr
  convert hw using 1
  unfold FinProb.expect
  apply sum_congr rfl
  intro η _
  ring

/-- Preferred spin, with the paper's `+1` convention at zero field. -/
def preferred (h : V → ℝ) (x : V) : Spin := if h x < 0 then 0 else 1

theorem preferred_direction (h : V → ℝ) (x : V) :
    spinVal (preferred h x) * h x = |h x| := by
  by_cases hx : h x < 0
  · simp [preferred, hx, abs_of_neg hx]
  · simp [preferred, hx, abs_of_nonneg (le_of_not_gt hx)]

theorem gibbs_positive (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (B T : Finset V) (φ η : Config V) : 0 < (gibbs Λ h β B T φ).w η :=
  div_pos (isingWeight_pos _ _ _ _ _ _ _) (isingZ_pos _ _ _ _ _ _)

/-- Equation (3.7) for the actual Gibbs law, including arbitrary partial
conditionings and arbitrary fixed exterior spins. -/
theorem gibbs_partial_strong_field (Λ : Lattice V) (h : V → ℝ) (β K d : ℝ)
    (B T E : Finset V) (hBT : Disjoint B T) (φ τ : Config V)
    (x : V) (hxB : x ∈ B) (hxE : x ∉ E)
    (hβ : 0 ≤ β) (hdeg : (Λ.maxDegree : ℝ) ≤ 2 * d) (hstrong : K < |h x|) :
    (condition (gibbs Λ h β B T φ) (gibbs_positive Λ h β B T φ) E τ).expect
      (fun η => defectIndicator (preferred h) η x) ≤ rho K d β := by
  have hfull := gibbs_defect_conditional_bound Λ h β K d B T hBT φ
    (preferred h) x hxB hβ hdeg (by rw [preferred_direction]; exact hstrong.le)
  exact partial_defect_bound _ _ E τ (preferred h) x hxE (rho K d β)
    (rho_pos _ _ _).le hfull

/-- The actual one-site marginal of a partially exposed Gibbs configuration. -/
def siteMarginal (p : FinProb (Config V)) (x : V) : FinProb Spin where
  w s := ∑ η, if η x = s then p.w η else 0
  nonneg s := sum_nonneg fun η _ => by
    by_cases hη : η x = s <;> simp only [hη, if_true, if_false]
    · exact p.nonneg η
    · exact le_rfl
  sum_one := by
    rw [sum_comm]
    simpa using p.sum_one

theorem siteMarginal_defect (p : FinProb (Config V)) (ζ : Config V) (x : V) :
    (siteMarginal p x).w (otherSpin (ζ x)) = p.expect (fun η => defectIndicator ζ η x) := by
  unfold siteMarginal FinProb.expect
  apply sum_congr rfl
  intro η _
  have he : η x = otherSpin (ζ x) ↔ η x ≠ ζ x := by
    generalize η x = a
    generalize ζ x = b
    fin_cases a <;> fin_cases b <;> norm_num [otherSpin]
  simp only [he, defectIndicator]
  split_ifs <;> simp

/-- For binary laws, maximal coupling disagreement is the difference of the
probabilities of either specified spin. -/
theorem spin_half_l1 (p q : FinProb Spin) (s : Spin) :
    (1 / 2 : ℝ) * ∑ t, |p.w t - q.w t| = |p.w s - q.w s| := by
  have hp : p.w 0 + p.w 1 = 1 := by simpa [Fin.sum_univ_two] using p.sum_one
  have hq : q.w 0 + q.w 1 = 1 := by simpa [Fin.sum_univ_two] using q.sum_one
  have he : p.w 1 - q.w 1 = -(p.w 0 - q.w 0) := by linarith
  have hs : s = 0 ∨ s = 1 := by
    rcases s with ⟨n, hn⟩
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · left; rfl
    · right; rfl
  rcases hs with rfl | rfl <;> simp only [Fin.sum_univ_two, he, abs_neg] <;> ring

/-- The actual maximal one-site coupling disagrees only with probability `ρ`
when both partially conditioned Gibbs marginals favor the same strong-field spin. -/
theorem strong_site_coupling_disagreement (p q : FinProb (Config V))
    (ζ : Config V) (x : V) (ρ : ℝ)
    (hp : p.expect (fun η => defectIndicator ζ η x) ≤ ρ)
    (hq : q.expect (fun η => defectIndicator ζ η x) ≤ ρ) :
    (Coupling.maximal (siteMarginal p x) (siteMarginal q x)).cost
      (fun s t => if s = t then 0 else 1) ≤ ρ := by
  have hc : (Coupling.maximal (siteMarginal p x) (siteMarginal q x)).cost
      (fun s t => if s = t then 0 else 1) =
      (1 / 2 : ℝ) * ∑ s, |(siteMarginal p x).w s - (siteMarginal q x).w s| := by
    convert Coupling.maximal_disagreement_cost (siteMarginal p x) (siteMarginal q x) using 2
    funext s t
    by_cases h : s = t <;> simp [h]
  rw [hc, spin_half_l1 _ _ (otherSpin (ζ x))]
  rw [abs_le]
  have hp0 := (siteMarginal p x).nonneg (otherSpin (ζ x))
  have hq0 := (siteMarginal q x).nonneg (otherSpin (ζ x))
  simp only [siteMarginal_defect] at hp0 hq0 ⊢
  constructor <;> linarith

/-- Change only the revealed coordinates, using coordinatewise spin
permutations. This is an actual bijection of the entire configuration space. -/
def assignmentEquiv (E : Finset V) (τ τ' : Config V) : Config V ≃ Config V where
  toFun η x := if x ∈ E then Equiv.swap (τ x) (τ' x) (η x) else η x
  invFun η x := if x ∈ E then Equiv.swap (τ x) (τ' x) (η x) else η x
  left_inv η := by funext x; by_cases hx : x ∈ E <;> simp [hx]
  right_inv η := by funext x; by_cases hx : x ∈ E <;> simp [hx]

theorem assignmentEquiv_agrees (E : Finset V) (τ τ' η : Config V) :
    agrees E τ' (assignmentEquiv E τ τ' η) ↔ agrees E τ η := by
  unfold agrees
  constructor
  · intro h x hx
    have he := h x hx
    change (if x ∈ E then Equiv.swap (τ x) (τ' x) (η x) else η x) = τ' x at he
    simpa only [hx, if_true, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] using he
  · intro h x hx
    simp [assignmentEquiv, hx, h x hx]

theorem assignmentEquiv_value (E : Finset V) (τ τ' η : Config V)
    (hη : agrees E τ η) (x : V) :
    assignmentEquiv E τ τ' η x = if x ∈ E then τ' x else η x := by
  by_cases hx : x ∈ E
  · simp [assignmentEquiv, hx, hη x hx]
  · simp [assignmentEquiv, hx]

/-- A canonical reference completion, used only to state the additive energy
constant of the revealed region. -/
def reference (E : Finset V) (τ : Config V) : Config V := fun x => if x ∈ E then τ x else 0

theorem reference_agrees (E : Finset V) (τ : Config V) : agrees E τ (reference E τ) := by
  intro x hx
  simp [reference, hx]

def energy (Λ : Lattice V) (h : V → ℝ) (β : ℝ) (B T : Finset V)
    (φ η : Config V) : ℝ :=
  Λ.interaction β B η + Lattice.fieldEnergy h B η + Λ.boundEnergy β B T φ η

/-- The actual Hamiltonian spatial Markov identity. If every edge from an
unrevealed site meets equal boundary or revealed spins, changing the revealed
assignment changes the Hamiltonian only by a constant, independent of all
unrevealed spins. No Markov-property premise is used. -/
theorem energy_difference_constant (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (B T E : Finset V) (φ φ' τ τ' η : Config V) (hη : agrees E τ η)
    (hE : ∀ u ∈ B \ E, ∀ v ∈ E, Λ.adj u v → τ v = τ' v)
    (hT : ∀ u ∈ B \ E, ∀ v ∈ T, Λ.adj u v → φ v = φ' v) :
    energy Λ h β B T φ η - energy Λ h β B T φ' (assignmentEquiv E τ τ' η) =
    energy Λ h β B T φ (reference E τ) -
      energy Λ h β B T φ' (assignmentEquiv E τ τ' (reference E τ)) := by
  have hv := assignmentEquiv_value E τ τ' η hη
  have hr := assignmentEquiv_value E τ τ' (reference E τ) (reference_agrees E τ)
  have hi : Λ.interaction β B η - Λ.interaction β B (assignmentEquiv E τ τ' η) =
      Λ.interaction β B (reference E τ) -
        Λ.interaction β B (assignmentEquiv E τ τ' (reference E τ)) := by
    unfold Lattice.interaction
    rw [← mul_sub, ← mul_sub]
    congr 1
    simp only [← sum_sub_distrib]
    apply sum_congr rfl
    intro u hu
    apply sum_congr rfl
    intro v hvB
    by_cases ha : Λ.adj u v
    · simp only [ha, if_true]
      by_cases huE : u ∈ E <;> by_cases hvE : v ∈ E
      · simp [hv, hr, reference, huE, hvE, hη u huE, hη v hvE]
      · have he := hE v (mem_sdiff.mpr ⟨hvB, hvE⟩) u huE (Λ.symm ha)
        simp [hv, hr, reference, huE, hvE, hη u huE, he]
      · have he := hE u (mem_sdiff.mpr ⟨hu, huE⟩) v hvE ha
        simp [hv, hr, reference, huE, hvE, hη v hvE, he]
      · simp [hv, hr, reference, huE, hvE]
    · simp [ha]
  have hf : Lattice.fieldEnergy h B η -
      Lattice.fieldEnergy h B (assignmentEquiv E τ τ' η) =
      Lattice.fieldEnergy h B (reference E τ) -
        Lattice.fieldEnergy h B (assignmentEquiv E τ τ' (reference E τ)) := by
    unfold Lattice.fieldEnergy
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro u hu
    by_cases huE : u ∈ E
    · simp [hv, hr, reference, huE, hη u huE]
    · simp [hv, hr, reference, huE]
  have hb : Λ.boundEnergy β B T φ η -
      Λ.boundEnergy β B T φ' (assignmentEquiv E τ τ' η) =
      Λ.boundEnergy β B T φ (reference E τ) -
        Λ.boundEnergy β B T φ' (assignmentEquiv E τ τ' (reference E τ)) := by
    unfold Lattice.boundEnergy
    rw [← mul_sub, ← mul_sub]
    congr 1
    simp only [← sum_sub_distrib]
    apply sum_congr rfl
    intro u hu
    apply sum_congr rfl
    intro v hvT
    by_cases ha : Λ.adj u v
    · simp only [ha, if_true]
      by_cases huE : u ∈ E
      · simp [hv, hr, reference, huE, hη u huE]
      · have he := hT u (mem_sdiff.mpr ⟨hu, huE⟩) v hvT ha
        simp [hv, hr, reference, huE, he]
    · simp [ha]
  unfold energy
  linarith

private theorem law_ext {α : Type*} [Fintype α] {p q : FinProb α}
    (h : ∀ a, p.w a = q.w a) : p = q := by
  cases p with
  | mk wp hp sp =>
    cases q with
    | mk wq hq sq =>
      have he : wp = wq := funext h
      cases he
      rfl

/-- Revealing one additional coordinate is exactly the conjunction of the
old assignment with that coordinate's sampled value. -/
theorem agrees_insert (E : Finset V) (τ η : Config V) (x : V) (hx : x ∉ E) (s : Spin) :
    agrees (insert x E) (Function.update τ x s) η ↔ agrees E τ η ∧ η x = s := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro y hy
      have hyx : y ≠ x := fun he => hx (he ▸ hy)
      simpa [hyx] using h y (mem_insert_of_mem hy)
    · simpa using h x (mem_insert_self _ _)
  · rintro ⟨h, hs⟩ y hy
    rcases mem_insert.mp hy with rfl | hy
    · simpa using hs
    · have hyx : y ≠ x := fun he => hx (he ▸ hy)
      simpa [hyx] using h y hy

/-- The next spin's marginal probability is the ratio of the two actual
assignment probabilities. -/
theorem siteMarginal_condition (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (E : Finset V) (τ : Config V) (x : V) (hx : x ∉ E) (s : Spin) :
    (siteMarginal (condition p hp E τ) x).w s =
      assignmentMass p (insert x E) (Function.update τ x s) / assignmentMass p E τ := by
  unfold siteMarginal condition assignmentMass
  rw [sum_div]
  apply sum_congr rfl
  intro η _
  simp only [agrees_insert E τ η x hx s]
  by_cases he : agrees E τ η <;> by_cases hs : η x = s <;> simp [he, hs]

/-- Exact conditional sampling: sample the next spin from its true marginal,
then sample the remaining conditional law. This verifies the marginals of
sequential exploration directly. -/
theorem condition_site_bind (p : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (E : Finset V) (τ : Config V) (x : V) (hx : x ∉ E) :
    (siteMarginal (condition p hp E τ) x).bind
      (fun s => condition p hp (insert x E) (Function.update τ x s)) = condition p hp E τ := by
  apply law_ext
  intro η
  change (∑ s, (siteMarginal (condition p hp E τ) x).w s *
    (condition p hp (insert x E) (Function.update τ x s)).w η) = (condition p hp E τ).w η
  rw [sum_eq_single (η x)]
  · rw [siteMarginal_condition p hp E τ x hx]
    simp only [condition, agrees_insert E τ η x hx (η x), and_true]
    by_cases he : agrees E τ η
    · simp only [if_pos he]
      field_simp [(assignmentMass_pos p hp E τ).ne',
        (assignmentMass_pos p hp (insert x E) (Function.update τ x (η x))).ne']
    · simp [he]
  · intro s hs hne
    have he : ¬ agrees (insert x E) (Function.update τ x s) η := by
      rw [agrees_insert E τ η x hx s]
      exact fun h => hne h.2.symm
    simp [condition, he]
  · simp

/-- Normalization preserves a genuine proportional density after the
revealed coordinates are changed by their explicit bijection. -/
theorem condition_transport_of_density (p q : FinProb (Config V))
    (hp : ∀ η, 0 < p.w η) (hq : ∀ η, 0 < q.w η)
    (E : Finset V) (τ τ' : Config V) (c : ℝ) (hc : c ≠ 0)
    (hdensity : ∀ η, agrees E τ η → p.w η = c * q.w (assignmentEquiv E τ τ' η)) :
    ∀ η, (condition p hp E τ).w η =
      (condition q hq E τ').w (assignmentEquiv E τ τ' η) := by
  have hn (η : Config V) : (if agrees E τ η then p.w η else 0) =
      c * (if agrees E τ' (assignmentEquiv E τ τ' η) then
        q.w (assignmentEquiv E τ τ' η) else 0) := by
    rw [assignmentEquiv_agrees]
    by_cases he : agrees E τ η
    · simp only [he, if_true, hdensity η he]
    · simp [he]
  have hm : assignmentMass p E τ = c * assignmentMass q E τ' := by
    unfold assignmentMass
    calc (∑ η, if agrees E τ η then p.w η else 0)
        = ∑ η, c * (if agrees E τ' (assignmentEquiv E τ τ' η) then
            q.w (assignmentEquiv E τ τ' η) else 0) := sum_congr rfl (fun η _ => hn η)
      _ = c * ∑ η, (if agrees E τ' (assignmentEquiv E τ τ' η) then
            q.w (assignmentEquiv E τ τ' η) else 0) := by rw [mul_sum]
      _ = _ := by
        congr 1
        exact (assignmentEquiv E τ τ').sum_comp
          (fun η => if agrees E τ' η then q.w η else 0)
  intro η
  change (if agrees E τ η then p.w η else 0) / assignmentMass p E τ = _
  rw [hn, hm]
  change c * (if agrees E τ' (assignmentEquiv E τ τ' η) then
    q.w (assignmentEquiv E τ τ' η) else 0) / (c * assignmentMass q E τ') = _
  rw [mul_div_mul_left _ _ hc]
  rfl

/-- The normalized conditional Gibbs laws agree on all unexplored spins at
exploration termination. This is derived from the Hamiltonian identity above. -/
theorem gibbs_spatial_markov (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (B T E : Finset V) (φ φ' τ τ' : Config V)
    (hE : ∀ u ∈ B \ E, ∀ v ∈ E, Λ.adj u v → τ v = τ' v)
    (hT : ∀ u ∈ B \ E, ∀ v ∈ T, Λ.adj u v → φ v = φ' v) :
    ∀ η, (condition (gibbs Λ h β B T φ) (gibbs_positive Λ h β B T φ) E τ).w η =
      (condition (gibbs Λ h β B T φ') (gibbs_positive Λ h β B T φ') E τ').w
        (assignmentEquiv E τ τ' η) := by
  let C := energy Λ h β B T φ (reference E τ) -
    energy Λ h β B T φ' (assignmentEquiv E τ τ' (reference E τ))
  let c := exp C * isingZ Λ h β B T φ' / isingZ Λ h β B T φ
  have hc : 0 < c := div_pos (mul_pos (exp_pos _) (isingZ_pos _ _ _ _ _ _))
    (isingZ_pos _ _ _ _ _ _)
  apply condition_transport_of_density _ _ _ _ E τ τ' c hc.ne'
  intro η hη
  have he := energy_difference_constant Λ h β B T E φ φ' τ τ' η hη hE hT
  have he' : energy Λ h β B T φ η = C +
      energy Λ h β B T φ' (assignmentEquiv E τ τ' η) := by dsimp [C]; linarith
  change exp (energy Λ h β B T φ η) / isingZ Λ h β B T φ =
    c * (exp (energy Λ h β B T φ' (assignmentEquiv E τ τ' η)) / isingZ Λ h β B T φ')
  rw [he', exp_add]
  dsimp [c]
  field_simp [(isingZ_pos Λ h β B T φ).ne', (isingZ_pos Λ h β B T φ').ne']

/-- A coordinate-bijection transport yields a concrete coupling. -/
def equivCoupling (p q : FinProb (Config V)) (e : Config V ≃ Config V)
    (he : ∀ η, p.w η = q.w (e η)) : Coupling p q where
  mass η ξ := if e η = ξ then p.w η else 0
  nonneg η ξ := by split_ifs; exact p.nonneg η; exact le_rfl
  row η := by simp
  col ξ := by
    calc (∑ η, if e η = ξ then p.w η else 0)
        = ∑ η, if η = e.symm ξ then p.w η else 0 := by
          apply sum_congr rfl
          intro η _
          have hh : e η = ξ ↔ η = e.symm ξ := e.apply_eq_iff_eq_symm_apply
          simp only [hh]
      _ = p.w (e.symm ξ) := by simp
      _ = q.w ξ := by rw [he, e.apply_symm_apply]

/-- The final identical sampling of the unexplored region, as an actual
finite coupling with the required Gibbs marginals. -/
def stoppedCoupling (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (B T E : Finset V) (φ φ' τ τ' : Config V)
    (hE : ∀ u ∈ B \ E, ∀ v ∈ E, Λ.adj u v → τ v = τ' v)
    (hT : ∀ u ∈ B \ E, ∀ v ∈ T, Λ.adj u v → φ v = φ' v) :
    Coupling (condition (gibbs Λ h β B T φ) (gibbs_positive Λ h β B T φ) E τ)
      (condition (gibbs Λ h β B T φ') (gibbs_positive Λ h β B T φ') E τ') :=
  equivCoupling _ _ (assignmentEquiv E τ τ') (gibbs_spatial_markov Λ h β B T E φ φ' τ τ' hE hT)

theorem stoppedCoupling_identical_unexplored (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (B T E : Finset V) (φ φ' τ τ' : Config V)
    (hE : ∀ u ∈ B \ E, ∀ v ∈ E, Λ.adj u v → τ v = τ' v)
    (hT : ∀ u ∈ B \ E, ∀ v ∈ T, Λ.adj u v → φ v = φ' v)
    (η ξ : Config V) (hm : (stoppedCoupling Λ h β B T E φ φ' τ τ' hE hT).mass η ξ ≠ 0)
    (x : V) (hx : x ∉ E) : η x = ξ x := by
  have he : assignmentEquiv E τ τ' η = ξ := by
    by_contra hn
    exact hm (by simp [stoppedCoupling, equivCoupling, hn])
  rw [← he]
  simp [assignmentEquiv, hx]

/-- The actual nearest-neighbor graph of the finite ambient site set. -/
def latticeGraph (Λ : Lattice V) : SimpleGraph V where
  Adj := Λ.adj
  symm := fun _ _ h => Λ.symm h
  loopless := Λ.irrefl

/-- Current disagreement sources, either revealed interior spins or the
original, fixed exterior perturbation. -/
def origin (E T : Finset V) (τ τ' φ φ' : Config V) (r : V) : Prop :=
  (r ∈ E ∧ τ r ≠ τ' r) ∨ (r ∈ T ∧ φ r ≠ φ' r)

/-- The next sites which can see a currently existing disagreement. -/
def frontier (Λ : Lattice V) (B T E : Finset V) (φ φ' τ τ' : Config V) (x : V) : Prop :=
  x ∈ B \ E ∧ ∃ r, origin E T τ τ' φ φ' r ∧ Λ.adj r x

/-- In the final samples, paths of actual differing spins connect revealed
sources to every as-yet-unrevealed disagreement. -/
def differenceOpen (B T : Finset V) (φ φ' η ξ : Config V) (x : V) : Prop :=
  (x ∈ B ∧ η x ≠ ξ x) ∨ (x ∈ T ∧ φ x ≠ φ' x)

def ConnectedDisagreements (Λ : Lattice V) (B T E : Finset V)
    (φ φ' τ τ' η ξ : Config V) : Prop :=
  ∀ x ∈ B \ E, η x ≠ ξ x → ∃ r, origin E T τ τ' φ φ' r ∧
    (Percolation.openGraph (latticeGraph Λ) (differenceOpen B T φ φ' η ξ)).Reachable r x

/-- Absence of a disagreement frontier gives the geometric hypotheses of
the already-proved Gibbs spatial Markov identity. -/
theorem no_frontier_separates (Λ : Lattice V) (B T E : Finset V)
    (φ φ' τ τ' : Config V) (hn : ¬ ∃ x, frontier Λ B T E φ φ' τ τ' x) :
    (∀ u ∈ B \ E, ∀ v ∈ E, Λ.adj u v → τ v = τ' v) ∧
    (∀ u ∈ B \ E, ∀ v ∈ T, Λ.adj u v → φ v = φ' v) := by
  constructor
  · intro u hu v hv ha
    by_contra hneq
    exact hn ⟨u, hu, v, Or.inl ⟨hv, hneq⟩, Λ.symm ha⟩
  · intro u hu v hv ha
    by_contra hneq
    exact hn ⟨u, hu, v, Or.inr ⟨hv, hneq⟩, Λ.symm ha⟩

theorem coupling_revealed_left (p q : FinProb (Config V)) (hp : ∀ η, 0 < p.w η)
    (E : Finset V) (τ : Config V) (c : Coupling (condition p hp E τ) q)
    {η ξ : Config V} (hm : c.mass η ξ ≠ 0) : agrees E τ η := by
  apply condition_support p hp E τ η
  intro hz
  exact hm (c.mass_eq_zero_of_row hz ξ)

theorem coupling_revealed_right (p q : FinProb (Config V)) (hq : ∀ η, 0 < q.w η)
    (E : Finset V) (τ : Config V) (c : Coupling p (condition q hq E τ))
    {η ξ : Config V} (hm : c.mass η ξ ≠ 0) : agrees E τ ξ := by
  apply condition_support q hq E τ ξ
  intro hz
  exact hm (c.mass_eq_zero_of_col hz η)

/-- A selected frontier site which ends up differing is joined by one actual
disagreement edge to an older revealed or original exterior source. -/
theorem frontier_disagreement_reachable (Λ : Lattice V) (B T E : Finset V)
    (hEB : E ⊆ B) (φ φ' τ τ' η ξ : Config V)
    (hη : agrees E τ η) (hξ : agrees E τ' ξ) (x : V)
    (hx : frontier Λ B T E φ φ' τ τ' x) (hneq : η x ≠ ξ x) :
    ∃ r, origin E T τ τ' φ φ' r ∧
      (Percolation.openGraph (latticeGraph Λ) (differenceOpen B T φ φ' η ξ)).Reachable r x := by
  obtain ⟨hxB, r, hr, ha⟩ := hx
  refine ⟨r, hr, SimpleGraph.Adj.reachable ?_⟩
  refine ⟨ha, ?_, Or.inl ⟨(mem_sdiff.mp hxB).1, hneq⟩⟩
  rcases hr with ⟨hrE, hrneq⟩ | hrT
  · exact Or.inl ⟨hEB hrE, by simpa only [hη r hrE, hξ r hrE] using hrneq⟩
  · exact Or.inr hrT

/-- The actual stopped Gibbs coupling contains no further disagreements and
therefore satisfies the terminal connectivity assertion. -/
theorem stoppedCoupling_connected (Λ : Lattice V) (h : V → ℝ) (β : ℝ)
    (B T E : Finset V) (φ φ' τ τ' : Config V)
    (hn : ¬ ∃ x, frontier Λ B T E φ φ' τ τ' x)
    (η ξ : Config V)
    (hm : (stoppedCoupling Λ h β B T E φ φ' τ τ'
      (no_frontier_separates Λ B T E φ φ' τ τ' hn).1
      (no_frontier_separates Λ B T E φ φ' τ τ' hn).2).mass η ξ ≠ 0) :
    ConnectedDisagreements Λ B T E φ φ' τ τ' η ξ := by
  intro x hx hneq
  exact (hneq (stoppedCoupling_identical_unexplored Λ h β B T E φ φ' τ τ' _ _
    η ξ hm x (mem_sdiff.mp hx).2)).elim

/-- Connectivity is preserved by the actual reveal-and-recurse operation. -/
theorem connected_step (Λ : Lattice V) (B T E : Finset V) (hEB : E ⊆ B)
    (φ φ' τ τ' η ξ : Config V) (x : V)
    (hx : frontier Λ B T E φ φ' τ τ' x) (s t : Spin)
    (hη : agrees (insert x E) (Function.update τ x s) η)
    (hξ : agrees (insert x E) (Function.update τ' x t) ξ)
    (hchild : ConnectedDisagreements Λ B T (insert x E) φ φ'
      (Function.update τ x s) (Function.update τ' x t) η ξ) :
    ConnectedDisagreements Λ B T E φ φ' τ τ' η ξ := by
  have hxE : x ∉ E := (mem_sdiff.mp hx.1).2
  have hηE := (agrees_insert E τ η x hxE s).mp hη
  have hξE := (agrees_insert E τ' ξ x hxE t).mp hξ
  intro z hz hneq
  by_cases hzx : z = x
  · subst z
    exact frontier_disagreement_reachable Λ B T E hEB φ φ' τ τ' η ξ hηE.1 hξE.1 x hx hneq
  · have hz' : z ∈ B \ insert x E := by simpa [hzx] using hz
    obtain ⟨r, hr, hpath⟩ := hchild z hz' hneq
    rcases hr with ⟨hr, hrdiff⟩ | hr
    · rcases mem_insert.mp hr with hrx | hrE
      · subst r
        have hst : s ≠ t := by simpa using hrdiff
        have hxdiff : η x ≠ ξ x := by simpa only [hηE.2, hξE.2] using hst
        obtain ⟨r, hr, hrx⟩ := frontier_disagreement_reachable Λ B T E hEB
          φ φ' τ τ' η ξ hηE.1 hξE.1 x hx hxdiff
        exact ⟨r, hr, hrx.trans hpath⟩
      · have hrx : r ≠ x := fun he => hxE (he ▸ hrE)
        refine ⟨r, Or.inl ⟨hrE, ?_⟩, hpath⟩
        simpa [hrx] using hrdiff
    · exact ⟨r, Or.inr hr, hpath⟩

/-- Site-opening probabilities of (3.2), with a fixed field realization. -/
def openingProbability (h : V → ℝ) (K ρ : ℝ) (x : V) : ℝ :=
  if |h x| ≤ K then 1 else ρ

theorem openingProbability_nonneg (h : V → ℝ) (K ρ : ℝ) (hρ : 0 ≤ ρ) (x : V) :
    0 ≤ openingProbability h K ρ x := by unfold openingProbability; split_ifs <;> linarith

theorem openingProbability_le_one (h : V → ℝ) (K ρ : ℝ) (hρ : ρ ≤ 1) (x : V) :
    openingProbability h K ρ x ≤ 1 := by unfold openingProbability; split_ifs <;> linarith

theorem spin_probability_complement (p : FinProb Spin) (s : Spin) :
    p.w s + p.w (otherSpin s) = 1 := by
  have he : p.w 0 + p.w 1 = 1 := by simpa [Fin.sum_univ_two] using p.sum_one
  have hs : s = 0 ∨ s = 1 := by
    rcases s with ⟨n, hn⟩
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · left; rfl
    · right; rfl
  rcases hs with rfl | rfl <;> norm_num [otherSpin] at * <;> linarith

/-- A common closed mass `1-p_x` can actually be allocated to the preferred
spin in every partially conditioned Gibbs marginal. -/
theorem gibbs_preferred_mass (Λ : Lattice V) (h : V → ℝ) (β K d : ℝ)
    (B T E : Finset V) (hBT : Disjoint B T) (φ τ : Config V)
    (x : V) (hxB : x ∈ B) (hxE : x ∉ E)
    (hβ : 0 ≤ β) (hdeg : (Λ.maxDegree : ℝ) ≤ 2 * d) :
    1 - openingProbability h K (rho K d β) x ≤
      (siteMarginal (condition (gibbs Λ h β B T φ) (gibbs_positive Λ h β B T φ) E τ) x).w
        (preferred h x) := by
  by_cases hweak : |h x| ≤ K
  · simp only [openingProbability, hweak, if_true, sub_self]
    exact (siteMarginal _ x).nonneg _
  · simp only [openingProbability, hweak, if_false]
    have hbound := gibbs_partial_strong_field Λ h β K d B T E hBT φ τ x hxB hxE hβ hdeg
      (lt_of_not_ge hweak)
    rw [← siteMarginal_defect] at hbound
    have hsum := spin_probability_complement
      (siteMarginal (condition (gibbs Λ h β B T φ) (gibbs_positive Λ h β B T φ) E τ) x)
      (preferred h x)
    linarith

/-- All initially sourced disagreements lie in the forced-open root cluster
once every actual interior disagreement carries an open mark. -/
theorem disagreement_cluster_inclusion (Λ : Lattice V) (B T : Finset V)
    (φ φ' η ξ : Config V) (ω : V → Bool) (y : V)
    (hboundary : ∀ r ∈ T, φ r ≠ φ' r → r = y)
    (hconnected : ConnectedDisagreements Λ B T ∅ φ φ' φ φ' η ξ)
    (hopen : ∀ x ∈ B, η x ≠ ξ x → ω x = true)
    (x : V) (hx : x ∈ B) (hneq : η x ≠ ξ x) :
    x ∈ Percolation.cluster (latticeGraph Λ) (fun z => z = y ∨ ω z = true) y := by
  obtain ⟨r, hr, hpath⟩ := hconnected x (by simpa using hx) hneq
  have hry : r = y := by
    rcases hr with ⟨hr, _⟩ | ⟨hr, hdiff⟩
    · simp at hr
    · exact hboundary r hr hdiff
  subst r
  refine ⟨Or.inl rfl, hpath.mono ?_⟩
  intro u v huv
  refine ⟨huv.1, ?_, ?_⟩
  · rcases huv.2.1 with ⟨huB, hudiff⟩ | ⟨huT, hudiff⟩
    · exact Or.inr (hopen u huB hudiff)
    · exact Or.inl (hboundary u huT hudiff)
  · rcases huv.2.2 with ⟨hvB, hvdiff⟩ | ⟨hvT, hvdiff⟩
    · exact Or.inr (hopen v hvB hvdiff)
    · exact Or.inl (hboundary v hvT hvdiff)

/-- The finite forced-open cluster, counted without assuming a box shape. -/
def forcedClusterCard (Λ : Lattice V) (ω : V → Bool) (y : V) : ℕ :=
  (univ.filter fun x => x ∈ Percolation.cluster (latticeGraph Λ)
    (fun z => z = y ∨ ω z = true) y).card

/-- Equation (3.8), once the actual exploration has yielded its two support
invariants: no disagreements outside the block, and cluster connectivity. -/
theorem hamming_le_forced_cluster (Λ : Lattice V) (B T : Finset V)
    (φ φ' η ξ : Config V) (ω : V → Bool) (y : V)
    (hboundary : ∀ r ∈ T, φ r ≠ φ' r → r = y)
    (hconnected : ConnectedDisagreements Λ B T ∅ φ φ' φ φ' η ξ)
    (hopen : ∀ x ∈ B, η x ≠ ξ x → ω x = true)
    (houtside : ∀ x, x ∉ B → η x = ξ x) :
    hamming η ξ ≤ min B.card (forcedClusterCard Λ ω y) := by
  apply le_min
  · apply card_le_card
    intro x hx
    have hneq := (mem_filter.mp hx).2
    by_contra hxB
    exact hneq (houtside x hxB)
  · apply card_le_card
    intro x hx
    have hneq := (mem_filter.mp hx).2
    have hxB : x ∈ B := by
      by_contra hxB
      exact hneq (houtside x hxB)
    exact mem_filter.mpr ⟨mem_univ _, disagreement_cluster_inclusion Λ B T φ φ' η ξ ω y
      hboundary hconnected hopen x hxB hneq⟩

/-- A pointwise domination in an actual marked coupling gives the expected
transport-cost bound under exactly its verified independent mark marginal. -/
theorem marked_cost_le {p q : FinProb (Config V)} {m : FinProb (V → Bool)}
    (c : MarkedCoupling p q m) (g : (V → Bool) → ℝ)
    (hdom : ∀ η ξ ω, c.mass η ξ ω ≠ 0 → hammingR η ξ ≤ g ω) :
    c.toCoupling.cost hammingR ≤ m.expect g := by
  calc c.toCoupling.cost hammingR
      = ∑ η, ∑ ξ, ∑ ω, c.mass η ξ ω * hammingR η ξ := by
        unfold Coupling.cost MarkedCoupling.toCoupling
        simp only [sum_mul]
    _ ≤ ∑ η, ∑ ξ, ∑ ω, c.mass η ξ ω * g ω := by
        apply sum_le_sum
        intro η _
        apply sum_le_sum
        intro ξ _
        apply sum_le_sum
        intro ω _
        by_cases hz : c.mass η ξ ω = 0
        · simp [hz]
        · exact mul_le_mul_of_nonneg_left (hdom η ξ ω hz) (c.nonneg η ξ ω)
    _ = ∑ ω, ∑ η, ∑ ξ, c.mass η ξ ω * g ω := by
        calc (∑ η, ∑ ξ, ∑ ω, c.mass η ξ ω * g ω)
            = ∑ η, ∑ ω, ∑ ξ, c.mass η ξ ω * g ω := by
              apply sum_congr rfl
              intro η _
              rw [sum_comm]
          _ = _ := by rw [sum_comm]
    _ = m.expect g := by
        unfold FinProb.expect
        apply sum_congr rfl
        intro ω _
        simp only [← sum_mul, c.mark]

private def retypeMarked {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    {p p' : FinProb α} {q q' : FinProb β} {m m' : FinProb γ}
    (c : MarkedCoupling p q m) (hp : p = p') (hq : q = q') (hm : m = m') :
    MarkedCoupling p' q' m' where
  mass := c.mass
  nonneg := c.nonneg
  left a := by rw [← hp]; exact c.left a
  right b := by rw [← hq]; exact c.right b
  mark ω := by rw [← hm]; exact c.mark ω

/-- The support invariant of the explicit adaptive disagreement exploration. -/
def ExplorationSupport (Λ : Lattice V) (B T E : Finset V)
    (φ φ' τ τ' η ξ : Config V) (ω : V → Bool) : Prop :=
  (∀ x, x ∉ B → η x = ξ x) ∧
  ConnectedDisagreements Λ B T E φ φ' τ τ' η ξ ∧
  (∀ x ∈ B \ E, η x ≠ ξ x → ω x = true)

/-- Construct the actual adaptive Gibbs disagreement exploration on every
finite, arbitrarily shaped block. A true one-site marginal is sampled at each
frontier site, using a verified independent Bernoulli mark. Recursion terminates
when the proved spatial Markov identity permits identical completion. All three
marginals (both Gibbs laws and the independent mark law) are verified. -/
theorem exists_marked_exploration (Λ : Lattice V) (h : V → ℝ) (β K d : ℝ)
    (B T : Finset V) (hBT : Disjoint B T) (φ φ' : Config V)
    (hβ : 0 ≤ β) (hdeg : (Λ.maxDegree : ℝ) ≤ 2 * d) :
    ∀ E : Finset V, E ⊆ B → ∀ τ τ' : Config V,
    ∃ c : MarkedCoupling
      (condition (gibbs Λ h β B T φ) (gibbs_positive Λ h β B T φ) E τ)
      (condition (gibbs Λ h β B T φ') (gibbs_positive Λ h β B T φ') E τ')
      (DisagreementMarks.productMarks (openingProbability h K (rho K d β))
        (openingProbability_nonneg h K _ (rho_pos _ _ _).le)
        (openingProbability_le_one h K _ (rho_lt_one _ _ _).le) (B \ E)),
      ∀ η ξ ω, c.mass η ξ ω ≠ 0 → ExplorationSupport Λ B T E φ φ' τ τ' η ξ ω := by
  let p := gibbs Λ h β B T φ
  let q := gibbs Λ h β B T φ'
  let hp := gibbs_positive Λ h β B T φ
  let hq := gibbs_positive Λ h β B T φ'
  let θ := openingProbability h K (rho K d β)
  let hθ0 := openingProbability_nonneg h K _ (rho_pos K d β).le
  let hθ1 := openingProbability_le_one h K _ (rho_lt_one K d β).le
  let M := DisagreementMarks.productMarks θ hθ0 hθ1
  have hall : ∀ n : ℕ, ∀ E : Finset V, (B \ E).card = n → E ⊆ B → ∀ τ τ' : Config V,
      ∃ c : MarkedCoupling (condition p hp E τ) (condition q hq E τ') (M (B \ E)),
      ∀ η ξ ω, c.mass η ξ ω ≠ 0 → ExplorationSupport Λ B T E φ φ' τ τ' η ξ ω := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro E hn hEB τ τ'
      by_cases hfront : ∃ x, frontier Λ B T E φ φ' τ τ' x
      · obtain ⟨x, hx⟩ := hfront
        have hxB : x ∈ B := (mem_sdiff.mp hx.1).1
        have hxE : x ∉ E := (mem_sdiff.mp hx.1).2
        have hU : (B \ E).erase x = B \ insert x E := by ext z; simp; tauto
        have hlt : (B \ insert x E).card < n := by
          rw [← hU, ← hn]
          exact card_erase_lt_of_mem hx.1
        have hE' : insert x E ⊆ B := insert_subset hxB hEB
        have hchildren : ∀ s t : Spin, ∃ c : MarkedCoupling
            (condition p hp (insert x E) (Function.update τ x s))
            (condition q hq (insert x E) (Function.update τ' x t)) (M (B \ insert x E)),
            ∀ η ξ ω, c.mass η ξ ω ≠ 0 →
              ExplorationSupport Λ B T (insert x E) φ φ'
                (Function.update τ x s) (Function.update τ' x t) η ξ ω :=
          fun s t => ih _ hlt _ rfl hE' _ _
        choose e he using hchildren
        let P := fun s => condition p hp (insert x E) (Function.update τ x s)
        let Q := fun t => condition q hq (insert x E) (Function.update τ' x t)
        let e' : ∀ s t (_b : Bool), MarkedCoupling (P s) (Q t) (M ((B \ E).erase x)) :=
          fun s t _b => retypeMarked (e s t) rfl rfl (by rw [hU])
        let cp := siteMarginal (condition p hp E τ) x
        let cq := siteMarginal (condition q hq E τ') x
        have hcp : 1 - θ x ≤ cp.w (preferred h x) :=
          gibbs_preferred_mass Λ h β K d B T E hBT φ τ x hxB hxE hβ hdeg
        have hcq : 1 - θ x ≤ cq.w (preferred h x) :=
          gibbs_preferred_mass Λ h β K d B T E hBT φ' τ' x hxB hxE hβ hdeg
        let a := DisagreementMarks.preferredCoupling cp cq (preferred h x) (preferred h x)
          (θ x) (hθ0 x) (hθ1 x) hcp hcq
        let comp := a.compose P Q (M ((B \ E).erase x)) e'
        let mapped := comp.mapMark (fun ν => Function.update ν.2 x ν.1)
        let c := retypeMarked mapped (condition_site_bind p hp E τ x hxE)
          (condition_site_bind q hq E τ' x hxE)
          (DisagreementMarks.productMarks_update θ hθ0 hθ1 (B \ E) x hx.1)
        refine ⟨c, ?_⟩
        intro η ξ ω hm
        obtain ⟨ν, hνω, hcomp⟩ := comp.mapMark_support _ η ξ ω hm
        obtain ⟨s, t, ha, he'⟩ := a.compose_support P Q (M ((B \ E).erase x)) e' η ξ ν hcomp
        have heMass : (e s t).mass η ξ ν.2 ≠ 0 := he'
        have hsupp := he s t η ξ ν.2 heMass
        have hη : agrees (insert x E) (Function.update τ x s) η := by
          apply condition_support p hp _ _ η
          intro hz
          exact heMass ((e s t).mass_eq_zero_of_left hz ξ ν.2)
        have hξ : agrees (insert x E) (Function.update τ' x t) ξ := by
          apply condition_support q hq _ _ ξ
          intro hz
          exact heMass ((e s t).mass_eq_zero_of_right hz η ν.2)
        refine ⟨hsupp.1, connected_step Λ B T E hEB φ φ' τ τ' η ξ x hx s t hη hξ hsupp.2.1, ?_⟩
        intro z hz hneq
        by_cases hzx : z = x
        · subst z
          have hηx : η x = s := by simpa using hη x (mem_insert_self _ _)
          have hξx : ξ x = t := by simpa using hξ x (mem_insert_self _ _)
          have hb : ν.1 = true := by
            cases hb : ν.1
            · have hc := DisagreementMarks.preferredCoupling_closed_support cp cq
                (preferred h x) (preferred h x) (θ x) (hθ0 x) (hθ1 x) hcp hcq s t
                (by simpa only [hb] using ha)
              exact False.elim (hneq (by rw [hηx, hξx, hc.1, hc.2]))
            · rfl
          rw [← hνω]
          simpa using hb
        · have hz' : z ∈ B \ insert x E := by simpa [hzx] using hz
          have hzopen := hsupp.2.2 z hz' hneq
          rw [← hνω]
          simpa [hzx] using hzopen
      · let c0 := stoppedCoupling Λ h β B T E φ φ' τ τ'
          (no_frontier_separates Λ B T E φ φ' τ τ' hfront).1
          (no_frontier_separates Λ B T E φ φ' τ τ' hfront).2
        let c := MarkedCoupling.independentProduct c0 (M (B \ E))
        refine ⟨c, ?_⟩
        intro η ξ ω hm
        have hc0 : c0.mass η ξ ≠ 0 := by
          intro hz
          exact hm (by simp [c, MarkedCoupling.independentProduct, hz])
        have hident : ∀ z, z ∉ E → η z = ξ z :=
          stoppedCoupling_identical_unexplored Λ h β B T E φ φ' τ τ' _ _ η ξ hc0
        refine ⟨fun z hz => hident z (fun hzE => hz (hEB hzE)), ?_, ?_⟩
        · exact stoppedCoupling_connected Λ h β B T E φ φ' τ τ' hfront η ξ hc0
        · intro z hz hneq
          exact False.elim (hneq (hident z (mem_sdiff.mp hz).2))
  intro E hEB τ τ'
  exact hall (B \ E).card E rfl hEB τ τ'

/-- The final disagreement paths from any revealed/exterior sources are
contained in the independent forced-open root cluster. -/
theorem disagreement_cluster_from_sources (Λ : Lattice V) (B T E : Finset V)
    (φ φ' τ τ' η ξ : Config V) (ω : V → Bool) (y : V)
    (horigin : ∀ r, origin E T τ τ' φ φ' r → r = y)
    (hconnected : ConnectedDisagreements Λ B T E φ φ' τ τ' η ξ)
    (hopen : ∀ x ∈ B \ E, η x ≠ ξ x → ω x = true)
    (hη : agrees E τ η) (hξ : agrees E τ' ξ)
    (x : V) (hx : x ∈ B \ E) (hneq : η x ≠ ξ x) :
    x ∈ Percolation.cluster (latticeGraph Λ) (fun z => z = y ∨ ω z = true) y := by
  obtain ⟨r, hr, hpath⟩ := hconnected x hx hneq
  have hry := horigin r hr
  subst r
  have hsub : ∀ z, differenceOpen B T φ φ' η ξ z → z = y ∨ ω z = true := by
    intro z hz
    rcases hz with ⟨hzB, hzdiff⟩ | hzT
    · by_cases hzE : z ∈ E
      · exact Or.inl (horigin z (Or.inl ⟨hzE,
          by simpa only [hη z hzE, hξ z hzE] using hzdiff⟩))
      · exact Or.inr (hopen z (mem_sdiff.mpr ⟨hzB, hzE⟩) hzdiff)
    · exact Or.inl (horigin z (Or.inr hzT))
  refine ⟨Or.inl rfl, hpath.mono ?_⟩
  intro u v huv
  exact ⟨huv.1, hsub u huv.2.1, hsub v huv.2.2⟩

/-- Split the Hamming cost into its fixed revealed part and the newly sampled
part. Outside the original Gibbs domain the exploration samples identically. -/
theorem hamming_revealed_partition (B E : Finset V) (hEB : E ⊆ B)
    (τ τ' η ξ : Config V) (hη : agrees E τ η) (hξ : agrees E τ' ξ)
    (houtside : ∀ x, x ∉ B → η x = ξ x) :
    hamming η ξ = defectCount E τ' τ + ((B \ E).filter fun x => η x ≠ ξ x).card := by
  have he : (univ.filter fun x => η x ≠ ξ x) =
      (E.filter fun x => τ x ≠ τ' x) ∪ ((B \ E).filter fun x => η x ≠ ξ x) := by
    ext x
    by_cases hxE : x ∈ E
    · simp [hxE, hEB hxE, hη x hxE, hξ x hxE]
    · by_cases hxB : x ∈ B
      · simp [hxE, hxB]
      · simp [hxE, hxB, houtside x hxB]
  have hd : Disjoint (E.filter fun x => τ x ≠ τ' x)
      ((B \ E).filter fun x => η x ≠ ξ x) := by
    apply disjoint_left.mpr
    intro x hx hx'
    exact (mem_sdiff.mp (mem_filter.mp hx').1).2 (mem_filter.mp hx).1
  unfold hamming defectCount
  rw [he, card_union_of_disjoint hd]

/-- Pointwise forced-cluster domination including the fixed cost of revealed
spins, for the actual exploration joint law. -/
theorem hamming_le_revealed_forced_cluster (Λ : Lattice V) (B T E : Finset V)
    (hEB : E ⊆ B) (φ φ' τ τ' η ξ : Config V) (ω : V → Bool) (y : V)
    (horigin : ∀ r, origin E T τ τ' φ φ' r → r = y)
    (hsupp : ExplorationSupport Λ B T E φ φ' τ τ' η ξ ω)
    (hη : agrees E τ η) (hξ : agrees E τ' ξ) :
    hamming η ξ ≤ defectCount E τ' τ + min (B \ E).card (forcedClusterCard Λ ω y) := by
  rw [hamming_revealed_partition B E hEB τ τ' η ξ hη hξ hsupp.1]
  apply Nat.add_le_add_left
  apply le_min
  · exact card_filter_le _ _
  · apply card_le_card
    intro x hx
    obtain ⟨hxU, hneq⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_univ _, disagreement_cluster_from_sources Λ B T E
      φ φ' τ τ' η ξ ω y horigin hsupp.2.1 hsupp.2.2 hη hξ x hxU hneq⟩

/-- Actual finite Gibbs influence bound before summing the good-root tails.
It applies directly to conditional block kernels of the full system: take
`E` to be the complement of the updated block. The only premises describe
the graph, fields, and locations of the one-site boundary perturbation. -/
theorem gibbs_conditional_influence (Λ : Lattice V) (h : V → ℝ) (β K d : ℝ)
    (B T E : Finset V) (hBT : Disjoint B T) (hEB : E ⊆ B)
    (φ φ' τ τ' : Config V) (y : V)
    (hβ : 0 ≤ β) (hdeg : (Λ.maxDegree : ℝ) ≤ 2 * d)
    (hsource : ∀ r ∈ E, τ r ≠ τ' r → r = y)
    (hboundary : ∀ r ∈ T, φ r ≠ φ' r → r = y) :
    hammingWasserstein
      (condition (gibbs Λ h β B T φ) (gibbs_positive Λ h β B T φ) E τ)
      (condition (gibbs Λ h β B T φ') (gibbs_positive Λ h β B T φ') E τ') ≤
      (defectCount E τ' τ : ℝ) +
      (DisagreementMarks.productMarks (openingProbability h K (rho K d β))
        (openingProbability_nonneg h K _ (rho_pos _ _ _).le)
        (openingProbability_le_one h K _ (rho_lt_one _ _ _).le) (B \ E)).expect
        (fun ω => (min (B \ E).card (forcedClusterCard Λ ω y) : ℝ)) := by
  obtain ⟨c, hc⟩ := exists_marked_exploration Λ h β K d B T hBT φ φ' hβ hdeg E hEB τ τ'
  calc hammingWasserstein _ _ ≤ c.toCoupling.cost hammingR :=
      Wasserstein.le_cost hammingR_nonneg _
    _ ≤ _ := by
      have hcost := marked_cost_le c
        (fun ω => (defectCount E τ' τ : ℝ) + (min (B \ E).card (forcedClusterCard Λ ω y) : ℝ)) ?_
      · simpa only [FinProb.expect_add, FinProb.expect_const] using hcost
      · intro η ξ ω hm
        have hη : agrees E τ η := by
          apply condition_support _ _ E τ η
          intro hz
          exact hm (c.mass_eq_zero_of_left hz ξ ω)
        have hξ : agrees E τ' ξ := by
          apply condition_support _ _ E τ' ξ
          intro hz
          exact hm (c.mass_eq_zero_of_right hz η ω)
        have horigin : ∀ r, origin E T τ τ' φ φ' r → r = y := by
          intro r hr
          rcases hr with ⟨hr, hd⟩ | ⟨hr, hd⟩
          · exact hsource r hr hd
          · exact hboundary r hr hd
        have h := hamming_le_revealed_forced_cluster Λ B T E hEB φ φ' τ τ' η ξ ω y
          horigin (hc η ξ ω hm) hη hξ
        dsimp only
        unfold hammingR
        exact_mod_cast h

/-- The no-revelation form is the arbitrary-block disagreement-percolation
bound (3.8) averaged over the genuine independent marks. -/
theorem gibbs_boundary_influence (Λ : Lattice V) (h : V → ℝ) (β K d : ℝ)
    (B T : Finset V) (hBT : Disjoint B T) (φ φ' : Config V) (y : V)
    (hβ : 0 ≤ β) (hdeg : (Λ.maxDegree : ℝ) ≤ 2 * d)
    (hboundary : ∀ r ∈ T, φ r ≠ φ' r → r = y) :
    hammingWasserstein (gibbs Λ h β B T φ) (gibbs Λ h β B T φ') ≤
      (DisagreementMarks.productMarks (openingProbability h K (rho K d β))
        (openingProbability_nonneg h K _ (rho_pos _ _ _).le)
        (openingProbability_le_one h K _ (rho_lt_one _ _ _).le) B).expect
        (fun ω => (min B.card (forcedClusterCard Λ ω y) : ℝ)) := by
  simpa only [condition_empty, defectCount, filter_empty, card_empty, Nat.cast_zero,
    zero_add, sdiff_empty] using gibbs_conditional_influence Λ h β K d B T ∅ hBT
      (empty_subset B) φ φ' φ φ' y hβ hdeg (fun r hr => by simp at hr) hboundary

/-- On a finite graph, the paper's finite-subset definition of cluster size
agrees exactly with the cardinality of its actual reachable component. -/
theorem clusterAtLeast_iff_card (G : SimpleGraph V) (ω : V → Prop) (y : V) (r : ℕ) :
    Percolation.clusterAtLeast G ω y r ↔
      r ≤ (univ.filter fun x => x ∈ Percolation.cluster G ω y).card := by
  constructor
  · rintro ⟨S, hS, hsub⟩
    rw [← hS]
    apply card_le_card
    intro x hx
    exact mem_filter.mpr ⟨mem_univ _, hsub hx⟩
  · intro hr
    obtain ⟨S, hsub, hS⟩ := exists_subset_card_eq hr
    refine ⟨S, hS, ?_⟩
    intro x hx
    exact (mem_filter.mp (hsub hx)).2

theorem forcedClusterCard_update (Λ : Lattice V) (ω : V → Bool) (y : V) :
    forcedClusterCard Λ (Function.update ω y true) y = forcedClusterCard Λ ω y := by
  have he : (fun z => z = y ∨ Function.update ω y true z = true) =
      (fun z => z = y ∨ ω z = true) := by
    funext z
    apply propext
    by_cases hz : z = y <;> simp [hz]
  simp only [forcedClusterCard, he]

/-- Ordinary root clusters require an open root; after conditioning the root
open, the ordinary and forced clusters are the same actual graph component. -/
theorem clusterAtLeast_forced_iff (Λ : Lattice V) (ω : V → Bool) (y : V)
    (r : ℕ) (hr : 0 < r) :
    Percolation.clusterAtLeast (latticeGraph Λ) (fun z => ω z = true) y r ↔
      ω y = true ∧ r ≤ forcedClusterCard Λ ω y := by
  have hroot : Percolation.clusterAtLeast (latticeGraph Λ) (fun z => ω z = true) y r →
      ω y = true := by
    rintro ⟨S, hS, hsub⟩
    have hp : 0 < S.card := by omega
    obtain ⟨x, hx⟩ := card_pos.mp hp
    exact (hsub hx).1
  by_cases hy : ω y = true
  · have he : (fun z => z = y ∨ ω z = true) = (fun z => ω z = true) := by
      funext z
      apply propext
      constructor
      · rintro (rfl | hz)
        · exact hy
        · exact hz
      · exact Or.inr
    simp only [hy, true_and, forcedClusterCard, he]
    exact clusterAtLeast_iff_card _ _ _ _
  · constructor
    · intro h
      exact (hy (hroot h)).elim
    · rintro ⟨h, _⟩
      exact (hy h).elim

/-- The actual finite product-law form of paper (3.9). The root's ordinary
opening probability divides out exactly; all other marks retain their law. -/
theorem forced_cluster_probability (Λ : Lattice V) (θ : V → ℝ)
    (hθ0 : ∀ x, 0 ≤ θ x) (hθ1 : ∀ x, θ x ≤ 1)
    (U : Finset V) (y : V) (hy : y ∉ U) (hθy : 0 < θ y) (r : ℕ) (hr : 0 < r) :
    (DisagreementMarks.productMarks θ hθ0 hθ1 U).expect
      (fun ω => if r ≤ forcedClusterCard Λ ω y then 1 else 0) =
    (DisagreementMarks.productMarks θ hθ0 hθ1 (insert y U)).expect
      (fun ω => if Percolation.clusterAtLeast (latticeGraph Λ) (fun z => ω z = true) y r
        then 1 else 0) / θ y := by
  have h := DisagreementMarks.forcedRoot_event_div θ hθ0 hθ1 U y hy hθy
    (fun ω => r ≤ forcedClusterCard Λ ω y)
  simpa only [forcedClusterCard_update, ← clusterAtLeast_forced_iff Λ _ y r hr] using h

/-- The integer layer-cake estimate used when only intermediate cluster tails
are controlled. The last term covers all cluster sizes beyond the cutoff. -/
theorem truncated_integer_tail (N n r₀ s : ℕ) :
    (min N n : ℝ) ≤ (r₀ : ℝ) +
      (∑ r ∈ Ico r₀ s, if r < n then (1 : ℝ) else 0) +
      (N : ℝ) * (if s ≤ n then 1 else 0) := by
  have he : ((Ico r₀ s).filter fun r => r < n) = Ico r₀ (min s n) := by
    ext r
    simp only [mem_filter, mem_Ico, lt_min_iff]
    omega
  rw [sum_boole, he, Nat.card_Ico]
  by_cases hs : s ≤ n
  · simp only [hs, if_true, mul_one]
    have hn : min N n ≤ r₀ + (min s n - r₀) + N := by omega
    exact_mod_cast hn
  · simp only [hs, if_false, mul_zero, add_zero]
    have hn : min N n ≤ r₀ + (min s n - r₀) := by omega
    exact_mod_cast hn

/-- Summing the integer tails under an actual finite law. -/
theorem expected_truncated_tail {Ω : Type*} [Fintype Ω]
    (m : FinProb Ω) (X : Ω → ℕ) (N r₀ s : ℕ) :
    m.expect (fun ω => (min N (X ω) : ℝ)) ≤ (r₀ : ℝ) +
      (∑ r ∈ Ico r₀ s, m.expect (fun ω => if r < X ω then (1 : ℝ) else 0)) +
      (N : ℝ) * m.expect (fun ω => if s ≤ X ω then (1 : ℝ) else 0) := by
  have h := m.expect_mono (fun ω => truncated_integer_tail N (X ω) r₀ s)
  have he : m.expect (fun ω => ∑ r ∈ Ico r₀ s, if r < X ω then (1 : ℝ) else 0) =
      ∑ r ∈ Ico r₀ s, m.expect (fun ω => if r < X ω then (1 : ℝ) else 0) := by
    unfold FinProb.expect
    simp only [mul_sum]
    rw [sum_comm]
  simpa only [FinProb.expect_add, FinProb.expect_const, FinProb.expect_smul, he] using h

end Paper09.Disagreement
