import MEJF.Setup
import Mathlib.Data.EReal.Operations

/-! # The endpoint rule with the source's infinite-endpoint convention

Radii and endpoints are computed in `EReal` from the actual learner and data.
Positive finite ranks are proved equal to the real-valued rule in `Setup`.
Zero inner or outer rank covers every response, and the independently defined
statistical supremum is then zero.
-/
namespace MEJF.ExtendedRule

open MeasureTheory Finset MEJF.Setup
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Inner score with ascending paper rank `n+1-t`, including the top endpoint
when `t=0`. -/
def radius {X : Type*} [MeasurableSpace X] {N n : ℕ}
    (A : Learner X n) (Z : Fin N → Block X n) (i k : Fin N) (t : ℕ) : EReal :=
  OrderStatistics.extended
    (fun j => ((|(Z i j).2 - pairPrediction A Z i k (Z i j).1| : ℝ) : EReal))
    (n + 1 - t)

def lowerEndpoint {X : Type*} [MeasurableSpace X] {m n : ℕ}
    (A : Learner X n) (Z : Fin (m+1) → Block X n) (i : Fin (m+1)) (j : Fin n)
    (t ell : ℕ) : EReal :=
  OrderStatistics.extended (fun k : Fin m =>
    (pairPrediction A Z i (i.succAbove k) (Z i j).1 : EReal) -
      radius A Z (i.succAbove k) i t) ell

def upperEndpoint {X : Type*} [MeasurableSpace X] {m n : ℕ}
    (A : Learner X n) (Z : Fin (m+1) → Block X n) (i : Fin (m+1)) (j : Fin n)
    (t ell : ℕ) : EReal :=
  OrderStatistics.extended (fun k : Fin m =>
    (pairPrediction A Z i (i.succAbove k) (Z i j).1 : EReal) +
      radius A Z (i.succAbove k) i t) (m + 1 - ell)

def covered {X : Type*} [MeasurableSpace X] {m n : ℕ}
    (A : Learner X n) (Z : Fin (m+1) → Block X n) (i : Fin (m+1)) (j : Fin n)
    (t ell : ℕ) : Prop :=
  ((Z i j).2 : EReal) ∈ Set.Icc (lowerEndpoint A Z i j t ell)
    (upperEndpoint A Z i j t ell)

def failure {X : Type*} [MeasurableSpace X] {m n : ℕ}
    (A : Learner X n) (Z : Fin (m+1) → Block X n) (i : Fin (m+1))
    (F t ell : ℕ) : Prop :=
  F ≤ (univ.filter fun j => ¬ covered A Z i j t ell).card

lemma stat_coe {n : ℕ} (u : Fin n → ℝ) (k : Fin n) :
    OrderStatistics.stat (fun j => (u j : EReal)) k =
      ((OrderStatistics.stat u k : ℝ) : EReal) :=
  OrderStatistics.stat_map_monotone u (fun x : ℝ => (x : EReal))
    (fun _ _ h => EReal.coe_le_coe h) k

lemma extended_const_bot {n r : ℕ} (hr : r ≤ n) :
    OrderStatistics.extended (fun _ : Fin n => (⊥ : EReal)) r = ⊥ := by
  by_cases hz : r = 0
  · simp [hz]
  · rw [OrderStatistics.extended_finite _ r (by omega) hr]
    rfl

lemma extended_const_top {n r : ℕ} (hr : 1 ≤ r) :
    OrderStatistics.extended (fun _ : Fin n => (⊤ : EReal)) r = ⊤ := by
  by_cases hn : r ≤ n
  · rw [OrderStatistics.extended_finite _ r hr hn]
    rfl
  · simp [OrderStatistics.extended, hn, show r ≠ 0 by omega]

@[simp] lemma radius_zero {X : Type*} [MeasurableSpace X] {N n : ℕ}
    (A : Learner X n) (Z : Fin N → Block X n) (i k : Fin N) :
    radius A Z i k 0 = ⊤ := by
  simp [radius]

@[simp] lemma lowerEndpoint_zero_outer {X : Type*} [MeasurableSpace X] {m n : ℕ}
    (A : Learner X n) (Z : Fin (m+1) → Block X n) (i : Fin (m+1)) (j : Fin n) (t : ℕ) :
    lowerEndpoint A Z i j t 0 = ⊥ := by simp [lowerEndpoint]

@[simp] lemma upperEndpoint_zero_outer {X : Type*} [MeasurableSpace X] {m n : ℕ}
    (A : Learner X n) (Z : Fin (m+1) → Block X n) (i : Fin (m+1)) (j : Fin n) (t : ℕ) :
    upperEndpoint A Z i j t 0 = ⊤ := by simp [upperEndpoint]

lemma lowerEndpoint_zero_inner {X : Type*} [MeasurableSpace X] {m n ell : ℕ}
    (A : Learner X n) (Z : Fin (m+1) → Block X n) (i : Fin (m+1)) (j : Fin n)
    (hell : ell ≤ m) : lowerEndpoint A Z i j 0 ell = ⊥ := by
  simp only [lowerEndpoint, radius_zero, EReal.sub_top]
  exact extended_const_bot hell

lemma upperEndpoint_zero_inner {X : Type*} [MeasurableSpace X] {m n ell : ℕ}
    (A : Learner X n) (Z : Fin (m+1) → Block X n) (i : Fin (m+1)) (j : Fin n)
    (hell : ell ≤ m) : upperEndpoint A Z i j 0 ell = ⊤ := by
  simp only [upperEndpoint, radius_zero, EReal.coe_add_top]
  exact extended_const_top (by omega)

lemma covered_zero_inner {X : Type*} [MeasurableSpace X] {m n ell : ℕ}
    (A : Learner X n) (Z : Fin (m+1) → Block X n) (i : Fin (m+1)) (j : Fin n)
    (hell : ell ≤ m) : covered A Z i j 0 ell := by
  simp [covered, lowerEndpoint_zero_inner A Z i j hell,
    upperEndpoint_zero_inner A Z i j hell]

lemma covered_zero_outer {X : Type*} [MeasurableSpace X] {m n : ℕ}
    (A : Learner X n) (Z : Fin (m+1) → Block X n) (i : Fin (m+1)) (j : Fin n) (t : ℕ) :
    covered A Z i j t 0 := by simp [covered]

/-- The two degenerate axes in (2.8) give no missed response, pointwise for every
actual learner and every data array. -/
theorem no_failure_zero_rank {X : Type*} [MeasurableSpace X] {m n F t ell : ℕ}
    (A : Learner X n) (Z : Fin (m+1) → Block X n) (i : Fin (m+1))
    (hF : 0 < F) (hell : ell ≤ m) (hz : t = 0 ∨ ell = 0) :
    ¬ failure A Z i F t ell := by
  have hc : ∀ j, covered A Z i j t ell := by
    rcases hz with rfl | rfl
    · exact fun j => covered_zero_inner A Z i j hell
    · exact fun j => covered_zero_outer A Z i j t
  have he : (univ.filter fun j => ¬ covered A Z i j t ell) = ∅ := by
    ext j
    simp [hc]
  unfold failure
  rw [he, card_empty]
  omega

lemma radius_finite {X : Type*} [MeasurableSpace X] {N n t : ℕ}
    (ht : 1 ≤ t ∧ t ≤ n) (A : Learner X n) (Z : Fin N → Block X n) (i k : Fin N) :
    radius A Z i k t = (Setup.radius A Z i k t ht : EReal) := by
  unfold radius
  rw [OrderStatistics.extended_finite _ (n + 1 - t) (by omega) (by omega), stat_coe]
  congr 1
  unfold Setup.radius Setup.innerIndex
  congr 1
  apply Fin.ext
  change n + 1 - t - 1 = n - t
  omega

lemma lowerEndpoint_finite {X : Type*} [MeasurableSpace X] {m n t ell : ℕ}
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (A : Learner X n) (Z : Fin (m+1) → Block X n) (i : Fin (m+1)) (j : Fin n) :
    lowerEndpoint A Z i j t ell = (Setup.lowerEndpoint A Z i j t ell ht he : EReal) := by
  unfold lowerEndpoint
  rw [OrderStatistics.extended_finite _ ell he.1 he.2]
  simp_rw [radius_finite ht, ← EReal.coe_sub]
  rw [stat_coe]
  rfl

lemma upperEndpoint_finite {X : Type*} [MeasurableSpace X] {m n t ell : ℕ}
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (A : Learner X n) (Z : Fin (m+1) → Block X n) (i : Fin (m+1)) (j : Fin n) :
    upperEndpoint A Z i j t ell = (Setup.upperEndpoint A Z i j t ell ht he : EReal) := by
  unfold upperEndpoint
  rw [OrderStatistics.extended_finite _ (m + 1 - ell) (by omega) (by omega)]
  simp_rw [radius_finite ht, ← EReal.coe_add]
  rw [stat_coe]
  congr 1
  unfold Setup.upperEndpoint Setup.upperIndex
  congr 1
  apply Fin.ext
  change m + 1 - ell - 1 = m - ell
  omega

lemma covered_finite {X : Type*} [MeasurableSpace X] {m n t ell : ℕ}
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (A : Learner X n) (Z : Fin (m+1) → Block X n) (i : Fin (m+1)) (j : Fin n) :
    covered A Z i j t ell ↔ Setup.covered A Z i j t ell ht he := by
  simp only [covered, lowerEndpoint_finite ht he, upperEndpoint_finite ht he,
    Setup.covered, Set.mem_Icc, EReal.coe_le_coe_iff]

lemma failure_finite {X : Type*} [MeasurableSpace X] {m n t ell : ℕ}
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m)
    (A : Learner X n) (Z : Fin (m+1) → Block X n) (i : Fin (m+1)) (F : ℕ) :
    failure A Z i F t ell ↔ Setup.failure A Z i F t ell ht he := by
  simp only [failure, Setup.failure, covered_finite ht he]

/-- Actual achievable probabilities of the EReal endpoint rule. -/
def minimaxValues (m n : ℕ) (alpha : ℝ) (t ell : ℕ) : Set ℝ :=
  {r : ℝ | ∃ (A : Learner UniversalCovariate n)
    (μ : Measure (Fin (m+1) → Block UniversalCovariate n)),
    IsProbabilityMeasure μ ∧ Exchangeability.Exchangeable μ ∧
    r = μ.real {Z | failure A Z (Fin.last m) (failureRank alpha n) t ell}}

/-- Statistical supremum for all integer ranks, with the infinite-endpoint
convention implemented above. It is not defined by a closed scalar formula. -/
def gamma (m n : ℕ) (alpha : ℝ) (t ell : ℕ) : ℝ :=
  sSup (minimaxValues m n alpha t ell)

lemma minimaxValues_nonempty (m n : ℕ) (alpha : ℝ) (t ell : ℕ) :
    (minimaxValues m n alpha t ell).Nonempty := by
  let A : Learner UniversalCovariate n := ⟨fun _ _ => 0, fun _ => measurable_const⟩
  let x : UniversalCovariate := ⟨0, by norm_num⟩
  let Z : Fin (m+1) → Block UniversalCovariate n := fun _ _ => (x, 0)
  let μ : Measure (Fin (m+1) → Block UniversalCovariate n) := Measure.dirac Z
  have hμ : Exchangeability.Exchangeable μ := by
    intro e
    have hm : Measurable (Exchangeability.relabel e :
        (Fin (m+1) → Block UniversalCovariate n) → _) :=
      measurable_pi_iff.mpr (fun i => measurable_pi_apply (e.symm i))
    refine ⟨hm, ?_⟩
    change Measure.map (Exchangeability.relabel e) (Measure.dirac Z) = Measure.dirac Z
    rw [Measure.map_dirac hm]
    rfl
  exact ⟨_, A, μ, by dsimp [μ]; infer_instance, hμ, rfl⟩

/-- Positive finite ranks recover exactly the original real-valued statistical
supremum. There is no conditional exact-law hypothesis in this bridge. -/
theorem gamma_finite (m n : ℕ) (alpha : ℝ) (t ell : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (he : 1 ≤ ell ∧ ell ≤ m) :
    gamma m n alpha t ell = Setup.finiteRankGamma m n alpha t ell ht he := by
  unfold gamma minimaxValues Setup.finiteRankGamma
  simp_rw [failure_finite ht he]

/-- Equation (2.8), proved for the statistical supremum over actual laws and
learners, rather than only for an arithmetic surrogate. -/
theorem gamma_zero (m n : ℕ) (alpha : ℝ) (t ell : ℕ)
    (hell : ell ≤ m) (hz : t = 0 ∨ ell = 0) : gamma m n alpha t ell = 0 := by
  have hF : 0 < failureRank alpha n := by unfold failureRank; omega
  have hall : ∀ r ∈ minimaxValues m n alpha t ell, r = 0 := by
    rintro r ⟨A, μ, hp, hx, hr⟩
    have hevent : {Z | failure A Z (Fin.last m) (failureRank alpha n) t ell} = ∅ := by
      ext Z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact no_failure_zero_rank A Z (Fin.last m) hF hell hz
    simpa only [hevent, measureReal_empty] using hr
  have hset : minimaxValues m n alpha t ell = {0} := by
    ext r
    constructor
    · intro hr
      simpa only [Set.mem_singleton_iff] using hall r hr
    · intro hr
      have hr0 : r = 0 := Set.mem_singleton_iff.mp hr
      subst r
      rcases minimaxValues_nonempty m n alpha t ell with ⟨v, hv⟩
      rw [hall v hv] at hv
      exact hv
  rw [gamma, hset, csSup_singleton]

end
end MEJF.ExtendedRule
