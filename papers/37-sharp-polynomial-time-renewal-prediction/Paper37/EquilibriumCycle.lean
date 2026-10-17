import Paper37.SupportPrior
import Paper37.BackwardRender
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
Finite projections of the classical equilibrium renewal-cycle construction.
The external input at the end quantifies over every finite gap realization;
it contains no hard-prior, good-event, posterior, or loss conclusion.
-/
namespace Paper37.EquilibriumCycle
open scoped BigOperators
open Paper37.LowerBound Paper37.SupportPrior
noncomputable section

variable {α : Type*} [Fintype α]

def gapMean (P : FiniteLaw α) (d : α → ℕ) : ℝ := ∑ i, ((d i : ℝ)+1)*P.mass i

lemma gapMean_ge_one (P : FiniteLaw α) (d : α → ℕ) : 1 ≤ gapMean P d := by
  rw [← P.total]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [P.nonneg i, (Nat.cast_nonneg (d i) : (0:ℝ) ≤ (d i:ℝ))]

lemma gapMean_pos (P : FiniteLaw α) (d : α → ℕ) : 0 < gapMean P d :=
  lt_of_lt_of_le zero_lt_one (gapMean_ge_one P d)

abbrev Phase (d : α → ℕ) := (i : α) × Fin (d i+1)

def phaseLaw (P : FiniteLaw α) (d : α → ℕ) : FiniteLaw (Phase d) where
  mass s := P.mass s.1 / gapMean P d
  nonneg s := div_nonneg (P.nonneg s.1) (gapMean_pos P d).le
  total := by
    have hm : Paper37.Boundary.finiteMean (fun i => d i+1) P.mass = gapMean P d := by
      simp [Paper37.Boundary.finiteMean, gapMean, Nat.cast_add, Nat.cast_one]
    simpa [Paper37.Boundary.phaseWeight, hm] using
      Paper37.Boundary.phaseWeight_sum (fun i => d i+1) P.mass
        (by rw [hm]; exact (gapMean_pos P d).ne')

/-- The actual independent finite product law for n backward gaps. -/
def iidLaw (P : FiniteLaw α) (n : ℕ) : FiniteLaw (Fin n → α) where
  mass ds := ∏ i, P.mass (ds i)
  nonneg ds := Finset.prod_nonneg (fun i _ => P.nonneg (ds i))
  total := by
    rw [← Fintype.prod_sum]
    simp_rw [P.total]
    simp

lemma iidLaw_coordinate [DecidableEq α] (P : FiniteLaw α) (n : ℕ) (i : Fin n) (x : α) :
    (iidLaw P n).eventMass (fun ds => ds i = x) = P.mass x := by
  classical
  let f : Fin n → α → ℝ := fun j a => P.mass a * (if j = i then if a = x then 1 else 0 else 1)
  have hprod (ds : Fin n → α) :
      (∏ j, f j (ds j)) = if ds i = x then ∏ j, P.mass (ds j) else 0 := by
    simp only [f, Finset.prod_mul_distrib]
    have haux : (∏ j : Fin n, if j = i then if ds j = x then (1:ℝ) else 0 else 1) =
        if ds i = x then 1 else 0 := by simp
    rw [haux]
    split_ifs <;> simp
  unfold FiniteLaw.eventMass
  change (∑ ds : Fin n → α, if ds i = x then ∏ j, P.mass (ds j) else 0) = _
  simp_rw [← hprod]
  rw [← Fintype.prod_sum]
  have hsum (j : Fin n) : (∑ a, f j a) = if j = i then P.mass x else 1 := by
    by_cases hj : j = i
    · simp [f, hj]
    · simp only [f, if_neg hj, mul_one]
      exact P.total
  simp_rw [hsum]
  simp

def sampleLaw (P : FiniteLaw α) (d : α → ℕ) (n : ℕ) :
    FiniteLaw (Phase d × (Fin n → α)) := product (phaseLaw P d) (iidLaw P n)

def sampleWord (d : α → ℕ) (n : ℕ) (s : Phase d × (Fin n → α)) : List Bool :=
  Paper37.BackwardRender.render n s.1.2.val (List.ofFn (fun i => d (s.2 i)))

lemma sampleWord_length (d : α → ℕ) (n : ℕ) (s : Phase d × (Fin n → α)) :
    (sampleWord d n s).length = n := by
  exact Paper37.BackwardRender.render_length (by simp)

/-- Integration against the finite product, with its factors kept explicit. -/
lemma sampleLaw_expectation (P : FiniteLaw α) (d : α → ℕ) (n : ℕ)
    (f : Phase d × (Fin n → α) → ℝ) :
    (sampleLaw P d n).expectation f =
      (phaseLaw P d).expectation (fun p => (iidLaw P n).expectation (fun ds => f (p,ds))) :=
  product_expectation (phaseLaw P d) (iidLaw P n) (fun p ds => f (p,ds))

lemma uniform_gapMean (S : Finset ℕ) (hS : S.Nonempty) :
    gapMean (uniformOn S hS) (fun i : S => i.val) =
      Paper37.Renewal.mean (uniformSupportLaw S hS) := by
  rw [uniformSupportLaw_mean]
  unfold gapMean
  simp_rw [uniformOn_mass, mul_one_div]
  rw [← Finset.sum_div, S.sum_coe_sort (fun i : ℕ => (i:ℝ)+1)]

lemma uniform_realizes (S : Finset ℕ) (hS : S.Nonempty) (t : ℕ) :
    (uniformSupportLaw S hS).mass t =
      ∑ i : S, if i.val = t then (uniformOn S hS).mass i else 0 := by
  classical
  simp_rw [uniformOn_mass]
  rw [S.sum_coe_sort (fun i : ℕ => if i = t then (1:ℝ) / S.card else 0)]
  by_cases ht : t ∈ S
  · simp [ht]
  · simp [ht]

/-- The precise classical external input used below: every finite realization
of every finite-mean renewal Law has the equilibrium cycle/phase, independent
backward-gap finite projection. The phase mass is P(i)/mean, so cycle i has
size-biased mass (d(i)+1)P(i)/mean and the phase is uniform within that cycle.

This is the lattice finite-projection corollary of the stationary construction
in Arratia, Goldstein and Kochman, *Size bias for one and all*, Probability
Surveys 16 (2019), §3, p.18, DOI 10.1214/13-PS221; that discussion refers to
Thorisson, *Coupling, Stationarity, and Regeneration* (2000), Ch.8, Thm.8.1.
The discrete phase form is also displayed in the source paper, Appendix F.2.
It is an explicit theorem parameter, not a Lean axiom. All subsequent finite
normalization, parsing, collision, Markov and good-event estimates are proved.
-/
def EquilibriumCyclePrinciple : Prop :=
  ∀ (α : Type) [Fintype α] (P : FiniteLaw α) (d : α → ℕ)
    (μ : Paper37.Renewal.Law),
    (∀ t, μ.mass t = ∑ i, if d i = t then P.mass i else 0) →
    ∀ (n : ℕ) (w : List Bool), w.length = n →
      (sampleLaw P d n).eventMass (fun s => sampleWord d n s = w) =
        Paper37.Renewal.blockMass μ w

lemma uniform_word_mass (cycle : EquilibriumCyclePrinciple)
    (S : Finset ℕ) (hS : S.Nonempty) (n : ℕ) (w : List Bool) (hw : w.length = n) :
    (sampleLaw (uniformOn S hS) (fun i : S => i.val) n).eventMass
      (fun s => sampleWord (fun i : S => i.val) n s = w) =
        Paper37.Renewal.blockMass (uniformSupportLaw S hS) w :=
  cycle S (uniformOn S hS) (fun i : S => i.val) (uniformSupportLaw S hS)
    (uniform_realizes S hS) n w hw

end
end Paper37.EquilibriumCycle
