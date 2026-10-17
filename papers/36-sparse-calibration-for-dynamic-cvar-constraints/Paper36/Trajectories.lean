import Paper36.Simulation
import Paper36.Posterior
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Finite physical-state Markov trajectories and the actual conditional
visit-count identity used in Appendix C.8. -/
namespace Paper36.Trajectories
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
noncomputable section

universe u
variable {S A X Y : Type u} [Fintype S] [Fintype A]

/-- Finite-law integration against a finite probability kernel. -/
def bindLaw [Fintype X] [Fintype Y] (P : Law X) (Q : X → Law Y) : Law Y where
  mass y := ∑ x, P.mass x * (Q x).mass y
  nonneg y := Finset.sum_nonneg fun x _ => mul_nonneg (P.nonneg x) ((Q x).nonneg y)
  total := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, Law.total, mul_one]

lemma bindLaw_expect [Fintype X] [Fintype Y] (P : Law X) (Q : X → Law Y) (f : Y → ℝ) :
    expect (bindLaw P Q).mass f = expect P.mass (fun x => expect (Q x).mass f) := by
  simp only [expect, bindLaw, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- A trajectory with `n` actions records `n+1` physical states. -/
def Trajectory (S A : Type u) : ℕ → Type u
  | 0 => S
  | n+1 => S × (A × Trajectory S A n)

private def trajectoryFintype : (n : ℕ) → Fintype (Trajectory S A n)
  | 0 => by dsimp [Trajectory]; infer_instance
  | n+1 => by
    dsimp [Trajectory]
    letI := trajectoryFintype n
    infer_instance

instance instFintypeTrajectory (n : ℕ) : Fintype (Trajectory S A n) := trajectoryFintype n
instance instMeasurableSpaceTrajectory (n : ℕ) : MeasurableSpace (Trajectory S A n) := ⊤
instance instDiscreteMeasurableSpaceTrajectory (n : ℕ) :
    DiscreteMeasurableSpace (Trajectory S A n) := ⟨fun _ => trivial⟩

instance instNonemptyTrajectory [Nonempty S] [Nonempty A] (n : ℕ) :
    Nonempty (Trajectory S A n) := by
  induction n with
  | zero => dsimp [Trajectory]; infer_instance
  | succ n ih =>
    dsimp [Trajectory]
    letI := ih
    infer_instance

/-- The trajectory law is constructed from the selected action row and true
transition row at each step, including the observed final successor. -/
def trajectoryLaw (π : Policy S A) (p : Simulation.Kernel S A) :
    (n : ℕ) → ℕ → S → Law (Trajectory S A n)
  | 0, _, s => dirac s
  | n+1, h, s => joint (dirac s) (fun u => joint (π h u)
      (fun a => bindLaw (p u a) (fun t => trajectoryLaw π p n (h+1) t)))

/-- The number of observed visits to a state-action row along a finite trajectory. -/
def visitCount [DecidableEq S] [DecidableEq A] (row : S × A) :
    (n : ℕ) → Trajectory S A n → ℕ
  | 0, _ => 0
  | n+1, path => (if (path.1, path.2.1) = row then 1 else 0) + visitCount row n path.2.2

lemma visitCount_le [DecidableEq S] [DecidableEq A] (row : S × A) (n : ℕ)
    (path : Trajectory S A n) : visitCount row n path ≤ n := by
  induction n with
  | zero => simp [visitCount]
  | succ n ih =>
    dsimp [visitCount]
    have := ih path.2.2
    split <;> omega

/-- The expected count under the constructed physical-state Markov trajectory. -/
def expectedVisits [DecidableEq S] [DecidableEq A] (π : Policy S A)
    (p : Simulation.Kernel S A) (row : S × A) (n h : ℕ) (s : S) : ℝ :=
  expect (trajectoryLaw π p n h s).mass (fun path => (visitCount row n path : ℝ))

lemma expectedVisits_zero [DecidableEq S] [DecidableEq A] (π : Policy S A)
    (p : Simulation.Kernel S A) (row : S × A) (h : ℕ) (s : S) :
    expectedVisits π p row 0 h s = 0 := by simp [expectedVisits, visitCount, expect]

lemma expect_const_add [Fintype X] (P : Law X) (c : ℝ) (f : X → ℝ) :
    expect P.mass (fun x => c + f x) = c + expect P.mass f := by
  simp only [expect, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, P.total, one_mul]

/-- The count Bellman recursion is derived by integrating the actual trajectory law. -/
lemma expectedVisits_succ [DecidableEq S] [DecidableEq A] (π : Policy S A)
    (p : Simulation.Kernel S A) (row : S × A) (n h : ℕ) (s : S) :
    expectedVisits π p row (n+1) h s =
      (if s = row.1 then (π h s).mass row.2 else 0) +
      expect (nominal π p h s).mass (expectedVisits π p row n (h+1)) := by
  classical
  unfold expectedVisits
  rw [trajectoryLaw, expect_joint, show
    (∑ u, (dirac s).mass u * _) = _ from expect_dirac s _]
  simp only [expect_joint, bindLaw_expect, visitCount, Nat.cast_add, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  have hcont : (∑ a, (π h s).mass a *
      expect (p s a).mass (fun t =>
        expect (trajectoryLaw π p n (h+1) t).mass
          (fun path => (if (s,a)=row then (1:ℝ) else 0) + (visitCount row n path : ℝ)))) =
      (∑ a, (π h s).mass a * (if (s,a)=row then (1:ℝ) else 0)) +
        expect (nominal π p h s).mass
          (fun t => expect (trajectoryLaw π p n (h+1) t).mass
            (fun path => (visitCount row n path : ℝ))) := by
    simp_rw [expect_const_add]
    rw [nominal, stateMarginal_expect, expect_joint]
    simp only [expect, mul_add, Finset.sum_add_distrib]

  rw [hcont]
  congr 1
  rcases row with ⟨rs, ra⟩
  by_cases hs : s = rs
  · subst s
    simp only [Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_pos, ite_true]
  · simp [Prod.mk.injEq, hs]

/-- A finite-law Bellman equality telescopes along its constructed forward occupancies. -/
lemma unroll_eq (K : ℕ → S → Law S) (d₀ : Law S) (v e : ℕ → S → ℝ)
    (H : ℕ) (hstep : ∀ h, h < H → ∀ s,
      v h s = expect (K h s).mass (v (h+1)) + e h s) :
    expect d₀.mass (v 0) = expect (occupancy K d₀ H).mass (v H) +
      ∑ h ∈ Finset.range H, expect (occupancy K d₀ h).mass (e h) := by
  have hs : ∀ n, n ≤ H → expect d₀.mass (v 0) =
      expect (occupancy K d₀ n).mass (v n) +
        ∑ h ∈ Finset.range n, expect (occupancy K d₀ h).mass (e h) := by
    intro n
    induction n with
    | zero => simp [occupancy]
    | succ n ih =>
      intro hn
      have hi := ih (by omega)
      have he : expect (occupancy K d₀ n).mass (v n) =
          expect (occupancy K d₀ (n+1)).mass (v (n+1)) +
            expect (occupancy K d₀ n).mass (e n) := by
        rw [occupancy, advance_expect]
        simp only [expect, ← Finset.sum_add_distrib, ← mul_add]
        apply Finset.sum_congr rfl
        intro s _
        rw [hstep n (by omega) s]
        rfl
      rw [hi, he, Finset.sum_range_succ]
      ring
  exact hs H le_rfl

/-- The exact nominal occupancy/count identity for the source's finite trajectory,
with no occupancy identity included as a premise. -/
theorem expectedVisits_eq_occupancy [DecidableEq S] [DecidableEq A]
    (π : Policy S A) (p : Simulation.Kernel S A) (row : S × A) (H : ℕ) (s₀ : S) :
    expectedVisits π p row H 0 s₀ = ∑ h ∈ Finset.range H,
      (occupancy (nominal π p) (dirac s₀) h).mass row.1 * (π h row.1).mass row.2 := by
  classical
  let v : ℕ → S → ℝ := fun h s => expectedVisits π p row (H-h) h s
  let e : ℕ → S → ℝ := fun h s => if s = row.1 then (π h s).mass row.2 else 0
  have hstep : ∀ h, h < H → ∀ s,
      v h s = expect (nominal π p h s).mass (v (h+1)) + e h s := by
    intro h hh s
    have heq : H - h = (H-(h+1))+1 := by omega
    dsimp [v, e]
    rw [heq, expectedVisits_succ]
    ring
  have hu := unroll_eq (nominal π p) (dirac s₀) v e H hstep
  rw [expect_dirac] at hu
  have hvH : v H = fun _ => 0 := by funext s; simp [v, expectedVisits_zero]
  rw [hvH, expect_const (occupancy (nominal π p) (dirac s₀) H).total] at hu
  simp only [v, Nat.sub_zero, zero_add] at hu
  rw [hu]
  apply Finset.sum_congr rfl
  intro h _
  simp [expect, e]

/-- Conversion of a real finite law to a genuine Mathlib probability mass function. -/
def lawPMF [Fintype X] (P : Law X) : PMF X :=
  PMF.ofFintype (fun x => ENNReal.ofReal (P.mass x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => P.nonneg x), P.total]
    norm_num)

/-- A genuine measure associated with a finite law. -/
def lawMeasure [Fintype X] [MeasurableSpace X] (P : Law X) : Measure X := (lawPMF P).toMeasure

instance lawMeasure_probability [Fintype X] [MeasurableSpace X] (P : Law X) :
    IsProbabilityMeasure (lawMeasure P) := by unfold lawMeasure; infer_instance

lemma integral_lawMeasure [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : Law X) (f : X → ℝ) : (∫ x, f x ∂lawMeasure P) = expect P.mass f := by
  rw [lawMeasure, PMF.integral_eq_sum]
  simp only [lawPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal (P.nonneg _), smul_eq_mul, expect]

/-- Finite measurable probability rows define an actual Markov kernel. -/
def lawKernel {Info : Type*} [MeasurableSpace Info]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : Info → Law X) (hP : ∀ x, Measurable (fun i => (P i).mass x)) :
    ProbabilityTheory.Kernel Info X where
  toFun i := lawMeasure (P i)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro B hB
    simp only [lawMeasure, PMF.toMeasure_apply_fintype, lawPMF, PMF.ofFintype_apply]
    apply Finset.measurable_sum
    intro x _
    by_cases hx : x ∈ B
    · simpa only [Set.indicator_of_mem hx] using (hP x).ennreal_ofReal
    · simp only [Set.indicator_of_notMem hx]
      exact measurable_const

instance lawKernel_markov {Info : Type*} [MeasurableSpace Info]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : Info → Law X) (hP : ∀ x, Measurable (fun i => (P i).mass x)) :
    IsMarkovKernel (lawKernel P hP) := ⟨fun i => lawMeasure_probability (P i)⟩

lemma measurable_trajectory_mass {Info : Type*} [MeasurableSpace Info]
    (πOf : Info → Policy S A) (pOf : Info → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun i => (πOf i h s).mass a))
    (hp : ∀ s a t, Measurable (fun i => (pOf i s a).mass t))
    (n h : ℕ) (s : S) (path : Trajectory S A n) :
    Measurable (fun i => (trajectoryLaw (πOf i) (pOf i) n h s).mass path) := by
  induction n generalizing h s with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun i => (dirac s).mass path.1 *
      ((πOf i h path.1).mass path.2.1 * ∑ t, (pOf i path.1 path.2.1).mass t *
        (trajectoryLaw (πOf i) (pOf i) n (h+1) t).mass path.2.2))
    exact measurable_const.mul ((hπ h path.1 path.2.1).mul
      (Finset.measurable_sum _ fun t _ => (hp path.1 path.2.1 t).mul (ih (h+1) t path.2.2)))

/-- The canonical measurable kernel for a physical-state Markov episode. -/
def trajectoryKernel {Info : Type*} [MeasurableSpace Info]
    (πOf : Info → Policy S A) (pOf : Info → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun i => (πOf i h s).mass a))
    (hp : ∀ s a t, Measurable (fun i => (pOf i s a).mass t))
    (H : ℕ) (s₀ : S) : ProbabilityTheory.Kernel Info (Trajectory S A H) :=
  lawKernel (fun i => trajectoryLaw (πOf i) (pOf i) H 0 s₀)
    (measurable_trajectory_mass πOf pOf hπ hp H 0 s₀)

instance trajectoryKernel_markov {Info : Type*} [MeasurableSpace Info]
    (πOf : Info → Policy S A) (pOf : Info → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun i => (πOf i h s).mass a))
    (hp : ∀ s a t, Measurable (fun i => (pOf i s a).mass t))
    (H : ℕ) (s₀ : S) : IsMarkovKernel (trajectoryKernel πOf pOf hπ hp H s₀) :=
  lawKernel_markov _ _

/-- The model's row count has the claimed expectation under its actual trajectory measure. -/
theorem integral_visitCount_eq_occupancy [DecidableEq S] [DecidableEq A]
    (π : Policy S A) (p : Simulation.Kernel S A) (row : S × A) (H : ℕ) (s₀ : S) :
    (∫ path, (visitCount row H path : ℝ) ∂lawMeasure (trajectoryLaw π p H 0 s₀)) =
      ∑ h ∈ Finset.range H,
        (occupancy (nominal π p) (dirac s₀) h).mass row.1 * (π h row.1).mass row.2 := by
  rw [integral_lawMeasure]
  exact expectedVisits_eq_occupancy π p row H s₀

lemma law_mass_le_one [Fintype X] (P : Law X) (x : X) : P.mass x ≤ 1 := by
  have h := Finset.single_le_sum (s := Finset.univ) (f := P.mass)
    (fun y _ => P.nonneg y) (Finset.mem_univ x)
  exact h.trans_eq P.total

/-- The same forward occupancy used by Simulation is measurable in the actual
policy and transition entries. -/
lemma measurable_occupancy_mass {Info : Type*} [MeasurableSpace Info]
    (πOf : Info → Policy S A) (pOf : Info → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun i => (πOf i h s).mass a))
    (hp : ∀ s a t, Measurable (fun i => (pOf i s a).mass t))
    (s₀ : S) (h : ℕ) (s : S) :
    Measurable (fun i => (occupancy (nominal (πOf i) (pOf i)) (dirac s₀) h).mass s) := by
  induction h generalizing s with
  | zero => exact measurable_const
  | succ h ih =>
    change Measurable (fun i => ∑ t,
      (occupancy (nominal (πOf i) (pOf i)) (dirac s₀) h).mass t *
        ∑ a, (πOf i h t).mass a * (pOf i t a).mass s)
    exact Finset.measurable_sum _ fun t _ => (ih t).mul
      (Finset.measurable_sum _ fun a _ => (hπ h t a).mul (hp t a s))

def nominalVisits (π : Policy S A) (p : Simulation.Kernel S A) (s₀ : S)
    (L : ℕ) (row : S × A) : ℝ :=
  ∑ h ∈ Finset.range L,
    (occupancy (nominal π p) (dirac s₀) h).mass row.1 * (π h row.1).mass row.2

lemma nominalVisits_nonneg (π : Policy S A) (p : Simulation.Kernel S A) (s₀ : S)
    (L : ℕ) (row : S × A) : 0 ≤ nominalVisits π p s₀ L row :=
  Finset.sum_nonneg fun h _ => mul_nonneg
    ((occupancy (nominal π p) (dirac s₀) h).nonneg row.1) ((π h row.1).nonneg row.2)

lemma nominalVisits_le (π : Policy S A) (p : Simulation.Kernel S A) (s₀ : S)
    (L : ℕ) (row : S × A) : nominalVisits π p s₀ L row ≤ L := by
  calc
    nominalVisits π p s₀ L row ≤ ∑ _h ∈ Finset.range L, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro h _
      exact law_mass_le_one (joint (occupancy (nominal π p) (dirac s₀) h) (π h)) row
    _ = L := by simp

lemma nominalVisits_mono (π : Policy S A) (p : Simulation.Kernel S A) (s₀ : S)
    {L H : ℕ} (hLH : L ≤ H) (row : S × A) :
    nominalVisits π p s₀ L row ≤ nominalVisits π p s₀ H row := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hLH)
  intro h _ _
  exact mul_nonneg ((occupancy (nominal π p) (dirac s₀) h).nonneg row.1)
    ((π h row.1).nonneg row.2)

lemma measurable_nominalVisits {Info : Type*} [MeasurableSpace Info]
    (πOf : Info → Policy S A) (pOf : Info → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun i => (πOf i h s).mass a))
    (hp : ∀ s a t, Measurable (fun i => (pOf i s a).mass t))
    (s₀ : S) (L : ℕ) (row : S × A) :
    Measurable (fun i => nominalVisits (πOf i) (pOf i) s₀ L row) :=
  Finset.measurable_sum _ fun h _ =>
    (measurable_occupancy_mass πOf pOf hπ hp s₀ h row.1).mul (hπ h row.1 row.2)

section ConditionalLearner

variable {Ω Info : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace Info]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A]

/-- The conditional expected visit count is proved from the episode's actual
conditional trajectory law. In particular, an occupancy identity is not a
premise: it is obtained by integrating the finite Markov trajectory measure. -/
theorem conditional_visitCount_eq_occupancy
    (πOf : Info → Policy S A) (pOf : Info → Simulation.Kernel S A)
    (H : ℕ) (s₀ : S) (info : Ω → Info) (path : Ω → Trajectory S A H)
    (κ : ProbabilityTheory.Kernel Info (Trajectory S A H))
    (hκ : ∀ i, κ i = lawMeasure (trajectoryLaw (πOf i) (pOf i) H 0 s₀))
    (hi : Measurable info) (hp : AEMeasurable path μ)
    (hmodel : condDistrib path info μ =ᵐ[μ.map info] κ) (row : S × A) :
    μ[fun ω => (visitCount row H (path ω) : ℝ) |
      MeasurableSpace.comap info inferInstance] =ᵐ[μ]
      fun ω => ∑ h ∈ Finset.range H,
        (occupancy (nominal (πOf (info ω)) (pOf (info ω))) (dirac s₀) h).mass row.1 *
          (πOf (info ω) h row.1).mass row.2 := by
  have hf : StronglyMeasurable (fun path : Trajectory S A H => (visitCount row H path : ℝ)) :=
    .of_discrete
  have hfi : Integrable (fun ω => (visitCount row H (path ω) : ℝ)) μ := by
    apply Integrable.of_bound ((hf.measurable.comp_aemeasurable hp).aestronglyMeasurable) H
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    change (visitCount row H (path ω) : ℝ) ≤ (H : ℝ)
    exact_mod_cast visitCount_le row H (path ω)
  have hce := condExp_ae_eq_integral_condDistrib hi hp hf hfi
  have hmodel' := ae_of_ae_map hi.aemeasurable hmodel
  filter_upwards [hce, hmodel'] with ω hce hmodel
  rw [hce, hmodel, hκ]
  exact integral_visitCount_eq_occupancy (πOf (info ω)) (pOf (info ω)) row H s₀

/-- The source conditional visit identity with the explicit episode kernel. -/
theorem conditional_visitCount_of_trajectoryKernel
    (πOf : Info → Policy S A) (pOf : Info → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun i => (πOf i h s).mass a))
    (htrans : ∀ s a t, Measurable (fun i => (pOf i s a).mass t))
    (H : ℕ) (s₀ : S) (info : Ω → Info) (path : Ω → Trajectory S A H)
    (hi : Measurable info) (hp : AEMeasurable path μ)
    (hmodel : condDistrib path info μ =ᵐ[μ.map info]
      trajectoryKernel πOf pOf hπ htrans H s₀) (row : S × A) :
    μ[fun ω => (visitCount row H (path ω) : ℝ) |
      MeasurableSpace.comap info inferInstance] =ᵐ[μ]
      fun ω => ∑ h ∈ Finset.range H,
        (occupancy (nominal (πOf (info ω)) (pOf (info ω))) (dirac s₀) h).mass row.1 *
          (πOf (info ω) h row.1).mass row.2 :=
  conditional_visitCount_eq_occupancy πOf pOf H s₀ info path
    (trajectoryKernel πOf pOf hπ htrans H s₀) (fun _ => rfl) hi hp hmodel row

/-- Equation C.8 for every bounded nonnegative predictable weight, proved from
the conditional trajectory law and the weighted tower property. -/
theorem weighted_visit_identity
    (πOf : Info → Policy S A) (pOf : Info → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun i => (πOf i h s).mass a))
    (htrans : ∀ s a t, Measurable (fun i => (pOf i s a).mass t))
    (H : ℕ) (s₀ : S) (info : Ω → Info) (path : Ω → Trajectory S A H)
    (hi : Measurable info) (hp : AEMeasurable path μ)
    (hmodel : condDistrib path info μ =ᵐ[μ.map info]
      trajectoryKernel πOf pOf hπ htrans H s₀)
    (weight : Info → ℝ) (hw : Measurable weight) (hwb : ∀ i, 0 ≤ weight i ∧ weight i ≤ 1)
    (row : S × A) :
    (∫ ω, weight (info ω) * nominalVisits (πOf (info ω)) (pOf (info ω)) s₀ H row ∂μ) =
      ∫ ω, weight (info ω) * (visitCount row H (path ω) : ℝ) ∂μ := by
  have hce := conditional_visitCount_of_trajectoryKernel πOf pOf hπ htrans H s₀
    info path hi hp hmodel row
  have hcmeas : AEStronglyMeasurable (fun ω => (visitCount row H (path ω) : ℝ)) μ :=
    ((Measurable.of_discrete : Measurable (fun path : Trajectory S A H =>
      (visitCount row H path : ℝ))).comp_aemeasurable hp).aestronglyMeasurable
  have hci : Integrable (fun ω => (visitCount row H (path ω) : ℝ)) μ := by
    apply Integrable.of_bound hcmeas H
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast visitCount_le row H (path ω)
  have hwc : Integrable (fun ω => weight (info ω) * (visitCount row H (path ω) : ℝ)) μ := by
    apply Integrable.of_bound ((hw.comp hi).aestronglyMeasurable.mul hcmeas) H
    filter_upwards with ω
    change ‖weight (info ω) * (visitCount row H (path ω) : ℝ)‖ ≤ (H : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hwb _).1 (Nat.cast_nonneg _))]
    have hc : (visitCount row H (path ω) : ℝ) ≤ H := by exact_mod_cast visitCount_le row H (path ω)
    exact (mul_le_mul_of_nonneg_right (hwb _).2 (Nat.cast_nonneg _)).trans (by simpa using hc)
  have hwsm : StronglyMeasurable[MeasurableSpace.comap info inferInstance]
      (fun ω => weight (info ω)) :=
    hw.stronglyMeasurable.comp_measurable (Measurable.of_comap_le le_rfl)
  calc
    (∫ ω, weight (info ω) * nominalVisits (πOf (info ω)) (pOf (info ω)) s₀ H row ∂μ) =
        ∫ ω, weight (info ω) *
          (μ[fun ω => (visitCount row H (path ω) : ℝ)|MeasurableSpace.comap info inferInstance]) ω ∂μ := by
      apply integral_congr_ae
      filter_upwards [hce] with ω hω
      rw [hω]
      rfl
    _ = ∫ ω, weight (info ω) * (visitCount row H (path ω) : ℝ) ∂μ :=
      Paper36.Posterior.weighted_conditional_expectation hi.comap_le hwsm hci hwc

/-- Truncating to the H-1 error-producing stages only decreases a nonnegative
weighted occupancy sum. -/
theorem weighted_partial_visit_le
    (πOf : Info → Policy S A) (pOf : Info → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun i => (πOf i h s).mass a))
    (htrans : ∀ s a t, Measurable (fun i => (pOf i s a).mass t))
    (H L : ℕ) (hLH : L ≤ H) (s₀ : S) (info : Ω → Info) (path : Ω → Trajectory S A H)
    (hi : Measurable info) (hp : AEMeasurable path μ)
    (hmodel : condDistrib path info μ =ᵐ[μ.map info]
      trajectoryKernel πOf pOf hπ htrans H s₀)
    (weight : Info → ℝ) (hw : Measurable weight) (hwb : ∀ i, 0 ≤ weight i ∧ weight i ≤ 1)
    (row : S × A) :
    (∫ ω, weight (info ω) * nominalVisits (πOf (info ω)) (pOf (info ω)) s₀ L row ∂μ) ≤
      ∫ ω, weight (info ω) * (visitCount row H (path ω) : ℝ) ∂μ := by
  have hiL (J : ℕ) : Integrable (fun ω =>
      weight (info ω) * nominalVisits (πOf (info ω)) (pOf (info ω)) s₀ J row) μ := by
    have hmeas := (hw.comp hi).mul ((measurable_nominalVisits πOf pOf hπ htrans s₀ J row).comp hi)
    apply Integrable.of_bound hmeas.aestronglyMeasurable J
    filter_upwards with ω
    change ‖weight (info ω) * nominalVisits (πOf (info ω)) (pOf (info ω)) s₀ J row‖ ≤ (J : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hwb _).1 (nominalVisits_nonneg _ _ _ _ _))]
    exact (mul_le_mul_of_nonneg_right (hwb _).2 (nominalVisits_nonneg _ _ _ _ _)).trans
      (by simpa using nominalVisits_le (πOf (info ω)) (pOf (info ω)) s₀ J row)
  calc
    _ ≤ ∫ ω, weight (info ω) * nominalVisits (πOf (info ω)) (pOf (info ω)) s₀ H row ∂μ :=
      integral_mono_ae (hiL L) (hiL H) (ae_of_all _ fun ω =>
        mul_le_mul_of_nonneg_left (nominalVisits_mono _ _ _ hLH row) (hwb _).1)
    _ = _ := weighted_visit_identity πOf pOf hπ htrans H s₀ info path hi hp hmodel weight hw hwb row

end ConditionalLearner

end
end Paper36.Trajectories
