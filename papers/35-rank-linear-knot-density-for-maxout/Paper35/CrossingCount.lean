import Paper35.CrossingArea
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace Paper35.Source.CrossingCount
open CrossingJacobian CrossingArea

/-- An indicator mark counts the selected actual preimages. -/
theorem fiberMass_indicator {E : Type*} (f : E → E) (s P : Set E) (y : E) :
    AreaFormula.fiberMass f s (P.indicator (fun _ => (1 : ℝ≥0∞))) y =
      ({x | x ∈ s ∧ f x = y ∧ x ∈ P}.encard : ℝ≥0∞) := by
  classical
  let F : Set E := {x | x ∈ s ∧ f x = y}
  let V : Set F := {x | x.1 ∈ P}
  let W : Set E := {x | x ∈ s ∧ f x = y ∧ x ∈ P}
  let e : V ≃ W :=
    { toFun := fun x => ⟨x.1.1, x.1.2.1, x.1.2.2, x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1, x.2.2.1⟩, x.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    AreaFormula.fiberMass f s (P.indicator (fun _ => (1 : ℝ≥0∞))) y =
        ∑' x : F, V.indicator (fun _ => (1 : ℝ≥0∞)) x := by
      apply tsum_congr
      intro x
      by_cases hx : x.1 ∈ P
      · simp [V, hx]
      · simp [V, hx]
    _ = ∑' _ : V, (1 : ℝ≥0∞) := (tsum_subtype V (fun _ => (1 : ℝ≥0∞))).symm
    _ = ∑' _ : W, (1 : ℝ≥0∞) := e.tsum_eq (fun _ => (1 : ℝ≥0∞))
    _ = (W.encard : ℝ≥0∞) := ENNReal.tsum_set_one W

/-- A target weight is constant along each actual fiber. -/
theorem fiberMass_mul_comp {E : Type*} (f : E → E) (s : Set E)
    (a ρ : E → ℝ≥0∞) (y : E) :
    AreaFormula.fiberMass f s (fun x => a x * ρ (f x)) y =
      AreaFormula.fiberMass f s a y * ρ y := by
  unfold AreaFormula.fiberMass
  calc
    (∑' x : {x | x ∈ s ∧ f x = y}, a x * ρ (f x)) =
        ∑' x : {x | x ∈ s ∧ f x = y}, a x * ρ y := by
      apply tsum_congr
      intro x
      rw [x.2.2]
    _ = (∑' x : {x | x ∈ s ∧ f x = y}, a x) * ρ y := ENNReal.tsum_mul_right

variable {d K : ℕ}

/-- The proved null-bias exclusion persists under every absolutely
continuous conditional bias-pair law, including heterogeneous densities. -/
theorem ae_not_exceptional_of_absolutelyContinuous (p : Probe d) (wi wj : Space d)
    (ν : Measure (ℝ × ℝ)) (hν : ν ≪ (volume : Measure (ℝ × ℝ))) :
    ∀ᵐ ξ ∂ν, ξ ∉ exceptionalBiases p wi wj :=
  hν.ae_le (measure_eq_zero_iff_ae_notMem.mp (exceptionalBiases_null p wi wj))

/-- Fixed weights may have any two different conditional density factors.
The bias weighting is transported through the actual marked area formula. -/
theorem phi_weighted_marked_area (p : Probe d) (wi wj : Space d)
    (D : Set (ℝ × ℝ)) (hD : MeasurableSet D) (hsub : D ⊆ strip p)
    (a : (ℝ × ℝ) → ℝ≥0∞) (ha : Measurable (D.restrict a))
    (ρ : (ℝ × ℝ) → ℝ≥0∞) (hρ : Measurable ρ) :
    (∫⁻ ξ, AreaFormula.fiberMass (phi p wi wj) D a ξ * ρ ξ) =
      ∫⁻ z in D, (a z * ρ (phi p wi wj z)) * ENNReal.ofReal
        (|inner ℝ (wi - wj) (deriv p.curve z.1)|) := by
  have hφ : Measurable (D.restrict (phi p wi wj)) :=
    (continuousOn_iff_continuous_restrict.mp
      ((phi_lipschitzOn p wi wj).continuousOn.mono hsub)).measurable
  have hm : Measurable (D.restrict (fun z => a z * ρ (phi p wi wj z))) :=
    ha.mul (hρ.comp hφ)
  have h := phi_marked_area_on p wi wj D hD hsub (fun z => a z * ρ (phi p wi wj z)) hm
  simpa only [fiberMass_mul_comp] using h.symm

/-- The remaining candidates are strictly below the pair's common height. -/
def visibilitySet (p : Probe d) (θ : Fin K → Candidate d) (q : OrderedCandidatePair K) :
    Set (ℝ × ℝ) :=
  {z | ∀ k, k ≠ q.1.1 → k ≠ q.1.2 → WeightedModel.scores p θ k z.1 < z.2}

def visibilityMark (p : Probe d) (θ : Fin K → Candidate d) (q : OrderedCandidatePair K) :
    (ℝ × ℝ) → ℝ≥0∞ := (visibilitySet p θ q).indicator (fun _ => 1)

/-- Selected visible fibers and the actual pair switch set are equivalent
outside the concrete null bias set. -/
def visibleFiberEquiv (p : Probe d) (θ : Fin K → Candidate d) (q : OrderedCandidatePair K)
    (hgood : ((θ q.1.1).2, (θ q.1.2).2) ∉
      exceptionalBiases p (θ q.1.1).1 (θ q.1.2).1) :
    {z : ℝ × ℝ | z ∈ Ioo 0 p.length ×ˢ (univ : Set ℝ) ∧
      phi p (θ q.1.1).1 (θ q.1.2).1 z = ((θ q.1.1).2, (θ q.1.2).2) ∧
      z ∈ visibilitySet p θ q} ≃
      pairSwitchSet (WeightedModel.scores p θ) p.length q where
  toFun z := by
    refine ⟨z.1.1, ?_⟩
    rw [pairSwitchSet_eq_visibleEqualityTimes p θ q hgood]
    have hi := congrArg Prod.fst z.2.2.1
    have hj := congrArg Prod.snd z.2.2.1
    change z.1.2 - inner ℝ (θ q.1.1).1 (p.curve z.1.1) = (θ q.1.1).2 at hi
    change z.1.2 - inner ℝ (θ q.1.2).1 (p.curve z.1.1) = (θ q.1.2).2 at hj
    have hheight : WeightedModel.scores p θ q.1.1 z.1.1 = z.1.2 := by
      change inner ℝ (θ q.1.1).1 (p.curve z.1.1) + (θ q.1.1).2 = z.1.2
      linarith
    refine ⟨z.2.1.1, ⟨?_, ?_⟩⟩
    · change inner ℝ (θ q.1.1).1 (p.curve z.1.1) + (θ q.1.1).2 =
        inner ℝ (θ q.1.2).1 (p.curve z.1.1) + (θ q.1.2).2
      linarith
    · intro k hki hkj
      rw [hheight]
      exact z.2.2.2 k hki hkj
  invFun s := by
    let y := WeightedModel.scores p θ q.1.1 s.1
    refine ⟨(s.1, y), ⟨⟨s.2.1, s.2.2.1⟩, mem_univ _⟩, ?_, ?_⟩
    · apply Prod.ext
      · change (inner ℝ (θ q.1.1).1 (p.curve s.1) + (θ q.1.1).2) -
          inner ℝ (θ q.1.1).1 (p.curve s.1) = (θ q.1.1).2
        ring
      · change (inner ℝ (θ q.1.1).1 (p.curve s.1) + (θ q.1.1).2) -
          inner ℝ (θ q.1.2).1 (p.curve s.1) = (θ q.1.2).2
        have heq := s.2.2.2.1.1
        change inner ℝ (θ q.1.1).1 (p.curve s.1) + (θ q.1.1).2 =
          inner ℝ (θ q.1.2).1 (p.curve s.1) + (θ q.1.2).2 at heq
        linarith
    · exact s.2.2.2.1.2
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hi := congrArg Prod.fst z.2.2.1
      change z.1.2 - inner ℝ (θ q.1.1).1 (p.curve z.1.1) = (θ q.1.1).2 at hi
      change inner ℝ (θ q.1.1).1 (p.curve z.1.1) + (θ q.1.1).2 = z.1.2
      linarith
  right_inv s := by
    apply Subtype.ext
    rfl

/-- The visible marked fiber count equals the actual Definition 2.1 pair count.
This is a pointwise statement outside an explicitly proved null bias set. -/
theorem visibility_fiberMass_eq_pairSwitchCount (p : Probe d)
    (θ : Fin K → Candidate d) (q : OrderedCandidatePair K)
    (hgood : ((θ q.1.1).2, (θ q.1.2).2) ∉
      exceptionalBiases p (θ q.1.1).1 (θ q.1.2).1) :
    AreaFormula.fiberMass (phi p (θ q.1.1).1 (θ q.1.2).1)
      (Ioo 0 p.length ×ˢ univ) (visibilityMark p θ q)
      ((θ q.1.1).2, (θ q.1.2).2) =
      ((pairSwitchSet (WeightedModel.scores p θ) p.length q).encard : ℝ≥0∞) := by
  rw [visibilityMark, fiberMass_indicator]
  exact congrArg ENat.toENNReal (Set.encard_congr (visibleFiberEquiv p θ q hgood))

end Paper35.Source.CrossingCount
