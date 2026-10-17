import Paper35.GaussianMarked
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Paper35.GaussianMarked

/-- The actual inverse Gaussian pair rotation, followed by the remaining candidates. -/
def rotatedCandidates {m : ℕ} (n : ℕ) (D : Source.Space m)
    (z : Source.Space m × (Fin n → Source.Space m)) : Fin (n+2) → Source.Space m :=
  Fin.cases ((Real.sqrt 2)⁻¹ • (z.1 + D))
    (Fin.cases ((Real.sqrt 2)⁻¹ • (z.1 - D)) (fun k => z.2 k))

/-- Inner-product candidate scores for the inverse pair rotation. -/
def rotatedScores {m : ℕ} (n : ℕ) (ψ : ℝ → Source.Space m) (D : Source.Space m)
    (z : Source.Space m × (Fin n → Source.Space m)) : Fin (n+2) → ℝ → ℝ :=
  Fin.cases (fun s => (Real.sqrt 2)⁻¹ * (inner ℝ z.1 (ψ s) + inner ℝ D (ψ s)))
    (Fin.cases (fun s => (Real.sqrt 2)⁻¹ * (inner ℝ z.1 (ψ s) - inner ℝ D (ψ s)))
      (fun k s => inner ℝ (z.2 k) (ψ s)))

/-- The scores are genuinely the inner products with reconstructed Gaussian candidates. -/
theorem rotatedScores_eq_inner {m : ℕ} (n : ℕ) (ψ : ℝ → Source.Space m)
    (D : Source.Space m) (z : Source.Space m × (Fin n → Source.Space m)) :
    rotatedScores n ψ D z = fun j s => inner ℝ (rotatedCandidates n D z j) (ψ s) := by
  funext j s
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [rotatedScores, rotatedCandidates, Fin.cases_zero,
      real_inner_smul_left, inner_add_left]
  · refine Fin.cases ?_ (fun k => ?_) k
    · simp only [rotatedScores, rotatedCandidates, Fin.cases_zero, Fin.cases_succ,
        real_inner_smul_left, inner_sub_left]
    · rfl

def firstPair (n : ℕ) : OrderedCandidatePair (n+2) :=
  ⟨(0, (0 : Fin (n+1)).succ), by simp⟩

/-- Gaussian pair equality and strict upper-envelope visibility are exactly the
unmarked hyperplane intersection and the independently sampled Gaussian mark. -/
theorem visiblePair_rotated_iff {m : ℕ} (n : ℕ) (ψ : ℝ → Source.Space m)
    (D : Source.Space m) (z : Source.Space m × (Fin n → Source.Space m)) (s : ℝ) :
    VisiblePair (rotatedScores n ψ D z) s (firstPair n) ↔
      inner ℝ D (ψ s) = 0 ∧ z ∈ vectorVisible n (ψ s) := by
  have ha : 0 < (Real.sqrt 2)⁻¹ := inv_pos.mpr (Real.sqrt_pos.2 (by norm_num))
  constructor
  · rintro ⟨heq, hbelow⟩
    have hD : inner ℝ D (ψ s) = 0 := by
      change (Real.sqrt 2)⁻¹ * (inner ℝ z.1 (ψ s) + inner ℝ D (ψ s)) =
        (Real.sqrt 2)⁻¹ * (inner ℝ z.1 (ψ s) - inner ℝ D (ψ s)) at heq
      nlinarith
    refine ⟨hD, ?_⟩
    intro k
    have hk0 : k.succ.succ ≠ (0 : Fin (n+2)) := Fin.succ_ne_zero _
    have hk1 : k.succ.succ ≠ (0 : Fin (n+1)).succ := by
      intro heq
      exact Fin.succ_ne_zero k (Fin.succ_inj.mp heq)
    have hk := hbelow k.succ.succ hk0 hk1
    simpa only [rotatedScores, firstPair, Fin.cases_succ, Fin.cases_zero, hD,
      add_zero] using hk
  · rintro ⟨hD, hmark⟩
    refine ⟨?_, ?_⟩
    · simp only [firstPair, rotatedScores, Fin.cases_zero, Fin.cases_succ, hD,
        add_zero, sub_zero]
    · change ∀ k : Fin (n+2), k ≠ 0 → k ≠ (0 : Fin (n+1)).succ → _
      intro k
      refine Fin.cases ?_ (fun j => ?_) k
      · intro hk
        exact (hk rfl).elim
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro _ hk
          exact (hk rfl).elim
        · intro _ _
          simpa only [rotatedScores, firstPair, Fin.cases_succ, Fin.cases_zero, hD, add_zero]
            using hmark j

/-- The two reconstructed scores differ by a positive constant times D·ψ. -/
theorem rotated_score_difference {m : ℕ} (n : ℕ) (ψ : ℝ → Source.Space m)
    (D : Source.Space m) (z : Source.Space m × (Fin n → Source.Space m)) :
    (fun s => rotatedScores n ψ D z 0 s -
      rotatedScores n ψ D z (0 : Fin (n+1)).succ s) =
        fun s => (2 * (Real.sqrt 2)⁻¹) * inner ℝ D (ψ s) := by
  funext s
  simp only [rotatedScores, Fin.cases_zero, Fin.cases_succ]
  ring

/-- An actual vector derivative gives the scalar pair derivative, with no Rice assumption. -/
theorem hasDerivAt_rotated_difference {m : ℕ} (n : ℕ) (ψ : ℝ → Source.Space m)
    (D : Source.Space m) (z : Source.Space m × (Fin n → Source.Space m))
    {s : ℝ} {u : Source.Space m} (hψ : HasDerivAt ψ u s) :
    HasDerivAt (fun t => rotatedScores n ψ D z 0 t -
      rotatedScores n ψ D z (0 : Fin (n+1)).succ t)
        ((2 * (Real.sqrt 2)⁻¹) * inner ℝ D u) s := by
  rw [rotated_score_difference]
  have hdot : HasDerivAt (fun t => inner ℝ D (ψ t)) (inner ℝ D u) s := by
    simpa only [inner_zero_left, add_zero] using (hasDerivAt_const s D).inner ℝ hψ
  exact hdot.const_mul _

/-- The own switch-counting step: if all pair equalities are regular, the genuine
pair-switch set is exactly the marked transverse-intersection set. -/
theorem pairSwitchSet_rotated_eq {m : ℕ} (n : ℕ) (ψ : ℝ → Source.Space m)
    (D : Source.Space m) (z : Source.Space m × (Fin n → Source.Space m)) (L : ℝ)
    (hregular : ∀ s ∈ Ioo 0 L, inner ℝ D (ψ s) = 0 →
      DifferentiableAt ℝ ψ s ∧ inner ℝ D (deriv ψ s) ≠ 0) :
    pairSwitchSet (rotatedScores n ψ D z) L (firstPair n) =
      transverseZeros ψ L D ∩ {s | z ∈ vectorVisible n (ψ s)} := by
  have ha : 2 * (Real.sqrt 2)⁻¹ ≠ 0 := mul_ne_zero (by norm_num)
    (inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num))))
  ext s
  constructor
  · rintro ⟨hs0, hsL, hvis, _⟩
    obtain ⟨hD, hmark⟩ := (visiblePair_rotated_iff n ψ D z s).mp hvis
    obtain ⟨hψ, htrans⟩ := hregular s ⟨hs0, hsL⟩ hD
    exact ⟨⟨hs0, hsL, hD, hψ, htrans⟩, hmark⟩
  · rintro ⟨⟨hs0, hsL, hD, hψ, htrans⟩, hmark⟩
    refine ⟨hs0, hsL, (visiblePair_rotated_iff n ψ D z s).mpr ⟨hD, hmark⟩, ?_⟩
    apply signChanges_of_hasDerivAt_ne_zero
      (hasDerivAt_rotated_difference n ψ D z hψ.hasDerivAt)
    · have heq := congrFun (rotated_score_difference n ψ D z) s
      simpa only [hD, mul_zero] using heq
    · exact mul_ne_zero ha htrans

/-- Explicit classical null-exception part of parameterized spherical Crofton.
The original AC/unit-sphere hypotheses are unchanged. Endpoints are excluded,
and nondifferentiable parameters, zero-speed images and tangencies have zero
Crofton measure (Santaló 1942 Eq. (37), p.716; 2004 Eq. (18.36), pp.323–324,
as recorded in paper Lemma 6.1). No visibility/switch conclusion is an input. -/
def ClassicalCroftonRegularityLaw : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (L : ℝ), 0 < L → ∀ (ψ : ℝ → Source.Space m),
    AbsolutelyContinuousOnInterval ψ 0 L → (∀ s ∈ Icc 0 L, ‖ψ s‖ = 1) →
      ∀ᵐ D ∂standardGaussian m, ∀ s ∈ Ioo 0 L, inner ℝ D (ψ s) = 0 →
        DifferentiableAt ℝ ψ s ∧ inner ℝ D (deriv ψ s) ≠ 0

/-- The derived marked Crofton law now counts the actual active-pair switches. -/
theorem first_pair_switch_crofton (hcrofton : ClassicalCroftonLaw)
    (hregular : ClassicalCroftonRegularityLaw) (hproj : GaussianUnitProjectionLaw)
    (m n : ℕ) (hm : 2 ≤ m) (L : ℝ) (hL : 0 < L)
    (ψ : ℝ → Source.Space m) (hac : AbsolutelyContinuousOnInterval ψ 0 L)
    (hunit : ∀ s ∈ Icc 0 L, ‖ψ s‖ = 1) :
    (∫⁻ D, ∫⁻ z, ((pairSwitchSet (rotatedScores n ψ D z) L (firstPair n)).encard : ℝ≥0∞)
      ∂vectorMarkLaw m n ∂standardGaussian m) =
      (ENNReal.ofReal (1 / Real.pi) * sphericalLength ψ L) * visibilityProbability n := by
  rw [← marked_pair_crofton hcrofton hproj m n hm L hL ψ hac hunit]
  apply lintegral_congr_ae
  filter_upwards [hregular m hm L hL ψ hac hunit] with D hD
  apply lintegral_congr
  intro z
  rw [pairSwitchSet_rotated_eq n ψ D z L hD]

end Paper35.GaussianMarked
