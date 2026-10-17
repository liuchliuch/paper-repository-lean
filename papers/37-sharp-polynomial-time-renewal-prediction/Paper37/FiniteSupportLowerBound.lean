import Paper37.SupportPrior

namespace Paper37.FiniteSupportLowerBound
open scoped BigOperators ENNReal
open Paper37.LowerBound Paper37.SupportPrior

noncomputable section

lemma support_length_cap {b : ℕ} (hb : 0 < b) (z : Sample b) {d : ℕ}
    (hd : d ∈ support z) : (d : ℝ) + 1 ≤ ((48 * b : ℕ) : ℝ) := by
  have hn : d + 1 ≤ 48 * b := by
    rcases Finset.mem_union.mp hd with hl | hh
    · have := lowSupport_bounds z hl
      omega
    · have := (highSupport_bounds hb z hh).2
      omega
  exact_mod_cast hn

lemma highSupport_subset_large_filter {b : ℕ} (hb : 0 < b) (z : Sample b) :
    highSupport z ⊆ (support z).filter (fun d : ℕ => ((24 * b : ℕ) : ℝ) ≤ (d : ℝ) + 1) := by
  intro d hd
  refine Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hd, ?_⟩
  have hn := (highSupport_bounds hb z hd).1
  exact_mod_cast (show 24 * b ≤ d + 1 by omega)

lemma law_mean_bounds {b : ℕ} (hb : 0 < b) (z : Sample b) :
    ((24 * b : ℕ) : ℝ) / 2 ≤ Paper37.Renewal.mean (law z) ∧
      Paper37.Renewal.mean (law z) ≤ ((48 * b : ℕ) : ℝ) := by
  have hcard : ((support z).card : ℝ) = ((24 * b : ℕ) : ℝ) := by rw [support_card hb z]
  have hlarge : ((24 * b : ℕ) : ℝ) / 2 ≤
      (((support z).filter (fun d : ℕ => ((24 * b : ℕ) : ℝ) ≤ (d : ℝ) + 1)).card : ℝ) := by
    have h := Finset.card_le_card (highSupport_subset_large_filter hb z)
    rw [highSupport_card hb z] at h
    have hR : ((12 * b : ℕ) : ℝ) ≤
        (((support z).filter (fun d : ℕ => ((24 * b : ℕ) : ℝ) ≤ (d : ℝ) + 1)).card : ℝ) :=
      by exact_mod_cast h
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hR ⊢
    linarith
  constructor
  · exact uniformSupportLaw_mean_ge_half (support z) (support_nonempty z) hcard hlarge
  · exact uniformSupportLaw_mean_le_support_cap (support z) (support_nonempty z)
      (fun d hd => support_length_cap hb z hd)

lemma boundaryCount_bounds {b t : ℕ} (hb : 0 < b) (ht : t < 24 * b) (z : Sample b) :
    ((24 * b : ℕ) : ℝ) / 2 ≤ boundaryCount z t ∧
      boundaryCount z t ≤ ((24 * b : ℕ) : ℝ) := by
  have hsubset : highSupport z ⊆ (support z).filter (fun d => t ≤ d) := by
    intro d hd
    refine Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hd, ?_⟩
    have := (highSupport_bounds hb z hd).1
    omega
  have hlo := Finset.card_le_card hsubset
  have hhi := Finset.card_filter_le (support z) (fun d => t ≤ d)
  rw [highSupport_card hb z] at hlo
  rw [support_card hb z] at hhi
  constructor
  · have hR : ((12 * b : ℕ) : ℝ) ≤ boundaryCount z t := by unfold boundaryCount; exact_mod_cast hlo
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hR ⊢
    linarith
  · unfold boundaryCount
    exact_mod_cast hhi

lemma boundaryWeight_range_low {b j : ℕ} (hb : 0 < b) (hj : j < 24 * b)
    (x : List Bool) (hg : Paper37.Renewal.ageFrom 0 x < 24 * b) (z : Sample b) :
    ((24 * b : ℕ) : ℝ) / 8 ≤ boundaryWeight j x z ∧
      boundaryWeight j x z ≤ 16 * (((24 * b : ℕ) : ℝ) / 8) := by
  have ha : (0 : ℝ) < ((24 * b : ℕ) : ℝ) := by exact_mod_cast (show 0 < 24 * b by omega)
  have hJ := boundaryCount_bounds hb hj z
  have hg' := boundaryCount_bounds hb hg z
  have hm := law_mean_bounds hb z
  have hmhi : Paper37.Renewal.mean (law z) ≤ 2 * ((24 * b : ℕ) : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hm ⊢
    linarith [hm.2]
  have h := two_boundary_weight_range ha hJ.1 hJ.2 hg'.1 hg'.2 hm.1 hmhi
  change _ ≤ boundaryWeight j x z ∧ boundaryWeight j x z ≤ _ at h
  constructor
  · exact h.1
  · nlinarith [h.2]

lemma seen_low_card_le_gap_count (b : ℕ) (x : List Bool) :
    (lowSeen b (Paper37.Renewal.gapsFrom 0 x).toFinset).card ≤
      (Paper37.Renewal.gapsFrom 0 x).length := by
  exact le_trans (Finset.card_filter_le _ _) (List.toFinset_card_le _)

lemma posterior_eventMass_eq_reweighted_seen {b : ℕ} (hb : 0 < b) (j : ℕ) (x : List Bool)
    (hZ : 0 < (prior b).expectation (observationLikelihood j x))
    (M : Sample b → Prop) [DecidablePred M] :
    (posterior j x hZ).eventMass M =
      ((seenPrior (Paper37.Renewal.gapsFrom 0 x).toFinset
        (compatible_probability_pos hb j x hZ)).reweight (boundaryWeight j x)
          (boundaryWeight_nonneg j x) (conditioned_boundaryWeight_pos hb j x hZ)).eventMass M := by
  unfold FiniteLaw.eventMass
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : M z
  · simp only [if_pos hz]
    exact posterior_conditioned_reweight_mass hb j x hZ z
  · simp [hz]

/-- Actual F.5 in the source branch J ≤ a. Every assumption is an observable
source good-event condition or positive prior-predictive block probability. -/
lemma posterior_stability_left_low {b j : ℕ} (hb : 0 < b) (hj : j < 24 * b)
    (x : List Bool) (hZ : 0 < (prior b).expectation (observationLikelihood j x))
    (hg : Paper37.Renewal.ageFrom 0 x < 24 * b)
    (hunseen : Paper37.Renewal.ageFrom 0 x ∉ (Paper37.Renewal.gapsFrom 0 x).toFinset)
    (hr : (Paper37.Renewal.gapsFrom 0 x).length ≤ b) :
    11 / 203 ≤ (posterior j x hZ).eventMass
      (fun z => Paper37.Renewal.ageFrom 0 x ∈ support z) ∧
    11 / 203 ≤ (posterior j x hZ).eventMass
      (fun z => Paper37.Renewal.ageFrom 0 x ∉ support z) := by
  let A := (Paper37.Renewal.gapsFrom 0 x).toFinset
  let hA := compatible_probability_pos hb j x hZ
  let P := seenPrior A hA
  let M := fun z : Sample b => Paper37.Renewal.ageFrom 0 x ∈ support z
  have hsmall : (lowSeen b A).card ≤ b := le_trans (seen_low_card_le_gap_count b x) hr
  have hp := seenPrior_membership_interval hb A hA _ hg hunseen hsmall
  have hm : (0 : ℝ) < ((24 * b : ℕ) : ℝ) / 8 := by positivity
  have hw := fun z : Sample b => boundaryWeight_range_low hb hj x hg z
  have hstable := P.reweighted_membership_stable M (boundaryWeight j x) hm hw
    (conditioned_boundaryWeight_pos hb j x hZ) hp.1 hp.2
  rw [posterior_eventMass_eq_reweighted_seen hb j x hZ,
    posterior_eventMass_eq_reweighted_seen hb j x hZ]
  exact hstable

def lengthSum (S : Finset ℕ) : ℝ := ∑ d ∈ S, ((d : ℝ) + 1)

lemma law_mean_split {b : ℕ} (hb : 0 < b) (z : Sample b) :
    Paper37.Renewal.mean (law z) =
      (lengthSum (lowSupport z) + lengthSum (highSupport z)) / ((24 * b : ℕ) : ℝ) := by
  change Paper37.Renewal.mean (uniformSupportLaw (support z) _) = _
  rw [uniformSupportLaw_mean, support_card hb z]
  congr 1
  exact Finset.sum_union (low_high_disjoint hb z)

lemma low_lengthSum_upper {b : ℕ} (z : Sample b) :
    lengthSum (lowSupport z) ≤ ((12 * b : ℕ) : ℝ) * ((24 * b : ℕ) : ℝ) := by
  calc
    _ ≤ ∑ _d ∈ lowSupport z, ((24 * b : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hn : d + 1 ≤ 24 * b := by have := lowSupport_bounds z hd; omega
      exact_mod_cast hn
    _ = _ := by simp [(lowSupport_spec z).2]

lemma high_lengthSum_lower {b : ℕ} (hb : 0 < b) (z : Sample b) :
    ((12 * b : ℕ) : ℝ) * ((24 * b : ℕ) : ℝ) ≤ lengthSum (highSupport z) := by
  calc
    _ = ∑ _d ∈ highSupport z, ((24 * b : ℕ) : ℝ) := by simp [highSupport_card hb z]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d hd
      have hn : 24 * b ≤ d + 1 := by have := (highSupport_bounds hb z hd).1; omega
      exact_mod_cast hn

lemma lengthSum_nonneg (S : Finset ℕ) : 0 ≤ lengthSum S := by
  exact Finset.sum_nonneg (fun _ _ => by positivity)

/-- Source mean comparison after fixing the high support, with no posterior
or observed-data premise. -/
lemma mean_fixed_high_ratio {b : ℕ} (hb : 0 < b)
    (L₁ L₂ : lowChoices b) (H : highFreeChoices b) :
    Paper37.Renewal.mean (law (L₂, H)) ≤ 2 * Paper37.Renewal.mean (law (L₁, H)) := by
  have hlow := low_lengthSum_upper (L₂, H)
  have hhigh := high_lengthSum_lower hb (L₁, H)
  have hnonneg := lengthSum_nonneg (lowSupport (L₁, H))
  have heq : highSupport (L₂, H) = highSupport (L₁, H) := rfl
  rw [law_mean_split hb, law_mean_split hb, heq]
  have hnum : lengthSum (lowSupport (L₂, H)) + lengthSum (highSupport (L₁, H)) ≤
      2 * (lengthSum (lowSupport (L₁, H)) + lengthSum (highSupport (L₁, H))) := by linarith
  calc
    _ ≤ (2 * (lengthSum (lowSupport (L₁, H)) + lengthSum (highSupport (L₁, H)))) /
        ((24 * b : ℕ) : ℝ) := div_le_div_of_nonneg_right hnum (by positivity)
    _ = _ := by ring

lemma boundaryCount_eq_high {b j : ℕ} (hb : 0 < b) (hj : 24 * b ≤ j) (z : Sample b) :
    boundaryCount z j = (((highSupport z).filter (fun d => j ≤ d)).card : ℝ) := by
  have heq : (support z).filter (fun d => j ≤ d) = (highSupport z).filter (fun d => j ≤ d) := by
    ext d
    simp only [Finset.mem_filter, support, Finset.mem_union]
    constructor
    · rintro ⟨hd | hd, hjd⟩
      · have := lowSupport_bounds z hd
        omega
      · exact ⟨hd, hjd⟩
    · rintro ⟨hd, hjd⟩
      exact ⟨Or.inr hd, hjd⟩
  exact congrArg (fun S : Finset ℕ => (S.card : ℝ)) heq

lemma boundaryCount_nonneg {b : ℕ} (z : Sample b) (j : ℕ) : 0 ≤ boundaryCount z j := by
  exact Nat.cast_nonneg _

/-- The left-censoring factor is shared after fixing H; the factor-four
comparison is for actual source weights, including zero left-tail factors. -/
lemma boundaryWeight_fixed_high_comparison {b j : ℕ} (hb : 0 < b) (hj : 24 * b ≤ j)
    (x : List Bool) (hg : Paper37.Renewal.ageFrom 0 x < 24 * b)
    (L₁ L₂ : lowChoices b) (H : highFreeChoices b) :
    boundaryWeight j x (L₁, H) ≤ 4 * boundaryWeight j x (L₂, H) := by
  have hJ : boundaryCount (L₁, H) j = boundaryCount (L₂, H) j := by
    rw [boundaryCount_eq_high hb hj, boundaryCount_eq_high hb hj]
    rfl
  have hU₁ := boundaryCount_bounds hb hg (L₁, H)
  have hU₂ := boundaryCount_bounds hb hg (L₂, H)
  have hU : boundaryCount (L₁, H) (Paper37.Renewal.ageFrom 0 x) ≤
      2 * boundaryCount (L₂, H) (Paper37.Renewal.ageFrom 0 x) := by linarith
  unfold boundaryWeight
  rw [← hJ]
  exact fixed_high_weight_comparison (boundaryCount_nonneg _ _)
    (boundaryCount_nonneg _ _) (Paper37.Renewal.mean_pos _) (Paper37.Renewal.mean_pos _)
    hU (mean_fixed_high_ratio hb L₁ L₂ H)

lemma seenPrior_expectation_product {b : ℕ} (hb : 0 < b) (A : Finset ℕ)
    (hA : 0 < (prior b).eventMass (fun z => A ⊆ support z)) (f : Sample b → ℝ) :
    (seenPrior A hA).expectation f = (seenLowPrior hb A hA).expectation
      (fun L => (seenHighPrior hb A hA).expectation (fun H => f (L, H))) := by
  calc
    _ = (product (seenLowPrior hb A hA) (seenHighPrior hb A hA)).expectation
        (fun z => f z) := by
      unfold FiniteLaw.expectation
      apply Finset.sum_congr rfl
      intro z _
      rw [seenPrior_mass_factor hb A hA]
      rfl
    _ = _ := by
      simpa only [Prod.mk.eta] using product_expectation (seenLowPrior hb A hA)
        (seenHighPrior hb A hA) (fun L H => f (L, H))

def marginalBoundaryWeight {b : ℕ} (hb : 0 < b) (A : Finset ℕ)
    (hA : 0 < (prior b).eventMass (fun z => A ⊆ support z))
    (j : ℕ) (x : List Bool) (L : lowChoices b) : ℝ :=
  (seenHighPrior hb A hA).expectation (fun H => boundaryWeight j x (L, H))

lemma marginalBoundaryWeight_nonneg {b : ℕ} (hb : 0 < b) (A : Finset ℕ)
    (hA : 0 < (prior b).eventMass (fun z => A ⊆ support z))
    (j : ℕ) (x : List Bool) (L : lowChoices b) :
    0 ≤ marginalBoundaryWeight hb A hA j x L :=
  (seenHighPrior hb A hA).expectation_nonneg (fun H => boundaryWeight_nonneg j x (L, H))

lemma marginal_weight_normalizer_pos {b : ℕ} (hb : 0 < b) (j : ℕ) (x : List Bool)
    (hZ : 0 < (prior b).expectation (observationLikelihood j x)) :
    0 < (seenLowPrior hb (Paper37.Renewal.gapsFrom 0 x).toFinset
      (compatible_probability_pos hb j x hZ)).expectation
        (marginalBoundaryWeight hb (Paper37.Renewal.gapsFrom 0 x).toFinset
          (compatible_probability_pos hb j x hZ) j x) := by
  unfold marginalBoundaryWeight
  rw [← seenPrior_expectation_product hb _ _ (boundaryWeight j x)]
  exact conditioned_boundaryWeight_pos hb j x hZ

/-- Exact Bayes marginalization over H; every left-boundary factor remains in
the marginalized likelihood. -/
lemma posterior_low_eventMass {b : ℕ} (hb : 0 < b) (j : ℕ) (x : List Bool)
    (hZ : 0 < (prior b).expectation (observationLikelihood j x))
    (M : (lowChoices b) → Prop) [DecidablePred M] :
    (posterior j x hZ).eventMass (fun z => M z.1) =
      ((seenLowPrior hb (Paper37.Renewal.gapsFrom 0 x).toFinset
        (compatible_probability_pos hb j x hZ)).reweight
          (marginalBoundaryWeight hb (Paper37.Renewal.gapsFrom 0 x).toFinset
            (compatible_probability_pos hb j x hZ) j x)
          (marginalBoundaryWeight_nonneg hb _ _ j x)
          (marginal_weight_normalizer_pos hb j x hZ)).eventMass M := by
  rw [posterior_eventMass_eq_reweighted_seen hb j x hZ,
    FiniteLaw.reweight_eventMass, FiniteLaw.reweight_eventMass,
    seenPrior_expectation_product hb _ _ (boundaryWeight j x),
    seenPrior_expectation_product hb _ _ (fun z => if M z.1 then boundaryWeight j x z else 0)]
  congr 1
  unfold FiniteLaw.expectation
  apply Finset.sum_congr rfl
  intro L _
  by_cases hM : M L
  · simp [hM, marginalBoundaryWeight, FiniteLaw.expectation]
  · simp [hM, marginalBoundaryWeight, FiniteLaw.expectation]

lemma marginal_weight_comparison {b j : ℕ} (hb : 0 < b) (hj : 24 * b ≤ j)
    (A : Finset ℕ) (hA : 0 < (prior b).eventMass (fun z => A ⊆ support z))
    (x : List Bool) (hg : Paper37.Renewal.ageFrom 0 x < 24 * b)
    (L₁ L₂ : lowChoices b) :
    marginalBoundaryWeight hb A hA j x L₁ ≤ 4 * marginalBoundaryWeight hb A hA j x L₂ := by
  exact marginalized_weight_comparison (seenHighPrior hb A hA)
    (fun H => boundaryWeight j x (L₁, H)) (fun H => boundaryWeight j x (L₂, H))
    (boundaryWeight_fixed_high_comparison hb hj x hg L₁ L₂)

lemma marginal_weight_pos {b j : ℕ} (hb : 0 < b) (hj : 24 * b ≤ j)
    (x : List Bool) (hZ : 0 < (prior b).expectation (observationLikelihood j x))
    (hg : Paper37.Renewal.ageFrom 0 x < 24 * b) (L : lowChoices b) :
    0 < marginalBoundaryWeight hb (Paper37.Renewal.gapsFrom 0 x).toFinset
      (compatible_probability_pos hb j x hZ) j x L := by
  let A := (Paper37.Renewal.gapsFrom 0 x).toFinset
  let hA := compatible_probability_pos hb j x hZ
  let P := seenLowPrior hb A hA
  let w := marginalBoundaryWeight hb A hA j x
  have hcomp : ∀ K, w K ≤ 4 * w L := fun K => marginal_weight_comparison hb hj A hA x hg K L
  have hbound : P.expectation w ≤ 4 * w L := by
    calc
      _ ≤ ∑ K, P.mass K * (4 * w L) :=
        Finset.sum_le_sum (fun K _ => mul_le_mul_of_nonneg_left (hcomp K) (P.nonneg K))
      _ = 4 * w L := by rw [← Finset.sum_mul, P.total, one_mul]
  have hpositive := marginal_weight_normalizer_pos hb j x hZ
  change 0 < P.expectation w at hpositive
  change 0 < w L
  linarith

/-- Actual F.5 for J > a. Conditioning on H and then taking the exact
posterior marginal preserves the source's two stationary boundaries. -/
lemma posterior_stability_left_high {b j : ℕ} (hb : 0 < b) (hj : 24 * b ≤ j)
    (x : List Bool) (hZ : 0 < (prior b).expectation (observationLikelihood j x))
    (hg : Paper37.Renewal.ageFrom 0 x < 24 * b)
    (hunseen : Paper37.Renewal.ageFrom 0 x ∉ (Paper37.Renewal.gapsFrom 0 x).toFinset)
    (hr : (Paper37.Renewal.gapsFrom 0 x).length ≤ b) :
    11 / 203 ≤ (posterior j x hZ).eventMass
      (fun z => Paper37.Renewal.ageFrom 0 x ∈ support z) ∧
    11 / 203 ≤ (posterior j x hZ).eventMass
      (fun z => Paper37.Renewal.ageFrom 0 x ∉ support z) := by
  let A := (Paper37.Renewal.gapsFrom 0 x).toFinset
  let hA := compatible_probability_pos hb j x hZ
  let P := seenLowPrior hb A hA
  let w := marginalBoundaryWeight hb A hA j x
  let M := fun L : lowChoices b => Paper37.Renewal.ageFrom 0 x ∈ L.val
  letI : Nonempty (↥(lowChoices b)) :=
    ⟨⟨(lowChoices_nonempty b).choose, (lowChoices_nonempty b).choose_spec⟩⟩
  have hsmall : (lowSeen b A).card ≤ b := le_trans (seen_low_card_le_gap_count b x) hr
  have hstrict : (lowSeen b A).card < 12 * b := by omega
  have hp := seenPrior_membership_interval hb A hA _ hg hunseen hsmall
  have hEq : (seenPrior A hA).eventMass (fun z => Paper37.Renewal.ageFrom 0 x ∈ support z) =
      P.eventMass M := (seenPrior_membership hb A hA _ hg hunseen hstrict).trans
        (seenLowPrior_membership hb A hA _ hg hunseen hstrict).symm
  rw [hEq] at hp
  have hpos : ∀ L, 0 < w L := fun L => marginal_weight_pos hb hj x hZ hg L
  have hcomp : ∀ L K, w L ≤ 16 * w K := by
    intro L K
    have h4 := marginal_weight_comparison hb hj A hA x hg L K
    change w L ≤ 4 * w K at h4
    linarith [hpos K]
  have hstable := P.reweighted_membership_stable_of_pairwise M w hpos hcomp
    (marginal_weight_normalizer_pos hb j x hZ) hp.1 hp.2
  have hmember : ∀ z : Sample b, Paper37.Renewal.ageFrom 0 x ∈ support z ↔ M z.1 := by
    intro z
    constructor
    · intro hz
      rcases Finset.mem_union.mp hz with hl | hh
      · exact hl
      · have := (highSupport_bounds hb z hh).1
        omega
    · exact Finset.mem_union_left _
  rw [eventMass_congr (posterior j x hZ) _ _ hmember,
    eventMass_congr (posterior j x hZ) _ _ (fun z => (hmember z).not),
    posterior_low_eventMass hb j x hZ M,
    posterior_low_eventMass hb j x hZ (fun L => ¬ M L)]
  exact hstable

/-- Source F.5 for the actual F.2 Bayes posterior, in both left-boundary cases. -/
lemma posterior_stability {b : ℕ} (hb : 0 < b) (j : ℕ)
    (x : List Bool) (hZ : 0 < (prior b).expectation (observationLikelihood j x))
    (hg : Paper37.Renewal.ageFrom 0 x < 24 * b)
    (hunseen : Paper37.Renewal.ageFrom 0 x ∉ (Paper37.Renewal.gapsFrom 0 x).toFinset)
    (hr : (Paper37.Renewal.gapsFrom 0 x).length ≤ b) :
    11 / 203 ≤ (posterior j x hZ).eventMass
      (fun z => Paper37.Renewal.ageFrom 0 x ∈ support z) ∧
    11 / 203 ≤ (posterior j x hZ).eventMass
      (fun z => Paper37.Renewal.ageFrom 0 x ∉ support z) := by
  by_cases hj : j < 24 * b
  · exact posterior_stability_left_low hb hj x hZ hg hunseen hr
  · exact posterior_stability_left_high hb (by omega) x hZ hg hunseen hr

lemma ageFrom_zero_prefix_true (a j : ℕ) (x : List Bool) :
    Paper37.Renewal.ageFrom a (List.replicate j false ++ true :: x) =
      Paper37.Renewal.ageFrom 0 x := by
  induction j generalizing a with
  | zero => simp [Paper37.Renewal.ageFrom]
  | succ j ih => simpa [List.replicate_succ, Paper37.Renewal.ageFrom] using ih (a + 1)

/-- F.12 for every actual positive-likelihood support model. -/
lemma actual_conditional_hazard {b : ℕ} (hb : 0 < b) (j : ℕ) (x : List Bool)
    (hg : Paper37.Renewal.ageFrom 0 x < 24 * b) (z : Sample b)
    (hp : 0 < observationLikelihood j x z) :
    Paper37.Renewal.conditional (law z) (List.replicate j false ++ true :: x) =
      if Paper37.Renewal.ageFrom 0 x ∈ support z then
        1 / boundaryCount z (Paper37.Renewal.ageFrom 0 x) else 0 := by
  rw [Paper37.Renewal.conditional_visible_renewal (law z) _ (by simp) hp,
    ageFrom_zero_prefix_true]
  change (uniformSupportLaw (support z) _).mass (Paper37.Renewal.ageFrom 0 x) /
      Paper37.Renewal.tail (uniformSupportLaw (support z) _) (Paper37.Renewal.ageFrom 0 x) = _
  rw [uniformSupportLaw_mass, uniformSupportLaw_tail]
  have ha : (0 : ℝ) < ((support z).card : ℝ) := by exact_mod_cast (support_nonempty z).card_pos
  have hU : 0 < boundaryCount z (Paper37.Renewal.ageFrom 0 x) := by
    have h := (boundaryCount_bounds hb hg z).1
    have ha' : (0 : ℝ) < ((24 * b : ℕ) : ℝ) / 2 := by positivity
    exact lt_of_lt_of_le ha' h
  change (if Paper37.Renewal.ageFrom 0 x ∈ support z then 1 / ((support z).card : ℝ) else 0) /
      (boundaryCount z (Paper37.Renewal.ageFrom 0 x) / ((support z).card : ℝ)) = _
  by_cases hm : Paper37.Renewal.ageFrom 0 x ∈ support z
  · simp only [if_pos hm]
    field_simp
  · simp [hm]

lemma posterior_positive_likelihood {b : ℕ} (j : ℕ) (x : List Bool)
    (hZ : 0 < (prior b).expectation (observationLikelihood j x)) (z : Sample b)
    (hz : (posterior j x hZ).mass z ≠ 0) : 0 < observationLikelihood j x z := by
  have hnonneg := Paper37.Renewal.blockMass_nonneg (law z)
    (List.replicate j false ++ true :: x)
  by_contra hnot
  have heq : observationLikelihood j x z = 0 := le_antisymm (not_lt.mp hnot) hnonneg
  apply hz
  change (prior b).mass z * observationLikelihood j x z /
    (prior b).expectation (observationLikelihood j x) = 0
  rw [heq]
  simp

lemma expectedKL_congr_on_mass {α : Type*} [Fintype α] (P : FiniteLaw α)
    (θ θ' : α → ℝ) (q : ℝ) (h : ∀ x, P.mass x ≠ 0 → θ x = θ' x) :
    P.expectedKL θ q = P.expectedKL θ' q := by
  unfold FiniteLaw.expectedKL
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P.mass x = 0
  · simp [hx]
  · rw [h x hx]

/-- Full F.6 for the actual observational posterior and actual next-step
conditionals, including q=0, q=1 and their infinite losses. -/
lemma actual_posterior_radius {b : ℕ} (hb : 0 < b) (j : ℕ)
    (x : List Bool) (hZ : 0 < (prior b).expectation (observationLikelihood j x))
    (hg : Paper37.Renewal.ageFrom 0 x < 24 * b)
    (hunseen : Paper37.Renewal.ageFrom 0 x ∉ (Paper37.Renewal.gapsFrom 0 x).toFinset)
    (hr : (Paper37.Renewal.gapsFrom 0 x).length ≤ b)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ENNReal.ofReal ((11 / 203) * (Real.log 2 - 1 / 2) / ((24 * b : ℕ) : ℝ)) ≤
      (posterior j x hZ).expectedKL
        (fun z => Paper37.Renewal.conditional (law z) (List.replicate j false ++ true :: x)) q := by
  have hstable := posterior_stability hb j x hZ hg hunseen hr
  rw [expectedKL_congr_on_mass (posterior j x hZ) _
    (fun z => if Paper37.Renewal.ageFrom 0 x ∈ support z then
      1 / boundaryCount z (Paper37.Renewal.ageFrom 0 x) else 0) q
    (fun z hz => actual_conditional_hazard hb j x hg z (posterior_positive_likelihood j x hZ z hz))]
  exact finite_hazard_posterior_radius (posterior j x hZ)
    (fun z => Paper37.Renewal.ageFrom 0 x ∈ support z)
    (fun z => boundaryCount z (Paper37.Renewal.ageFrom 0 x))
    (by exact_mod_cast (show 2 ≤ 24 * b by omega)) (fun z => boundaryCount_bounds hb hg z)
    hstable.1 hstable.2 hq hq1

lemma actual_randomized_posterior_radius {Ω : Type*} [MeasurableSpace Ω]
    (ρ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure ρ]
    {b : ℕ} (hb : 0 < b) (j : ℕ)
    (x : List Bool) (hZ : 0 < (prior b).expectation (observationLikelihood j x))
    (hg : Paper37.Renewal.ageFrom 0 x < 24 * b)
    (hunseen : Paper37.Renewal.ageFrom 0 x ∉ (Paper37.Renewal.gapsFrom 0 x).toFinset)
    (hr : (Paper37.Renewal.gapsFrom 0 x).length ≤ b)
    (q : Ω → ℝ) (hq : ∀ ω, 0 ≤ q ω ∧ q ω ≤ 1) :
    ENNReal.ofReal ((11 / 203) * (Real.log 2 - 1 / 2) / ((24 * b : ℕ) : ℝ)) ≤
      ∫⁻ ω, (posterior j x hZ).expectedKL
        (fun z => Paper37.Renewal.conditional (law z) (List.replicate j false ++ true :: x)) (q ω) ∂ρ := by
  calc
    _ = ∫⁻ _ : Ω, ENNReal.ofReal
        ((11 / 203) * (Real.log 2 - 1 / 2) / ((24 * b : ℕ) : ℝ)) ∂ρ := by simp
    _ ≤ _ := MeasureTheory.lintegral_mono (fun ω =>
      actual_posterior_radius hb j x hZ hg hunseen hr (hq ω).1 (hq ω).2)

end
end Paper37.FiniteSupportLowerBound
