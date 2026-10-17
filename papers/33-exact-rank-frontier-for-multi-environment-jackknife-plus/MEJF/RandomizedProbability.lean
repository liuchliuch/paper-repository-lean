import MEJF.TournamentOptimization
import MEJF.MainExact
import MEJF.FiniteExchangeable

/-! Exact hidden-global-rank statistical minimax law, with a single learner
outside the independent finite rank expectation. -/
namespace MEJF.RandomizedProbability
open MeasureTheory Finset Setup Exchangeability TournamentOptimization
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A genuine distribution on the positive finite outer ranks. -/
structure RankLaw (m : ℕ) where
  mass : Fin m → ℝ
  nonneg : ∀ l, 0 ≤ mass l
  sum_one : ∑ l, mass l = 1

def rankValid {m : ℕ} (l : Fin m) : 1 ≤ l.val+1 ∧ l.val+1 ≤ m := by omega

/-- Finite expectation over a hidden independent global rank. `A` has no rank
input and is fixed before this sum, as required in (6.19). -/
def weightedProbability {X : Type*} [MeasurableSpace X] {m n : ℕ}
    (pi : Fin m → ℝ) (A : Learner X n)
    (μ : Measure (Fin (m+1) → Block X n)) (F t : ℕ) (ht : 1 ≤ t ∧ t ≤ n)
    (i : Fin (m+1)) : ℝ :=
  ∑ l, pi l * μ.real {Z | Setup.failure A Z i F t (l.val+1) ht (rankValid l)}

/-- The statistical supremum retains one learner and one exchangeable data law
outside the hidden-rank expectation. It is independent of the tournament formula. -/
def gammaF (m n F t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (pi : RankLaw m) : ℝ :=
  sSup {r : ℝ | ∃ (A : Learner UniversalCovariate n)
    (μ : Measure (Fin (m+1) → Block UniversalCovariate n)),
    IsProbabilityMeasure μ ∧ Exchangeable μ ∧
    r = weightedProbability pi.mass A μ F t ht (Fin.last m)}

/-- The original alpha-parametrized randomized-rank minimax problem. -/
def finiteRankGammaPi (m n : ℕ) (alpha : ℝ) (t : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (pi : RankLaw m) : ℝ :=
  gammaF m n (failureRank alpha n) t ht pi

lemma weighted_card_sum {m : ℕ} (pi : Fin m → ℝ)
    (H : Fin m → Fin (m+1) → Prop) :
    (∑ l, pi l * ((univ.filter (H l)).card : ℝ)) =
      ∑ u : Fin (m+1), ∑ l : Fin m, if H l u then pi l else 0 := by
  rw [sum_comm]
  apply sum_congr rfl
  intro l _
  rw [← sum_filter]
  simp [mul_comm]

theorem pointwise_weighted_count_le {X : Type*} [MeasurableSpace X] {m n F t : ℕ}
    (A : Learner X n) (Z : Fin (m+1) → Block X n) (ht : 1 ≤ t ∧ t ≤ n)
    (htF : t ≤ F) (pi : Fin m → ℝ) (hpi : ∀ l, 0 ≤ pi l) :
    (∑ u : Fin (m+1), ∑ l : Fin m,
      if Setup.failure A Z u F t (l.val+1) ht (rankValid l) then pi l else 0) ≤
      maxObjective F m t pi := by
  let R : Fin (m+1) → Fin (m+1) → Prop :=
    fun u v => Setup.radius A Z v u t ht < Setup.radius A Z u v t ht
  have hasym : ∀ u v, R u v → ¬ R v u := by
    intro u v huv hvu
    exact (not_lt_of_gt huv) hvu
  apply le_trans ?_ (oriented_payoff_le_max F m t pi hpi R hasym)
  apply RandomizedRanks.weighted_bound_of_failure_forces _ _ pi hpi
  intro l u hf
  exact DeterministicUpper.learner_failure_forces_high_outdegree A Z u F t (l.val+1)
    ht (rankValid l) htF hf

/-- Weighted label averaging for the actual exchangeable law. -/
lemma weighted_average {X : Type*} [MeasurableSpace X] {m n : ℕ}
    (A : Learner X n) (μ : Measure (Fin (m+1) → Block X n)) [IsProbabilityMeasure μ]
    (hμ : Exchangeable μ) (F t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (pi : Fin m → ℝ)
    (i : Fin (m+1)) :
    (∫ Z, (∑ u : Fin (m+1), ∑ l : Fin m,
      if Setup.failure A Z u F t (l.val+1) ht (rankValid l) then pi l else 0) ∂μ) =
      (m+1 : ℕ) * weightedProbability pi A μ F t ht i := by
  let f : Fin (m+1) → Fin m → (Fin (m+1) → Block X n) → ℝ := fun u l =>
    Set.indicator {Z | Setup.failure A Z u F t (l.val+1) ht (rankValid l)} (fun _ => pi l)
  have hf : ∀ u l, Integrable (f u l) μ := by
    intro u l
    exact (integrable_const _).indicator (Setup.measurableSet_failure A u F t (l.val+1) ht (rankValid l))
  have heq : (fun Z => ∑ u : Fin (m+1), ∑ l : Fin m,
      if Setup.failure A Z u F t (l.val+1) ht (rankValid l) then pi l else 0) =
      fun Z => ∑ u : Fin (m+1), ∑ l : Fin m, f u l Z := by
    funext Z
    simp [f, Set.indicator_apply]
  rw [heq, integral_finset_sum _ (fun u _ => integrable_finset_sum _ (fun l _ => hf u l))]
  have hint : ∀ u, (∫ Z, ∑ l : Fin m, f u l Z ∂μ) = weightedProbability pi A μ F t ht i := by
    intro u
    rw [integral_finset_sum _ (fun l _ => hf u l)]
    apply sum_congr rfl
    intro l _
    rw [show (∫ Z, f u l Z ∂μ) =
      μ.real {Z | Setup.failure A Z u F t (l.val+1) ht (rankValid l)} * pi l from by
        exact integral_indicator_const _ (Setup.measurableSet_failure A u F t (l.val+1) ht (rankValid l))]
    rw [event_probability_eq μ hμ
      (fun Z u => Setup.failure A Z u F t (l.val+1) ht (rankValid l))
      (fun u => Setup.measurableSet_failure A u F t (l.val+1) ht (rankValid l))
      (SetupEquivariance.failure_equivariant A F t (l.val+1) ht (rankValid l)) u i]
    exact mul_comm _ _
  simp only [hint, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem weighted_probability_le {X : Type*} [MeasurableSpace X] {m n F t : ℕ}
    (A : Learner X n) (μ : Measure (Fin (m+1) → Block X n)) [IsProbabilityMeasure μ]
    (hμ : Exchangeable μ) (ht : 1 ≤ t ∧ t ≤ n) (htF : t ≤ F)
    (pi : Fin m → ℝ) (hpi : ∀ l, 0 ≤ pi l) (i : Fin (m+1)) :
    weightedProbability pi A μ F t ht i ≤ maxObjective F m t pi / (m+1 : ℕ) := by
  let f := fun Z => ∑ u : Fin (m+1), ∑ l : Fin m,
    if Setup.failure A Z u F t (l.val+1) ht (rankValid l) then pi l else 0
  have hf : Integrable f μ := by
    apply integrable_finset_sum
    intro u _
    apply integrable_finset_sum
    intro l _
    exact (integrable_const _).indicator (Setup.measurableSet_failure A u F t (l.val+1) ht (rankValid l))
  have hi : (∫ Z, f Z ∂μ) ≤ maxObjective F m t pi := by
    calc
      _ ≤ ∫ _ : (Fin (m+1) → Block X n), maxObjective F m t pi ∂μ :=
        integral_mono hf (integrable_const _) (fun Z => pointwise_weighted_count_le A Z ht htF pi hpi)
      _ = _ := by simp
  rw [weighted_average A μ hμ F t ht pi i] at hi
  apply (le_div_iff₀ (by positivity : (0:ℝ) < (m+1 : ℕ))).mpr
  simpa [mul_comm] using hi

/-- The independent finite rank expectation on any actual permutation orbit
is the weighted base-array label count divided by the number of labels. -/
theorem orbit_weighted_probability {X : Type*} [MeasurableSpace X] {m n : ℕ}
    (A : Learner X n) (Z : Fin (m+1) → Block X n) (F t : ℕ)
    (ht : 1 ≤ t ∧ t ≤ n) (pi : Fin m → ℝ) :
    weightedProbability pi A (FiniteExchangeable.blockPermutationLaw Z) F t ht (Fin.last m) =
      (∑ u : Fin (m+1),∑ l : Fin m,
        if Setup.failure A Z u F t (l.val+1) ht (rankValid l) then pi l else 0)/(m+1 : ℕ) := by
  have hp (l : Fin m) := FiniteExchangeable.blockPermutationLaw_equivariant_probability Z
    (fun W u => Setup.failure A W u F t (l.val+1) ht (rankValid l))
    (fun u => Setup.measurableSet_failure A u F t (l.val+1) ht (rankValid l))
    (SetupEquivariance.failure_equivariant A F t (l.val+1) ht (rankValid l)) (Fin.last m)
  unfold weightedProbability
  simp_rw [hp,Fintype.card_fin,←mul_div_assoc]
  rw [←sum_div,weighted_card_sum]

/-- A common actual learner and the finite permutation law attain the tournament
objective, before drawing the hidden global rank. -/
theorem exists_attaining_model (m n F t : ℕ) (hF : 1 ≤ F) (hFn : F ≤ n)
    (ht : 1 ≤ t ∧ t ≤ F) (pi : RankLaw m) :
    ∃ (A : Learner UniversalCovariate n) (Z : Fin (m+1) → Block UniversalCovariate n),
      weightedProbability pi.mass A (FiniteExchangeable.blockPermutationLaw Z) F t
        ⟨ht.1, ht.2.trans hFn⟩ (Fin.last m) = maxObjective F m t pi.mass / (m+1 : ℕ) := by
  obtain ⟨T, hT⟩ := maxObjective_attained F m t pi.mass
  obtain ⟨A, Z, hpay⟩ := RandomizedRanks.exists_joint_payoff_model (relation T)
    (relation_asymm T) hF hFn ht (PredictionTable.unitEmbedding (m+1) n)
    (PredictionTable.unitEmbedding (m+1) n).injective
  refine ⟨A, Z, ?_⟩
  have hp (l : Fin m) := FiniteExchangeable.blockPermutationLaw_equivariant_probability Z
    (fun W u => Setup.failure A W u F t (l.val+1) ⟨ht.1, ht.2.trans hFn⟩ (rankValid l))
    (fun u => Setup.measurableSet_failure A u F t (l.val+1) ⟨ht.1, ht.2.trans hFn⟩ (rankValid l))
    (SetupEquivariance.failure_equivariant A F t (l.val+1) ⟨ht.1, ht.2.trans hFn⟩ (rankValid l)) (Fin.last m)
  unfold weightedProbability
  simp_rw [hp, Fintype.card_fin, ← mul_div_assoc]
  rw [← sum_div]
  rw [weighted_card_sum]
  rw [hpay]
  exact congrArg (fun x : ℝ => x / (m+1 : ℕ)) hT

/-- The exact law (6.22), with the supremum taken over actual laws and learners. -/
theorem gammaF_eq (m n F t : ℕ) (hF : 1 ≤ F) (hFn : F ≤ n)
    (ht : 1 ≤ t ∧ t ≤ F) (pi : RankLaw m) :
    gammaF m n F t ⟨ht.1, ht.2.trans hFn⟩ pi = maxObjective F m t pi.mass / (m+1 : ℕ) := by
  obtain ⟨A, Z, hatt⟩ := exists_attaining_model m n F t hF hFn ht pi
  let μ := FiniteExchangeable.blockPermutationLaw Z
  have hmem : maxObjective F m t pi.mass / (m+1 : ℕ) ∈
      {r : ℝ | ∃ (A : Learner UniversalCovariate n)
        (μ : Measure (Fin (m+1) → Block UniversalCovariate n)),
        IsProbabilityMeasure μ ∧ Exchangeable μ ∧
        r = weightedProbability pi.mass A μ F t ⟨ht.1, ht.2.trans hFn⟩ (Fin.last m)} := by
    exact ⟨A, μ, by dsimp [μ]; infer_instance,
      FiniteExchangeable.blockPermutationLaw_exchangeable Z, hatt.symm⟩
  have hb : ∀ r ∈ {r : ℝ | ∃ (A : Learner UniversalCovariate n)
      (μ : Measure (Fin (m+1) → Block UniversalCovariate n)),
      IsProbabilityMeasure μ ∧ Exchangeable μ ∧
      r = weightedProbability pi.mass A μ F t ⟨ht.1, ht.2.trans hFn⟩ (Fin.last m)},
      r ≤ maxObjective F m t pi.mass / (m+1 : ℕ) := by
    intro r hr
    obtain ⟨A, ν, hprob, hex, rfl⟩ := hr
    letI : IsProbabilityMeasure ν := hprob
    exact weighted_probability_le A ν hex _ ht.2 pi.mass pi.nonneg (Fin.last m)
  unfold gammaF
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hb) (le_csSup ⟨_, hb⟩ hmem)

/-- In the automatic `t>F` branch one common learner makes every positive
outer rank fail on every base label. Its exchangeable orbit attains probability
one under the same hidden global rank distribution. -/
theorem gammaF_high_inner (m n F t : ℕ) (hm : 1 ≤ m) (hF : 1 ≤ F) (hFn : F ≤ n)
    (ht : 1 ≤ t ∧ t ≤ n) (htF : F < t) (pi : RankLaw m) : gammaF m n F t ht pi = 1 := by
  let emb := PredictionTable.unitEmbedding (m+1) n
  obtain ⟨R,S,B,hasym,hScard,hmark,hunmark,hrows,hzero⟩ :=
    Sharpness.exists_sharpness_array m n F t 1 hm hFn ht.1 (by omega)
  have hS : S.card = m+1 := by
    have hs' : S.card = min (m+1) (2*(m+1)-1) := by
      simpa only [if_pos htF,Nat.sub_zero] using hScard
    rw [hs']
    omega
  have hSeq : S = univ := eq_of_subset_of_card_le (subset_univ S) (by simpa using hS.ge)
  let A := PredictionTable.tableLearner (PredictionTable.incidenceTable R B) emb
  let Z := PredictionTable.modelData emb
  have hfail (ell : ℕ) (he : 1 ≤ ell ∧ ell ≤ m) (u : Fin (m+1)) :
      Setup.failure A Z u F t ell ht he := by
    apply (RandomizedRanks.model_failure_iff_capacity R hasym B emb emb.injective hF hFn ht he
      hmark hunmark u m le_rfl ?_ (fun j hj => hzero u j (Or.inr hj))).mpr (by omega)
    intro j hj
    simpa using hrows u (by simp [hSeq]) j hj
  let μ := FiniteExchangeable.blockPermutationLaw Z
  have hatt : weightedProbability pi.mass A μ F t ht (Fin.last m) = 1 := by
    change weightedProbability pi.mass A (FiniteExchangeable.blockPermutationLaw Z) F t ht (Fin.last m) = 1
    rw [orbit_weighted_probability]
    simp [hfail,pi.sum_one]
    exact div_self (by positivity)
  have hmem : (1 : ℝ) ∈ {r : ℝ | ∃ (A : Learner UniversalCovariate n)
      (μ : Measure (Fin (m+1) → Block UniversalCovariate n)),
      IsProbabilityMeasure μ ∧ Exchangeable μ ∧ r = weightedProbability pi.mass A μ F t ht (Fin.last m)} :=
    ⟨A,μ,by dsimp [μ]; infer_instance,FiniteExchangeable.blockPermutationLaw_exchangeable Z,hatt.symm⟩
  have hb : ∀ r ∈ {r : ℝ | ∃ (A : Learner UniversalCovariate n)
      (μ : Measure (Fin (m+1) → Block UniversalCovariate n)),
      IsProbabilityMeasure μ ∧ Exchangeable μ ∧ r = weightedProbability pi.mass A μ F t ht (Fin.last m)}, r ≤ 1 := by
    intro r hr
    obtain ⟨A,ν,hprob,_,rfl⟩ := hr
    letI : IsProbabilityMeasure ν := hprob
    unfold weightedProbability
    calc
      _ ≤ ∑ l,pi.mass l*1 := sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left measureReal_le_one (pi.nonneg l))
      _ = 1 := by simpa using pi.sum_one
  unfold gammaF
  exact le_antisymm (csSup_le ⟨1,hmem⟩ hb) (le_csSup ⟨1,hb⟩ hmem)

/-- Theorem 6.3 in the paper's original alpha parametrization. -/
theorem finiteRankGammaPi_eq (m n : ℕ) (alpha : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (t : ℕ) (ht : 1 ≤ t ∧ t ≤ n) (htF : t ≤ failureRank alpha n) (pi : RankLaw m) :
    finiteRankGammaPi m n alpha t ht pi =
      maxObjective (failureRank alpha n) m t pi.mass / (m+1 : ℕ) := by
  have hn : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hFn : failureRank alpha n ≤ n := by
    unfold failureRank
    have hx : alpha*(n:ℝ) < n := by nlinarith
    have hh := (Nat.floor_lt (mul_nonneg ha hnR.le)).mpr hx
    omega
  exact gammaF_eq m n (failureRank alpha n) t (by unfold failureRank; omega) hFn ⟨ht.1,htF⟩ pi

/-- The uniform law on paper ranks two and three in Proposition 6.4. -/
def rank23Law : RankLaw 6 where
  mass l := if l.val=1 ∨ l.val=2 then 1/2 else 0
  nonneg l := by split_ifs <;> norm_num
  sum_one := by norm_num [Fin.sum_univ_succ]

lemma rank23_objective (T : Tour 7) :
    objective 1 6 1 rank23Law.mass T =
      (((univ.filter fun u => 5 ≤ Extensions.Tournament.degree T u).card +
        (univ.filter fun u => 4 ≤ Extensions.Tournament.degree T u).card : ℕ) : ℝ)/2 := by
  have hp (u : Fin 7) : RandomizedRanks.payoff 1 6 1 rank23Law.mass (degree T u) =
      (if 5 ≤ degree T u then (1/2 : ℝ) else 0) +
      (if 4 ≤ degree T u then (1/2 : ℝ) else 0) := by
    norm_num [RandomizedRanks.payoff,rank23Law,Incidence.threshold,Fin.sum_univ_succ]
    have h5 : 6 ≤ degree T u+1 ↔ 5 ≤ degree T u := by omega
    have h4 : 6 ≤ degree T u+2 ↔ 4 ≤ degree T u := by omega
    simp only [h5,h4]
  unfold objective
  simp_rw [hp]
  rw [sum_add_distrib]
  have hs (P : Fin 7 → Prop) :
      (∑ u : Fin 7, if P u then (1/2 : ℝ) else 0) = ((univ.filter P).card : ℝ)/2 := by
    rw [← sum_filter]
    simp [div_eq_mul_inv]
  simp only [sum_ite,sum_const_zero,add_zero,sum_const,nsmul_eq_mul]
  simp only [degree_eq_extensions,Nat.cast_add]
  ring

lemma rank23_maximum : maxObjective 1 6 1 rank23Law.mass = 3 := by
  apply le_antisymm
  · obtain ⟨T,hT⟩ := maxObjective_attained 1 6 1 rank23Law.mass
    rw [←hT,rank23_objective]
    have h := Extensions.Tournament.seven_rank_count T
    have hh : (((univ.filter fun u => 5 ≤ Extensions.Tournament.degree T u).card +
        (univ.filter fun u => 4 ≤ Extensions.Tournament.degree T u).card : ℕ) : ℝ) ≤ 6 := by exact_mod_cast h
    linarith
  · have h := le_maxObjective 1 6 1 rank23Law.mass Extensions.Tournament.sevenWitness
    rw [rank23_objective,Extensions.Tournament.sevenWitness_attains] at h
    norm_num at h ⊢
    exact h

/-- Proposition 6.4 for the actual statistical supremum, together with the two
separate deterministic statistical suprema from Theorem 3.1. -/
theorem nonconvexification_actual :
    finiteRankGammaPi 6 1 (1/2) 1 (by norm_num) rank23Law = 3/7 ∧
    Setup.finiteRankGamma 6 1 (1/2) 1 2 (by norm_num) (by norm_num) = 3/7 ∧
    Setup.finiteRankGamma 6 1 (1/2) 1 3 (by norm_num) (by norm_num) = 5/7 ∧
    (3/7 : ℝ) < (1/2)*(3/7+5/7) ∧ (1/2 : ℝ)*(3/7+5/7) = 4/7 := by
  have hf : ⌊(1/2 : ℝ)⌋₊ = 0 := Nat.floor_eq_zero.mpr (by norm_num)
  constructor
  · rw [finiteRankGammaPi_eq 6 1 (1/2) (by norm_num) (by norm_num) 1
      (by norm_num) (by norm_num [Setup.failureRank]) rank23Law]
    norm_num [Setup.failureRank,hf,rank23_maximum]
  constructor
  · rw [MainExact.finiteRankGamma_eq 6 1 (1/2) (by norm_num) (by norm_num)]
    norm_num [Setup.failureRank,hf,RankFrontier.failureRate,RankFrontier.failureCount,RankFrontier.capacity]
  constructor
  · rw [MainExact.finiteRankGamma_eq 6 1 (1/2) (by norm_num) (by norm_num)]
    norm_num [Setup.failureRank,hf,RankFrontier.failureRate,RankFrontier.failureCount,RankFrontier.capacity]
  norm_num

end
end MEJF.RandomizedProbability
