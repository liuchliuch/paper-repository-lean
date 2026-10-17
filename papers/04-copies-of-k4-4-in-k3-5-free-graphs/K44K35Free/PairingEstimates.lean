import K44K35Free.Construction
import K44K35Free.ExceptionalCounts
import K44K35Free.Lemma6Geometry
import K44K35Free.Copies

/-! Exact finite expectations and the joint preliminary-selection inequality
for the actual quartic incidence construction. -/
noncomputable section
open scoped BigOperators
open Finset
namespace K44K35Free.Construction
open Geometry
variable {F : Type*} [Field F] [Fintype F]

attribute [local instance] Classical.propDecidable

local instance pairingEstimatesLocalInstance1 (α : F) (c : Quartic F) : Fintype (BlockIndex α c) := Fintype.ofFinite _

noncomputable def exceptionalPlanes (α : F) (c : Quartic F) : Finset (Plane F) := by
  classical
  exact univ.filter (Exceptional α c)

@[simp] theorem mem_exceptionalPlanes (α : F) (c : Quartic F) (E : Plane F) :
    E ∈ exceptionalPlanes α c ↔ Exceptional α c E := by
  simp [exceptionalPlanes]

theorem sum_blockIndex (α : F) (c : Quartic F) (f : BlockIndex α c → ℕ) :
    (∑ i, f i) = ∑ b : Bool, ∑ E : {E : Plane F // Exceptional α c E}, f (b, E) := by
  classical
  calc
    (∑ i, f i) = ∑ i ∈ (univ : Finset Bool) ×ˢ
        (univ : Finset {E : Plane F // Exceptional α c E}), f i := by
      apply sum_congr
      · ext i
        simp
      · intro i _
        rfl
    _ = _ := Finset.sum_product _ _ _

theorem totalBlockEdges_eq (α : F) (c : Quartic F) (T : V F ≃ₗ[F] V F) :
    (PreliminaryAlteration.totalBlockEdges (fun i => (actualBlocks α c T i).edges) : ℝ) =
      RandomPairing.exceptionalEdgeSum (exceptionalPlanes α c) polarEquiv
        (fun E => ((planeSection α c E).card : ℝ)) T := by
  classical
  unfold PreliminaryAlteration.totalBlockEdges RandomPairing.exceptionalEdgeSum
  rw [Finset.sum_subtype (exceptionalPlanes α c) (mem_exceptionalPlanes α c)]
  rw [sum_blockIndex]
  simp only [Nat.cast_sum, Fintype.sum_bool,
    actualBlocks, Pruning.sectionBlock, Pruning.Block.edges, card_product,
    Bool.false_eq_true, if_false, if_true, Nat.cast_mul]
  rw [← sum_add_distrib]
  push_cast
  apply sum_congr rfl
  intro E _
  let a : ℝ := (planeSection α c (polar (mapPlane T E.val))).card
  let b : ℝ := (planeSection α c E.val).card
  let d : ℝ := (planeSection α c (mapPlane T.symm (polar E.val))).card
  change a * b + b * d = b * (a + d)
  ring

theorem mutualBlockEdges_eq (α : F) (c : Quartic F) (T : V F ≃ₗ[F] V F) :
    (PreliminaryAlteration.mutualBlockEdges
      (fun i => (actualBlocks α c T i).edges) (actualMutual α c T) : ℝ) =
      RandomPairing.mutualEdgeSum (exceptionalPlanes α c) polarEquiv
        (fun E => ((planeSection α c E).card : ℝ)) T := by
  classical
  unfold PreliminaryAlteration.mutualBlockEdges RandomPairing.mutualEdgeSum
  rw [Finset.sum_subtype (exceptionalPlanes α c) (mem_exceptionalPlanes α c)]
  rw [sum_filter, sum_blockIndex]
  simp only [Nat.cast_sum, Fintype.sum_bool,
    actualBlocks, actualMutual, Pruning.sectionBlock, Pruning.sectionMutual,
    Pruning.Block.edges, card_product, Bool.false_eq_true, if_false, if_true,
    Nat.cast_ite, Nat.cast_mul, Nat.cast_zero, mem_exceptionalPlanes]
  rw [← sum_add_distrib]
  push_cast
  apply sum_congr rfl
  intro E _
  let a : ℝ := (planeSection α c (polar (mapPlane T E.val))).card
  let b : ℝ := (planeSection α c E.val).card
  let d : ℝ := (planeSection α c (mapPlane T.symm (polar E.val))).card
  let A := Exceptional α c (polar (mapPlane T E.val))
  let D := Exceptional α c (mapPlane T.symm (polar E.val))
  change (if A then a * b else 0) + (if D then b * d else 0) =
    b * ((if A then a else 0) + (if D then d else 0))
  split_ifs <;> ring

theorem designatedPairs_eq (α : F) (c : Quartic F) (T : V F ≃ₗ[F] V F) :
    designatedPairs α c T = RandomPairing.designatedPairs (richPlanes α c) polarEquiv T := by
  classical
  ext D
  have hpolar : D.1 = polar (mapPlane T D.2) ↔ mapPlane T D.2 = polar D.1 := by
    constructor
    · intro h
      rw [h, polar_polar]
    · intro h
      rw [h, polar_polar]
  simp only [designatedPairs, RandomPairing.designatedPairs, mem_filter,
    mem_product, leftDual_apply, generalLinear_smul_plane]
  exact and_congr_right fun _ => hpolar

theorem mean_initial_designated (α : F) (c : Quartic F) :
    RandomPairing.mean (fun T : V F ≃ₗ[F] V F => ((designatedPairs α c T).card : ℝ)) =
      ((richPlanes α c).card : ℝ)^2 / Fintype.card (Plane F) := by
  simp_rw [designatedPairs_eq]
  exact mean_designated_planes (richPlanes α c)

theorem copyEdges_subset_initial (α : F) (c : Quartic F) (T : V F ≃ₗ[F] V F)
    (D : Plane F × Plane F) (hD : D ∈ designatedPairs α c T) :
    copyEdges α c D ⊆ initialEdges α c T := by
  classical
  have hd := (mem_designatedPairs α c T D).1 hD
  have hmap : mapPlane T D.2 = polar D.1 := by
    rw [hd.2.2, leftDual_apply, polar_polar]
  intro e he
  rcases mem_product.1 he with ⟨hp, hr⟩
  exact (mem_initialEdges α c T e.1 e.2).2
    (designated_plane_incidence α c T D.1 D.2 hmap hp hr)

theorem mean_totalBlockEdges (α : F) (c : Quartic F) :
    RandomPairing.mean (fun T : V F ≃ₗ[F] V F =>
      (PreliminaryAlteration.totalBlockEdges (fun i => (actualBlocks α c T i).edges) : ℝ)) =
      2 * (∑ E ∈ exceptionalPlanes α c, ((planeSection α c E).card : ℝ)) *
        (∑ E, ((planeSection α c E).card : ℝ)) / Fintype.card (Plane F) := by
  simp_rw [totalBlockEdges_eq]
  exact mean_exceptional_plane_edges α c (exceptionalPlanes α c)

theorem mean_mutualBlockEdges (α : F) (c : Quartic F) :
    RandomPairing.mean (fun T : V F ≃ₗ[F] V F =>
      (PreliminaryAlteration.mutualBlockEdges
        (fun i => (actualBlocks α c T i).edges) (actualMutual α c T) : ℝ)) =
      2 * (∑ E ∈ exceptionalPlanes α c, ((planeSection α c E).card : ℝ))^2 /
        Fintype.card (Plane F) := by
  simp_rw [mutualBlockEdges_eq]
  exact mean_mutual_plane_edges α c (exceptionalPlanes α c)

theorem exceptionalPlanes_eq (α : F) (c : Quartic F) :
    exceptionalPlanes α c = Geometry.exceptionalPlanes α c := by
  ext E
  simp

theorem plane_card_lower_real :
    (Fintype.card F : ℝ)^9 ≤ Fintype.card (Plane F) := by
  have h := pow_nine_le_card_grassmann_three_dim_six (F := F) (V := V F)
    (by simp [V])
  have h' : Fintype.card F ^ 9 ≤ Fintype.card (Plane F) := by
    simpa only [Nat.card_eq_fintype_card] using h
  exact_mod_cast h'

theorem plane_card_upper_real :
    (Fintype.card (Plane F) : ℝ) ≤ 20 * (Fintype.card F : ℝ)^9 := by
  have h := card_grassmann_three_dim_six_le (F := F) (V := V F) (by simp [V])
  have h' : Fintype.card (Plane F) ≤ 20 * Fintype.card F ^ 9 := by
    simpa only [Nat.card_eq_fintype_card] using h
  exact_mod_cast h'

theorem exceptional_mass_le (α : F) (c : Quartic F)
    (hα : IsNonsquare α) (hodd : Odd (Fintype.card F)) :
    (∑ E ∈ exceptionalPlanes α c, ((planeSection α c E).card : ℝ)) ≤
      5 * (Fintype.card F : ℝ)^5 := by
  rw [exceptionalPlanes_eq]
  exact_mod_cast Geometry.exceptional_total_incidence_le α c hα hodd

theorem mean_Z_le (α : F) (c : Quartic F)
    (hα : IsNonsquare α) (hodd : Odd (Fintype.card F)) :
    RandomPairing.mean (fun T : V F ≃ₗ[F] V F =>
      (PreliminaryAlteration.totalBlockEdges (fun i => (actualBlocks α c T i).edges) : ℝ)) ≤
        10 * (Fintype.card F : ℝ)^5 := by
  rw [mean_totalBlockEdges]
  have ha := exceptional_mass_le α c hα hodd
  have havg := Geometry.average_plane_section α c
  have havgle : (∑ E, ((planeSection α c E).card : ℝ)) /
      Fintype.card (Plane F) ≤ 1 := by
    rw [havg]
    apply (div_le_one (by positivity)).2
    linarith
  have hmass : 0 ≤ 2 * (∑ E ∈ exceptionalPlanes α c,
      ((planeSection α c E).card : ℝ)) := by positivity
  calc
    _ = 2 * (∑ E ∈ exceptionalPlanes α c, ((planeSection α c E).card : ℝ)) *
        ((∑ E, ((planeSection α c E).card : ℝ)) / Fintype.card (Plane F)) := by ring
    _ ≤ 2 * (∑ E ∈ exceptionalPlanes α c, ((planeSection α c E).card : ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left havgle hmass
    _ ≤ _ := by linarith

theorem mean_U_le (α : F) (c : Quartic F)
    (hα : IsNonsquare α) (hodd : Odd (Fintype.card F)) :
    RandomPairing.mean (fun T : V F ≃ₗ[F] V F =>
      (PreliminaryAlteration.mutualBlockEdges
        (fun i => (actualBlocks α c T i).edges) (actualMutual α c T) : ℝ)) ≤
        50 * (Fintype.card F : ℝ) := by
  rw [mean_mutualBlockEdges]
  have ha := exceptional_mass_le α c hα hodd
  have hn := plane_card_lower_real (F := F)
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hnpos : (0 : ℝ) < Fintype.card (Plane F) := lt_of_lt_of_le (by positivity) hn
  apply (div_le_iff₀ hnpos).2
  have hs : (∑ E ∈ exceptionalPlanes α c, ((planeSection α c E).card : ℝ)) ^ 2 ≤
      (5 * (Fintype.card F : ℝ)^5)^2 := by
    have hnonneg : 0 ≤ ∑ E ∈ exceptionalPlanes α c,
        ((planeSection α c E).card : ℝ) := by positivity
    nlinarith
  have hn' := mul_le_mul_of_nonneg_left hn (show 0 ≤ 50 * (Fintype.card F : ℝ) by positivity)
  nlinarith

def pairingDenominator : ℕ := 20 * 768 ^ 2

def preliminaryLoad : ℕ := 240 * pairingDenominator

def preliminaryThreshold : ℕ := 1200 * pairingDenominator

theorem mean_K0_lower (α : F) (c : Quartic F)
    (hrich : Fintype.card F ^ 9 ≤ 768 * (richPlanes α c).card) :
    (Fintype.card F : ℝ)^9 / pairingDenominator ≤
      RandomPairing.mean (fun T : V F ≃ₗ[F] V F => ((designatedPairs α c T).card : ℝ)) := by
  rw [mean_initial_designated]
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hn := plane_card_upper_real (F := F)
  have hnlo := plane_card_lower_real (F := F)
  have hnpos : (0 : ℝ) < Fintype.card (Plane F) := lt_of_lt_of_le (by positivity) hnlo
  have hb : (Fintype.card F : ℝ)^9 ≤ 768 * (richPlanes α c).card := by exact_mod_cast hrich
  have hb' : (Fintype.card F : ℝ)^9 / 768 ≤ (richPlanes α c).card := by linarith
  have hbsq : ((Fintype.card F : ℝ)^9 / 768)^2 ≤ ((richPlanes α c).card : ℝ)^2 := by
    have hbnon : (0 : ℝ) ≤ (richPlanes α c).card := by positivity
    nlinarith
  calc
    _ = ((Fintype.card F : ℝ)^9 / 768)^2 / (20 * (Fintype.card F : ℝ)^9) := by
      unfold pairingDenominator
      push_cast
      field_simp
      <;> ring
    _ ≤ ((richPlanes α c).card : ℝ)^2 / (20 * (Fintype.card F : ℝ)^9) :=
      div_le_div_of_nonneg_right hbsq (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) hnpos hn

def preliminaryConstant : ℝ := 1 / (2 * pairingDenominator)

theorem preliminaryConstant_pos : 0 < preliminaryConstant := by
  norm_num [preliminaryConstant, pairingDenominator]

set_option maxHeartbeats 800000 in
theorem preliminary_joint_mean (α : F) (c : Quartic F) (L : ℕ) (hL : 0 < L) :
    ∃ T : V F ≃ₗ[F] V F,
      RandomPairing.mean (fun T : V F ≃ₗ[F] V F => ((designatedPairs α c T).card : ℝ)) -
        gaussianBinom2 (Fintype.card F) *
          (RandomPairing.mean (fun T : V F ≃ₗ[F] V F =>
            (PreliminaryAlteration.mutualBlockEdges
              (fun i => (actualBlocks α c T i).edges) (actualMutual α c T) : ℝ)) +
          RandomPairing.mean (fun T : V F ≃ₗ[F] V F =>
            (PreliminaryAlteration.totalBlockEdges (fun i => (actualBlocks α c T i).edges) : ℝ)) / L) ≤
        ((preDesignated α c T L).card : ℝ) := by
  classical
  obtain ⟨T, hT⟩ := PreliminaryAlteration.exists_preliminary_copies
    (fun T : V F ≃ₗ[F] V F => initialEdges α c T)
    (fun T i => (actualBlocks α c T i).edges)
    (fun T => actualMutual α c T)
    L (fun T => designatedPairs α c T) (copyEdges α c)
    (gaussianBinom2 (Fintype.card F)) hL
    (fun T D hD => copyEdges_subset_initial α c T D hD)
    (fun T e he => designatedPairs_through_edge_le α c T e he)
  exact ⟨T, hT⟩

set_option maxHeartbeats 800000 in
/-- Equations (24)--(25) for the actual finite-field graph, with one fixed
absolute load threshold and one fixed positive copy constant. -/
theorem preliminary_many_copies (α : F) (c : Quartic F)
    (hα : IsNonsquare α) (hodd : Odd (Fintype.card F))
    (hrich : Fintype.card F ^ 9 ≤ 768 * (richPlanes α c).card)
    (hq : preliminaryThreshold ≤ Fintype.card F) :
    ∃ T : V F ≃ₗ[F] V F,
      preliminaryConstant * (Fintype.card F : ℝ)^9 ≤
        ((preDesignated α c T preliminaryLoad).card : ℝ) := by
  classical
  have hL : 0 < preliminaryLoad := by norm_num [preliminaryLoad, pairingDenominator]
  obtain ⟨T, hT⟩ := preliminary_joint_mean α c preliminaryLoad hL
  have hk := mean_K0_lower α c hrich
  have hu := mean_U_le α c hα hodd
  have hz := mean_Z_le α c hα hodd
  have hq2 : 2 ≤ Fintype.card F := by
    have := Fintype.one_lt_card (α := F)
    omega
  have hm : (gaussianBinom2 (Fintype.card F) : ℝ) ≤
      6 * (Fintype.card F : ℝ)^4 := by exact_mod_cast gaussianBinom2_le _ hq2
  have hln : (0 : ℝ) < preliminaryLoad := by exact_mod_cast hL
  have hu0 : 0 ≤ RandomPairing.mean (fun T : V F ≃ₗ[F] V F =>
      (PreliminaryAlteration.mutualBlockEdges
        (fun i => (actualBlocks α c T i).edges) (actualMutual α c T) : ℝ)) := by
    unfold RandomPairing.mean
    positivity
  have hz0 : 0 ≤ RandomPairing.mean (fun T : V F ≃ₗ[F] V F =>
      (PreliminaryAlteration.totalBlockEdges (fun i => (actualBlocks α c T i).edges) : ℝ)) := by
    unfold RandomPairing.mean
    positivity
  have hloss : (gaussianBinom2 (Fintype.card F) : ℝ) *
      (RandomPairing.mean (fun T : V F ≃ₗ[F] V F =>
        (PreliminaryAlteration.mutualBlockEdges
          (fun i => (actualBlocks α c T i).edges) (actualMutual α c T) : ℝ)) +
      RandomPairing.mean (fun T : V F ≃ₗ[F] V F =>
        (PreliminaryAlteration.totalBlockEdges (fun i => (actualBlocks α c T i).edges) : ℝ)) /
          preliminaryLoad) ≤ 300 * (Fintype.card F : ℝ)^5 +
            60 * (Fintype.card F : ℝ)^9 / preliminaryLoad := by
    calc
      _ ≤ (6 * (Fintype.card F : ℝ)^4) *
          (50 * (Fintype.card F : ℝ) + 10 * (Fintype.card F : ℝ)^5 / preliminaryLoad) := by
        apply mul_le_mul hm (add_le_add hu (div_le_div_of_nonneg_right hz hln.le))
        · positivity
        · positivity
      _ = _ := by ring
  have hq1 : 1 ≤ Fintype.card F := Fintype.card_pos
  have hpow : Fintype.card F ≤ Fintype.card F ^ 4 := by
    simpa using Nat.pow_le_pow_right hq1 (show 1 ≤ 4 by omega)
  have hthresh : (1200 * pairingDenominator : ℝ) ≤ (Fintype.card F : ℝ)^4 := by
    exact_mod_cast hq.trans hpow
  have hsmall : 300 * (Fintype.card F : ℝ)^5 ≤
      (Fintype.card F : ℝ)^9 / (4 * pairingDenominator) := by
    apply (le_div_iff₀ (by norm_num [pairingDenominator])).2
    have h := mul_le_mul_of_nonneg_left hthresh
      (show 0 ≤ (Fintype.card F : ℝ)^5 by positivity)
    nlinarith only [h]
  have hload : 60 * (Fintype.card F : ℝ)^9 / preliminaryLoad =
      (Fintype.card F : ℝ)^9 / (4 * pairingDenominator) := by
    norm_num [preliminaryLoad, pairingDenominator]
    <;> ring
  rw [hload] at hloss
  refine ⟨T, ?_⟩
  have heq : preliminaryConstant * (Fintype.card F : ℝ)^9 =
      (Fintype.card F : ℝ)^9 / pairingDenominator -
      (Fintype.card F : ℝ)^9 / (4 * pairingDenominator) -
      (Fintype.card F : ℝ)^9 / (4 * pairingDenominator) := by
    unfold preliminaryConstant
    ring
  rw [heq]
  linarith only [hT, hk, hloss, hsmall]

/-- Choose the monic quartic and the pairing together.  The load and the
positive constant are absolute and independent of the field. -/
theorem exists_preliminary_many_copies (α : F) (hα : IsNonsquare α)
    (hodd : Odd (Fintype.card F)) (hq : preliminaryThreshold ≤ Fintype.card F) :
    ∃ (c : Quartic F) (T : V F ≃ₗ[F] V F),
      preliminaryConstant * (Fintype.card F : ℝ)^9 ≤
        ((preDesignated α c T preliminaryLoad).card : ℝ) := by
  have hq8 : 8 ≤ Fintype.card F := by
    have : 8 ≤ preliminaryThreshold := by norm_num [preliminaryThreshold, pairingDenominator]
    omega
  obtain ⟨c, hc⟩ := lemma_6_many_richPlanes α hα (char_ne_two_of_odd_card hodd) hq8
  obtain ⟨T, hT⟩ := preliminary_many_copies α c hα hodd hc hq
  exact ⟨c, T, hT⟩

end K44K35Free.Construction
