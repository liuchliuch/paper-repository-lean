import Paper09.PercolationLabels
import Paper09.FinePercolation
import Paper09.BlockCovering
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Complex.ExponentialBounds

open Finset BigOperators Classical MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology

noncomputable section
set_option maxHeartbeats 1000000

namespace Paper09.Percolation

/-- Fine-cluster tail for the actual Gaussian and uniform construction (3.2).
The sharp exploration count is applied to exact finite mark probabilities. -/
theorem annealed_cluster_tail {d : ℕ} (hd : 0 < d) (σ K ρ : ℝ)
    (hp : markParameter σ K ρ ≤ 1 / (20 * (d : ℝ)))
    (z : LatticeGeometry.Point d) (r : ℕ) (hr : 0 < r) :
    (jointLaw d σ).real
      {a | clusterAtLeast (nnGraph d) (siteOpen K ρ a.1 a.2) z r} ≤
        (Real.exp 1 / 10) ^ r := by
  exact Fine.lattice_cluster_probability_le d hd (jointLaw d σ)
    (fun a => siteOpen K ρ a.1 a.2) (markParameter σ K ρ)
    (markParameter_nonneg σ K ρ)
    (fun S => (joint_all_open_probability σ K ρ S).le) hp z r hr

/-- The two sparsity inequalities in Assumption 1.2 imply the required
annealed mark parameter, with its actual Gaussian weak-field probability. -/
theorem markParameter_strong_bound {d : ℕ} (hd : 0 < d) (σ K ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρsmall : ρ < 1 / (40 * (d : ℝ)))
    (hweak : (Gaussian.law σ).real {x | |x| ≤ K} < 1 / (40 * (d : ℝ))) :
    markParameter σ K ρ < 1 / (20 * (d : ℝ)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hρ1 : ρ ≤ 1 := by
    have h := (lt_div_iff₀ (show (0 : ℝ) < 40 * d by positivity)).mp hρsmall
    nlinarith [mul_le_mul_of_nonneg_right hd1 hρ]
  unfold markParameter
  rw [oneSiteMarkLaw_true σ K ρ hρ hρ1]
  have hpk : 0 ≤ (Gaussian.law σ).real {x | |x| ≤ K} := ENNReal.toReal_nonneg
  have hle : (1 - (Gaussian.law σ).real {x | |x| ≤ K}) * ρ ≤ ρ := by
    nlinarith [mul_nonneg hpk hρ]
  have hsum : 1 / (40 * (d : ℝ)) + 1 / (40 * d) = 1 / (20 * d) := by
    field_simp
    <;> ring
  linarith

/-- The Markov-and-union part of (3.4), now for the actual quenched label. -/
theorem badLabel_probability_sum {d : ℕ} (hd : 0 < d) (σ K ρ : ℝ)
    (hp : markParameter σ K ρ ≤ 1 / (20 * (d : ℝ)))
    (R r0 s : ℕ) (hr0 : 0 < r0) (v : LatticeGeometry.Point d) :
    (RFIM.environmentLaw d σ).real {h | ¬goodLabel K ρ R r0 s h v} ≤
      ((2 * R + 1 : ℕ) : ℝ) ^ d *
        ∑ r ∈ Finset.Icc r0 s, (Real.exp 1 ^ 2 / 10) ^ r := by
  have hset : {h | ¬goodLabel K ρ R r0 s h v} =
      ⋃ z ∈ latticeCube (coarseCenter R v) R, ⋃ r ∈ Finset.Icc r0 s,
        {h | Real.exp (-(r : ℝ)) < quenchedCluster K ρ h z r} := by
    ext h
    simp only [Set.mem_setOf_eq, goodLabel, not_forall, not_le, exists_prop,
      Set.mem_iUnion, Finset.mem_Icc]
    constructor
    · rintro ⟨z, hz, r, hr, hrs, hb⟩
      exact ⟨z, hz, r, ⟨hr, hrs⟩, hb⟩
    · rintro ⟨z, hz, r, ⟨hr, hrs⟩, hb⟩
      exact ⟨z, hz, r, hr, hrs, hb⟩
  rw [hset]
  apply (measureReal_biUnion_finset_le _ _).trans
  calc
    (∑ z ∈ latticeCube (coarseCenter R v) R, (RFIM.environmentLaw d σ).real
      (⋃ r ∈ Finset.Icc r0 s, {h | Real.exp (-(r : ℝ)) < quenchedCluster K ρ h z r}))
        ≤ ∑ z ∈ latticeCube (coarseCenter R v) R,
          ∑ r ∈ Finset.Icc r0 s, (Real.exp 1 ^ 2 / 10) ^ r := by
      apply sum_le_sum
      intro z hz
      apply (measureReal_biUnion_finset_le _ _).trans
      apply sum_le_sum
      intro r hr
      have hr' : 0 < r := by have := (Finset.mem_Icc.mp hr).1; omega
      apply (quenchedCluster_bad_probability σ K ρ z r hr').trans
      have htail := annealed_cluster_tail hd σ K ρ hp z r hr'
      have hm := mul_le_mul_of_nonneg_left htail (Real.exp_nonneg (r : ℝ))
      have heq : Real.exp (r : ℝ) * (Real.exp 1 / 10) ^ r =
          (Real.exp 1 ^ 2 / 10) ^ r := by
        rw [show Real.exp (r : ℝ) = Real.exp 1 ^ r by simp,
          ← mul_pow]
        congr 1
        ring
      simpa only [heq] using hm
    _ = _ := by simp [card_latticeCube]

/-- The coarse component convention used by the deterministic block covering
is exactly the actual irreflexive star-graph component; self steps do not matter. -/
theorem block_clusterSet_eq {d : ℕ} (good : LatticeGeometry.Point d → Prop)
    (z : LatticeGeometry.Point d) :
    BlockCovering.clusterSet good z = cluster (starGraph d) (fun v => ¬good v) z := by
  ext x
  constructor
  · rintro ⟨hz, hreach⟩
    refine ⟨hz, ?_⟩
    induction hreach with
    | refl => exact .rfl
    | @tail y x hreach hstep ih =>
      by_cases hyx : y = x
      · simpa [hyx] using ih
      · have he : (openGraph (starGraph d) (fun v => ¬good v)).Adj y x := by
          refine ⟨⟨hyx, ?_⟩, hstep.1, hstep.2.1⟩
          intro j
          have h := hstep.2.2 j
          dsimp [BlockCovering.StarNear, BlockCovering.Near] at h
          omega
        exact ih.trans he.reachable
  · rintro ⟨hz, ⟨p⟩⟩
    refine ⟨hz, ?_⟩
    induction p with
    | nil => exact .refl
    | @cons z y x h p ih =>
      apply Relation.ReflTransGen.head ?_ (ih h.2.2)
      refine ⟨h.2.1, h.2.2, ?_⟩
      intro j
      have hj := h.1.2 j
      dsimp [BlockCovering.StarNear, BlockCovering.Near]
      omega

/-- Coarse cluster tail from actual residue independence and the proved
connected-animal enumeration. No cluster probability is assumed. -/
theorem coarse_cluster_probability_bound {d : ℕ} (σ K ρ : ℝ) (R r0 s : ℕ)
    (hR : 0 < R) (hr0 : 0 < r0) (hsR : s ≤ R)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hmarg : ∀ v : LatticeGeometry.Point d,
      (RFIM.environmentLaw d σ).real {h | ¬goodLabel K ρ R r0 s h v} ≤ q)
    (z : LatticeGeometry.Point d) (r : ℕ) (hr : 0 < r) :
    (RFIM.environmentLaw d σ).real {h | clusterAtLeast (starGraph d)
      (fun v => ¬goodLabel K ρ R r0 s h v) z r} ≤
        ((3 ^ d - 1 : ℕ) : ℝ) ^ (2 * (r - 1)) *
          q ^ ((r : ℝ) / (5 : ℝ) ^ d) := by
  classical
  have hset : {h | clusterAtLeast (starGraph d)
      (fun v => ¬goodLabel K ρ R r0 s h v) z r} =
      ⋃ S ∈ rootedAnimals (starGraph d) z r, {h | ∀ v ∈ S, ¬goodLabel K ρ R r0 s h v} := by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    exact clusterAtLeast_iff_animal (starGraph d) _ z r hr
  rw [hset]
  apply (measureReal_biUnion_finset_le _ _).trans
  calc
    (∑ S ∈ rootedAnimals (starGraph d) z r,
      (RFIM.environmentLaw d σ).real {h | ∀ v ∈ S, ¬goodLabel K ρ R r0 s h v})
        ≤ ∑ _S ∈ rootedAnimals (starGraph d) z r,
          q ^ ((r : ℝ) / (5 : ℝ) ^ d) := by
      apply sum_le_sum
      intro S hS
      have hc := (mem_filter.mp hS).2
      simpa only [hc] using all_bad_probability_bound σ K ρ R r0 s hR hr0 hsR
        S q hq hq1 (fun v _ => hmarg v)
    _ = ((rootedAnimals (starGraph d) z r).card : ℝ) *
        q ^ ((r : ℝ) / (5 : ℝ) ^ d) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hq _)
      exact_mod_cast card_rootedAnimals_le (starGraph d) (3 ^ d - 1)
        starGraph_degree_le z r

/-- The geometric ratio after quenched Markov's inequality. -/
def tailBase : ℝ := Real.exp 1 ^ 2 / 10

theorem tailBase_pos : 0 < tailBase := by unfold tailBase; positivity

theorem tailBase_lt_one : tailBase < 1 := by
  have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have he0 := Real.exp_pos 1
  unfold tailBase
  nlinarith

/-- An explicit scale-dependent upper bound for every one-site bad label. -/
def badMarginalBound (d R : ℕ) : ℝ :=
  ((2 * R + 1 : ℕ) : ℝ) ^ d * tailBase ^ initialRadius R / (1 - tailBase)

theorem badMarginalBound_nonneg (d R : ℕ) : 0 ≤ badMarginalBound d R := by
  unfold badMarginalBound
  exact div_nonneg (mul_nonneg (by positivity) (pow_nonneg tailBase_pos.le _))
    (sub_nonneg.mpr tailBase_lt_one.le)

theorem badLabel_probability_geometric {d : ℕ} (hd : 0 < d) (σ K ρ : ℝ)
    (hp : markParameter σ K ρ ≤ 1 / (20 * (d : ℝ)))
    (R s : ℕ) (hr0 : 0 < initialRadius R) (v : LatticeGeometry.Point d) :
    (RFIM.environmentLaw d σ).real {h | ¬goodLabel K ρ R (initialRadius R) s h v} ≤
      badMarginalBound d R := by
  apply (badLabel_probability_sum hd σ K ρ hp R (initialRadius R) s hr0 v).trans
  have hIcc : Finset.Icc (initialRadius R) s = Finset.Ico (initialRadius R) (s + 1) := by
    ext r
    simp only [mem_Icc, mem_Ico]
    omega
  unfold badMarginalBound
  rw [hIcc]
  have hg := geom_sum_Ico_le_of_lt_one (m := initialRadius R) (n := s + 1)
    tailBase_pos.le tailBase_lt_one
  exact (mul_le_mul_of_nonneg_left hg (by positivity)).trans_eq (by ring)

/-- The squared-logarithmic cutoff eventually dominates every fixed power.
This quantitative form also makes the subsequent choice of `R0` transparent. -/
theorem badMarginalBound_le_inv (d R : ℕ) (hR : 1 ≤ R)
    (hlog : ((d + 1 : ℕ) : ℝ) / (-Real.log tailBase) ≤ Real.log (R : ℝ)) :
    badMarginalBound d R ≤ (3 ^ d / (1 - tailBase)) / R := by
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hlog0 : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg hR1
  have hc : 0 < -Real.log tailBase := neg_pos.mpr (Real.log_neg tailBase_pos tailBase_lt_one)
  have hquad : ((d + 1 : ℕ) : ℝ) * Real.log (R : ℝ) ≤
      (-Real.log tailBase) * (Real.log (R : ℝ)) ^ 2 := by
    have hh := (div_le_iff₀ hc).mp hlog
    have hm := mul_le_mul_of_nonneg_right hh hlog0
    nlinarith
  have hceil : (Real.log (R : ℝ)) ^ 2 ≤ (initialRadius R : ℝ) := Nat.le_ceil _
  have hpow : tailBase ^ initialRadius R ≤ ((R : ℝ) ^ (d + 1))⁻¹ := by
    calc
      _ = Real.exp (Real.log tailBase * (initialRadius R : ℝ)) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos tailBase_pos]
      _ ≤ Real.exp (Real.log tailBase * (Real.log (R : ℝ)) ^ 2) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left hceil (Real.log_neg tailBase_pos tailBase_lt_one).le
      _ ≤ Real.exp (-(((d + 1 : ℕ) : ℝ) * Real.log (R : ℝ))) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = ((R : ℝ) ^ (d + 1))⁻¹ := by
        rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hR0]
  have hpoly : (((2 * R + 1 : ℕ) : ℝ) ^ d) ≤ (3 * (R : ℝ)) ^ d := by
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    linarith
  unfold badMarginalBound
  calc
    _ ≤ (3 * (R : ℝ)) ^ d * ((R : ℝ) ^ (d + 1))⁻¹ / (1 - tailBase) := by
      apply div_le_div_of_nonneg_right _ (by linarith [tailBase_lt_one])
      exact mul_le_mul hpoly hpow (pow_nonneg tailBase_pos.le _) (by positivity)
    _ = (3 ^ d / (1 - tailBase)) / R := by
      rw [mul_pow, pow_succ]
      field_simp

/-- Actual one-site bad-label probabilities tend uniformly to zero at the
paper's squared-logarithmic cutoff. -/
theorem tendsto_badMarginalBound (d : ℕ) :
    Tendsto (badMarginalBound d) atTop (𝓝 0) := by
  have hcast : Tendsto (fun R : ℕ => (R : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp hcast
  have hinv : Tendsto (fun R : ℕ => (3 ^ d / (1 - tailBase)) / (R : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcast
  apply squeeze_zero' (Filter.Eventually.of_forall (badMarginalBound_nonneg d)) _ hinv
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hlog.eventually_ge_atTop (((d + 1 : ℕ) : ℝ) / (-Real.log tailBase))] with R hR hl
  exact badMarginalBound_le_inv d R hR hl

/-- Small enough one-site bad probabilities give the source exponential
coarse cluster tail, with all finite dependence handled by actual labels. -/
theorem coarse_cluster_exponential_tail {d : ℕ} (hd : 0 < d)
    (σ K ρ : ℝ) (R r0 s : ℕ) (hR : 0 < R) (hr0 : 0 < r0) (hsR : s ≤ R)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hmarg : ∀ v : LatticeGeometry.Point d,
      (RFIM.environmentLaw d σ).real {h | ¬goodLabel K ρ R r0 s h v} ≤ q)
    (hsmall : (((3 ^ d - 1 : ℕ) : ℝ) ^ 2) * q ^ (1 / (5 : ℝ) ^ d) ≤ Real.exp (-3))
    (z : LatticeGeometry.Point d) (r : ℕ) (hr : 0 < r) :
    (RFIM.environmentLaw d σ).real {h | clusterAtLeast (starGraph d)
      (fun v => ¬goodLabel K ρ R r0 s h v) z r} ≤ Real.exp (-3 * (r : ℝ)) := by
  apply (coarse_cluster_probability_bound σ K ρ R r0 s hR hr0 hsR q hq hq1 hmarg z r hr).trans
  have hD : (1 : ℝ) ≤ ((3 ^ d - 1 : ℕ) : ℝ) := by
    have hpow : (1 : ℕ) < 3 ^ d := one_lt_pow₀ (by norm_num) (by omega)
    exact_mod_cast (by omega : 1 ≤ 3 ^ d - 1)
  have hpoly := pow_le_pow_right₀ hD (show 2 * (r - 1) ≤ 2 * r by omega)
  have hqpow : q ^ ((r : ℝ) / (5 : ℝ) ^ d) = (q ^ (1 / (5 : ℝ) ^ d)) ^ r := by
    rw [← Real.rpow_mul_natCast hq]
    congr 1
    ring
  calc
    _ ≤ (((3 ^ d - 1 : ℕ) : ℝ) ^ (2 * r)) * q ^ ((r : ℝ) / (5 : ℝ) ^ d) :=
      mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hq _)
    _ = ((((3 ^ d - 1 : ℕ) : ℝ) ^ 2) * q ^ (1 / (5 : ℝ) ^ d)) ^ r := by
      rw [hqpow, pow_mul, ← mul_pow]
    _ ≤ (Real.exp (-3)) ^ r := pow_le_pow_left₀ (by positivity) hsmall r
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- The complete coarse cluster exponential estimate holds uniformly for all
sufficiently large scales, under the actual annealed mark-parameter condition. -/
theorem eventually_coarse_cluster_tail {d : ℕ} (hd : 0 < d) (σ K ρ : ℝ)
    (hp : markParameter σ K ρ ≤ 1 / (20 * (d : ℝ))) :
    ∃ R0 : ℕ, 4 ≤ R0 ∧ ∀ R : ℕ, R0 ≤ R → ∀ s : ℕ, s ≤ R →
      ∀ z : LatticeGeometry.Point d, ∀ r : ℕ, 0 < r →
        (RFIM.environmentLaw d σ).real {h | clusterAtLeast (starGraph d)
          (fun v => ¬goodLabel K ρ R (initialRadius R) s h v) z r} ≤
            Real.exp (-3 * (r : ℝ)) := by
  let a : ℝ := 1 / (5 : ℝ) ^ d
  have ha : 0 < a := by dsimp [a]; positivity
  have ht := (tendsto_badMarginalBound d).rpow_const (p := a) (Or.inr ha.le)
  have hzero : (0 : ℝ) ^ a = 0 := Real.zero_rpow ha.ne'
  rw [hzero] at ht
  have ht' := (tendsto_const_nhds (x := (((3 ^ d - 1 : ℕ) : ℝ) ^ 2))).mul ht
  simp only [mul_zero] at ht'
  have hsmall := ht'.eventually (gt_mem_nhds (Real.exp_pos (-3)))
  have hqone := (tendsto_badMarginalBound d).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨R1, hR1⟩ := eventually_atTop.mp (hsmall.and hqone)
  refine ⟨max 4 R1, le_max_left _ _, ?_⟩
  intro R hR s hsR z r hr
  have hR4 : 4 ≤ R := (le_max_left _ _).trans hR
  have hR1' : R1 ≤ R := (le_max_right _ _).trans hR
  have hr0 : 0 < initialRadius R := by
    have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < R))
    have hceil : (Real.log (R : ℝ)) ^ 2 ≤ (initialRadius R : ℝ) := Nat.le_ceil _
    exact_mod_cast (lt_of_lt_of_le (sq_pos_of_pos hlog) hceil)
  apply coarse_cluster_exponential_tail hd σ K ρ R (initialRadius R) s (by omega) hr0 hsR
    (badMarginalBound d R) (badMarginalBound_nonneg d R) (hR1 R hR1').2.le
    (fun v => badLabel_probability_geometric hd σ K ρ hp R s hr0 v)
    (hR1 R hR1').1.le z r hr

/-- Relevant physical coarse centers give a finite deterministic index cube. -/
theorem relevant_index_mem_cube {d : ℕ} (n s : ℕ) (hs : 0 < s)
    (k : LatticeGeometry.Point d)
    (hk : BlockCovering.Near (n + 8 * s) (BlockCovering.center s k) 0) :
    k ∈ latticeCube (0 : LatticeGeometry.Point d) (n + 1) := by
  apply mem_latticeCube.mpr
  intro j
  have h := hk j
  dsimp [BlockCovering.center] at h
  push_cast at h
  have hR : (0 : ℤ) < 8 * s := by positivity
  have hnR : (n : ℤ) ≤ (n : ℤ) * (8 * s) := by
    have hm := mul_nonneg (show (0 : ℤ) ≤ n by positivity)
      (show (0 : ℤ) ≤ 8 * s - 1 by omega)
    nlinarith
  have hup : k j ≤ (n : ℤ) + 1 := (mul_le_mul_right hR).mp (by nlinarith :
    k j * (8 * (s : ℤ)) ≤ ((n : ℤ) + 1) * (8 * s))
  have hlo : -((n : ℤ) + 1) ≤ k j := (mul_le_mul_right hR).mp (by nlinarith :
    (-((n : ℤ) + 1)) * (8 * (s : ℤ)) ≤ k j * (8 * s))
  simpa using And.intro hlo hup

/-- The final union bound over all physically relevant coarse sites. Its good
event is exactly strong enough to supply the block-covering `SmallClusters`. -/
theorem smallClusters_probability_strong {d : ℕ} (σ K ρ : ℝ)
    (n s L : ℕ) (hn : 4 ≤ n) (hs : 0 < s) (hr0 : 0 < initialRadius (8 * s))
    (htail : ∀ z : LatticeGeometry.Point d, ∀ r : ℕ, 0 < r →
      (RFIM.environmentLaw d σ).real {h | clusterAtLeast (starGraph d)
        (fun v => ¬goodLabel K ρ (8 * s) (initialRadius (8 * s)) s h v) z r} ≤
          Real.exp (-3 * (r : ℝ)))
    (hL : (d : ℝ) * Real.log (n : ℝ) ≤ L) :
    1 - Real.exp (-(L : ℝ) - 3) ≤ (RFIM.environmentLaw d σ).real
      {h | BlockCovering.SmallClusters
        (goodLabel K ρ (8 * s) (initialRadius (8 * s)) s h) n s L} := by
  classical
  let good := fun h : LatticeGeometry.Point d → ℝ => goodLabel K ρ (8 * s) (initialRadius (8 * s)) s h
  let T := latticeCube (0 : LatticeGeometry.Point d) (n + 1)
  let E : Set (LatticeGeometry.Point d → ℝ) :=
    ⋃ z ∈ T, {h | clusterAtLeast (starGraph d) (fun v => ¬good h v) z (L + 1)}
  have hE : MeasurableSet E := by
    apply Finset.measurableSet_biUnion
    intro z hz
    exact measurableSet_clusterAtLeast (starGraph d) (fun h v => ¬good h v)
      (fun v => (measurableSet_goodLabel K ρ (8 * s) (initialRadius (8 * s)) s v hr0).compl)
      z (L + 1) (by omega)
  have hEprob : (RFIM.environmentLaw d σ).real E ≤
      (T.card : ℝ) * Real.exp (-3 * ((L + 1 : ℕ) : ℝ)) := by
    apply (measureReal_biUnion_finset_le _ _).trans
    calc
      _ ≤ ∑ _z ∈ T, Real.exp (-3 * ((L + 1 : ℕ) : ℝ)) :=
        sum_le_sum (fun z _ => htail z (L + 1) (by omega))
      _ = _ := by simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (by omega : 3 ≤ n)
  have hTcard : (T.card : ℝ) ≤ Real.exp (2 * (L : ℝ)) := by
    have hpoly : (2 * (n : ℝ) + 3) ^ d ≤ ((n : ℝ) ^ 2) ^ d := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [mul_nonneg (sub_nonneg.mpr hn3) (show (0 : ℝ) ≤ n + 1 by positivity)]
    calc
      _ = (2 * (n : ℝ) + 3) ^ d := by simp [T, card_latticeCube]; congr 1; ring
      _ ≤ ((n : ℝ) ^ 2) ^ d := hpoly
      _ = Real.exp (((2 * d : ℕ) : ℝ) * Real.log (n : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log hn0, pow_mul]
      _ ≤ Real.exp (2 * (L : ℝ)) := by
        apply Real.exp_le_exp.mpr
        push_cast
        linarith
  have hfail : (RFIM.environmentLaw d σ).real E ≤ Real.exp (-(L : ℝ) - 3) := by
    apply hEprob.trans
    calc
      _ ≤ Real.exp (2 * (L : ℝ)) * Real.exp (-3 * ((L + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hTcard (Real.exp_nonneg _)
      _ = Real.exp (2 * (L : ℝ) - 3 * ((L + 1 : ℕ) : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by apply Real.exp_le_exp.mpr; push_cast; linarith
  have hsub : Eᶜ ⊆ {h | BlockCovering.SmallClusters (good h) n s L} := by
    intro h hh k hk
    have hkT := relevant_index_mem_cube n s hs k hk
    have hnlarge : ¬clusterAtLeast (starGraph d) (fun v => ¬good h v) k (L + 1) := by
      intro hc
      exact hh (Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hkT, hc⟩⟩)
    have hb := (not_clusterAtLeast_iff k L).mp hnlarge
    simpa only [block_clusterSet_eq] using hb
  calc
    1 - Real.exp (-(L : ℝ) - 3) ≤ 1 - (RFIM.environmentLaw d σ).real E := by linarith
    _ = (RFIM.environmentLaw d σ).real Eᶜ := by rw [measureReal_compl hE, measureReal_univ_eq_one]
    _ ≤ _ := measureReal_mono hsub

/-- Lemma 3.2 for every divisible-by-eight scale, with the actual Gaussian and
uniform construction and the exact environmental event used by Lemma 3.3.
The only disorder condition is the actual annealed opening-parameter threshold. -/
theorem lemma_3_2_parameter {d : ℕ} (hd : 0 < d) (σ K ρ : ℝ)
    (hp : markParameter σ K ρ ≤ 1 / (20 * (d : ℝ))) :
    ∃ R0 : ℕ, ∃ κ : ℝ, 0 < κ ∧ ∀ R n L : ℕ,
      R0 ≤ R → R ≤ n → 8 ∣ R → κ * Real.log (n : ℝ) ≤ L →
        1 - Real.exp (-(L : ℝ)) ≤ (RFIM.environmentLaw d σ).real
          {h | BlockCovering.SmallClusters
            (goodLabel K ρ R (initialRadius R) (R / 8) h) n (R / 8) L} := by
  obtain ⟨R0, hR04, htail⟩ := eventually_coarse_cluster_tail hd σ K ρ hp
  refine ⟨R0, (d : ℝ), by exact_mod_cast hd, ?_⟩
  intro R n L hR hRn hdiv hL
  have hR4 : 4 ≤ R := hR04.trans hR
  have hRpos : 0 < R := by omega
  have hRs : 8 * (R / 8) = R := Nat.mul_div_cancel' hdiv
  have hs : 0 < R / 8 := by omega
  have hr0 : 0 < initialRadius R := by
    have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < R))
    exact_mod_cast (lt_of_lt_of_le (sq_pos_of_pos hlog)
      (Nat.le_ceil ((Real.log (R : ℝ)) ^ 2)))
  have ht := htail R hR (R / 8) (Nat.div_le_self _ _) 
  have hbound := smallClusters_probability_strong σ K ρ n (R / 8) L
    (hR4.trans hRn) hs (by simpa only [hRs] using hr0)
    (by simpa only [hRs] using ht) hL
  apply le_trans (b := 1 - Real.exp (-(L : ℝ) - 3))
  · have he := Real.exp_le_exp.mpr (show -(L : ℝ) - 3 ≤ -(L : ℝ) by linarith)
    linarith
  · simpa only [hRs] using hbound

/-- Lemma 3.2 directly under the paper's two strong-disorder sparsity
inequalities, with no cluster-tail or independence certificate assumptions. -/
theorem lemma_3_2 {d : ℕ} (hd : 0 < d) (σ K ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρsmall : ρ < 1 / (40 * (d : ℝ)))
    (hweak : (Gaussian.law σ).real {x | |x| ≤ K} < 1 / (40 * (d : ℝ))) :
    ∃ R0 : ℕ, ∃ κ : ℝ, 0 < κ ∧ ∀ R n L : ℕ,
      R0 ≤ R → R ≤ n → 8 ∣ R → κ * Real.log (n : ℝ) ≤ L →
        1 - Real.exp (-(L : ℝ)) ≤ (RFIM.environmentLaw d σ).real
          {h | BlockCovering.SmallClusters
            (goodLabel K ρ R (initialRadius R) (R / 8) h) n (R / 8) L} :=
  lemma_3_2_parameter hd σ K ρ (markParameter_strong_bound hd σ K ρ hρ hρsmall hweak).le

/-- The paper's explicit exponential rate in (3.4). -/
def quenchedDecay : ℝ := Real.log 10 - 2

theorem tailBase_eq_exp_decay : tailBase = Real.exp (-quenchedDecay) := by
  unfold tailBase quenchedDecay
  have h10 : (10 : ℝ) = Real.exp (Real.log 10) := (Real.exp_log (by norm_num)).symm
  have h2 : Real.exp 1 ^ 2 = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h2, h10, ← Real.exp_sub]
  congr 1
  simp only [Real.log_exp]
  ring

theorem quenchedDecay_pos : 0 < quenchedDecay := by
  have h := tailBase_lt_one
  rw [tailBase_eq_exp_decay, Real.exp_lt_one_iff] at h
  linarith

/-- Exact source form (3.4), with `c = log 10 - 2 > 0`. -/
theorem badLabel_probability_exp {d : ℕ} (hd : 0 < d) (σ K ρ : ℝ)
    (hp : markParameter σ K ρ ≤ 1 / (20 * (d : ℝ)))
    (R s : ℕ) (hR : 1 ≤ R) (hr0 : 0 < initialRadius R)
    (v : LatticeGeometry.Point d) :
    (RFIM.environmentLaw d σ).real {h | ¬goodLabel K ρ R (initialRadius R) s h v} ≤
      (3 ^ d / (1 - tailBase)) * (R : ℝ) ^ d *
        Real.exp (-quenchedDecay * (initialRadius R : ℝ)) := by
  apply (badLabel_probability_geometric hd σ K ρ hp R s hr0 v).trans
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hpoly : (((2 * R + 1 : ℕ) : ℝ) ^ d) ≤ (3 * (R : ℝ)) ^ d := by
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    linarith
  have heq : tailBase ^ initialRadius R =
      Real.exp (-quenchedDecay * (initialRadius R : ℝ)) := by
    rw [tailBase_eq_exp_decay, ← Real.exp_nat_mul]
    congr 1
    ring
  unfold badMarginalBound
  rw [heq]
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg _))
    (sub_nonneg.mpr tailBase_lt_one.le)).trans_eq
  rw [mul_pow]
  ring

/-- The source bad-cluster event with an arbitrary real size threshold. -/
def SmallClustersReal {d : ℕ} (good : LatticeGeometry.Point d → Prop)
    (n R : ℕ) (L : ℝ) : Prop :=
  ∀ k : LatticeGeometry.Point d,
    BlockCovering.Near (n + R) (coarseCenter R k) 0 →
      (BlockCovering.clusterSet good k).Finite ∧
        ((BlockCovering.clusterSet good k).ncard : ℝ) ≤ L

/-- Lemma 3.2 preserving the original real threshold quantifier. The
integer approximation is only internal, and the stated probability is still
`1-exp(-L)` for the exact real `L`. -/
theorem lemma_3_2_real {d : ℕ} (hd : 0 < d) (σ K ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρsmall : ρ < 1 / (40 * (d : ℝ)))
    (hweak : (Gaussian.law σ).real {x | |x| ≤ K} < 1 / (40 * (d : ℝ))) :
    ∃ R0 : ℕ, ∃ κ : ℝ, 0 < κ ∧ ∀ R n : ℕ, ∀ L : ℝ,
      R0 ≤ R → R ≤ n → 8 ∣ R → κ * Real.log (n : ℝ) ≤ L →
        1 - Real.exp (-L) ≤ (RFIM.environmentLaw d σ).real
          {h | SmallClustersReal
            (goodLabel K ρ R (initialRadius R) (R / 8) h) n R L} := by
  have hp := (markParameter_strong_bound hd σ K ρ hρ hρsmall hweak).le
  obtain ⟨R0, hR04, htail⟩ := eventually_coarse_cluster_tail hd σ K ρ hp
  refine ⟨R0, (d : ℝ) + 1, by positivity, ?_⟩
  intro R n L hR hRn hdiv hL
  have hR4 : 4 ≤ R := hR04.trans hR
  have hn4 : 4 ≤ n := hR4.trans hRn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (by omega : 3 ≤ n)
  have hlog1 : 1 < Real.log (n : ℝ) := (Real.lt_log_iff_exp_lt hn0).mpr
    (Real.exp_one_lt_d9.trans (by linarith))
  have hL0 : 0 ≤ L := by nlinarith
  let M := Nat.floor L
  have hML : (M : ℝ) ≤ L := Nat.floor_le hL0
  have hLM : L < (M : ℝ) + 1 := Nat.lt_floor_add_one L
  have hMint : (d : ℝ) * Real.log (n : ℝ) ≤ M := by linarith
  have hRs : 8 * (R / 8) = R := Nat.mul_div_cancel' hdiv
  have hs : 0 < R / 8 := by omega
  have hr0 : 0 < initialRadius R := by
    have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < R))
    exact_mod_cast (lt_of_lt_of_le (sq_pos_of_pos hlog)
      (Nat.le_ceil ((Real.log (R : ℝ)) ^ 2)))
  have ht := htail R hR (R / 8) (Nat.div_le_self _ _)
  have hbound := smallClusters_probability_strong σ K ρ n (R / 8) M hn4 hs
    (by simpa only [hRs] using hr0) (by simpa only [hRs] using ht) hMint
  have hsub : {h : LatticeGeometry.Point d → ℝ | BlockCovering.SmallClusters
      (goodLabel K ρ R (initialRadius R) (R / 8) h) n (R / 8) M} ⊆
      {h : LatticeGeometry.Point d → ℝ | SmallClustersReal (goodLabel K ρ R (initialRadius R) (R / 8) h) n R L} := by
    intro h hh k hk
    have hc : BlockCovering.center (R / 8) k = coarseCenter R k := by
      funext j
      simp only [BlockCovering.center, coarseCenter, hRs]
      ring
    have hki : BlockCovering.Near (n + 8 * (R / 8))
        (BlockCovering.center (R / 8) k) 0 := by simpa only [hc, hRs] using hk
    obtain ⟨hfin, hcard⟩ := hh k hki
    refine ⟨hfin, (show ((BlockCovering.clusterSet
      (goodLabel K ρ R (initialRadius R) (R / 8) h) k).ncard : ℝ) ≤ M by
        exact_mod_cast hcard).trans hML⟩
  calc
    1 - Real.exp (-L) ≤ 1 - Real.exp (-(M : ℝ) - 3) := by
      have he := Real.exp_le_exp.mpr (show -(M : ℝ) - 3 ≤ -L by linarith)
      linarith
    _ ≤ (RFIM.environmentLaw d σ).real {h | BlockCovering.SmallClusters
        (goodLabel K ρ R (initialRadius R) (R / 8) h) n (R / 8) M} := by
      simpa only [hRs] using hbound
    _ ≤ _ := measureReal_mono hsub

/-- At every sufficiently large scale, all infinite bad clusters are
excluded almost surely, under the actual disorder construction. -/
theorem infinite_bad_clusters_null {d : ℕ} (hd : 0 < d) (σ K ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρsmall : ρ < 1 / (40 * (d : ℝ)))
    (hweak : (Gaussian.law σ).real {x | |x| ≤ K} < 1 / (40 * (d : ℝ))) :
    ∃ R0 : ℕ, 4 ≤ R0 ∧ ∀ R : ℕ, R0 ≤ R → ∀ s : ℕ, s ≤ R →
      RFIM.environmentLaw d σ {h | ∃ z : LatticeGeometry.Point d,
        (BlockCovering.clusterSet (goodLabel K ρ R (initialRadius R) s h) z).Infinite} = 0 := by
  have hp := (markParameter_strong_bound hd σ K ρ hρ hρsmall hweak).le
  obtain ⟨R0, hR04, htail⟩ := eventually_coarse_cluster_tail hd σ K ρ hp
  refine ⟨R0, hR04, ?_⟩
  intro R hR s hs
  let good := fun h : LatticeGeometry.Point d → ℝ => goodLabel K ρ R (initialRadius R) s h
  have hroot (z : LatticeGeometry.Point d) :
      RFIM.environmentLaw d σ {h | (BlockCovering.clusterSet (good h) z).Infinite} = 0 := by
    let E : Set (LatticeGeometry.Point d → ℝ) :=
      {h | (BlockCovering.clusterSet (good h) z).Infinite}
    have hEbound : ∀ᶠ r : ℕ in atTop,
        (RFIM.environmentLaw d σ).real E ≤ (Real.exp (-3)) ^ r := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with r hr
      have hsub : E ⊆ {h | clusterAtLeast (starGraph d) (fun v => ¬good h v) z r} := by
        intro h hh
        change (BlockCovering.clusterSet (good h) z).Infinite at hh
        have hinf : (cluster (starGraph d) (fun v => ¬good h v) z).Infinite := by
          simpa only [block_clusterSet_eq] using hh
        obtain ⟨S, hsub, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf r
        exact ⟨S, hcard, hsub⟩
      apply (measureReal_mono hsub).trans
      have h := htail R hR s hs z r (by omega)
      have heq : Real.exp (-3 * (r : ℝ)) = (Real.exp (-3)) ^ r := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      simpa only [heq] using h
    have hlim : Tendsto (fun r : ℕ => (Real.exp (-3)) ^ r) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_nonneg _)
        (Real.exp_lt_one_iff.mpr (by norm_num))
    have hreal : (RFIM.environmentLaw d σ).real E = 0 :=
      le_antisymm (ge_of_tendsto hlim hEbound) ENNReal.toReal_nonneg
    rcases (ENNReal.toReal_eq_zero_iff _).mp hreal with hzero | hinf
    · exact hzero
    · exact (measure_ne_top (RFIM.environmentLaw d σ) E hinf).elim
  have hset : {h | ∃ z : LatticeGeometry.Point d,
      (BlockCovering.clusterSet (good h) z).Infinite} =
      ⋃ z : LatticeGeometry.Point d, {h | (BlockCovering.clusterSet (good h) z).Infinite} := by
    ext h
    simp
  rw [hset]
  exact measure_iUnion_null hroot

/-- The event in the real-threshold version of Lemma 3.2 is measurable. -/
theorem measurableSet_smallClustersReal {d : ℕ} (K ρ : ℝ) (R r0 s n : ℕ)
    (L : ℝ) (hr0 : 0 < r0) (hL : 0 ≤ L) :
    MeasurableSet {h : LatticeGeometry.Point d → ℝ |
      SmallClustersReal (goodLabel K ρ R r0 s h) n R L} := by
  have heq : {h : LatticeGeometry.Point d → ℝ |
      SmallClustersReal (goodLabel K ρ R r0 s h) n R L} =
      ⋂ k : LatticeGeometry.Point d,
        {h | BlockCovering.Near (n + R) (coarseCenter R k) 0 →
          ¬clusterAtLeast (starGraph d) (fun v => ¬goodLabel K ρ R r0 s h v)
            k (Nat.floor L + 1)} := by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_iInter, SmallClustersReal]
    apply forall_congr'
    intro k
    apply imp_congr_right
    intro hk
    rw [not_clusterAtLeast_iff, ← block_clusterSet_eq]
    exact (and_congr_right (fun _ => (Nat.le_floor_iff hL).symm))
  rw [heq]
  apply MeasurableSet.iInter
  intro k
  by_cases hk : BlockCovering.Near (n + R) (coarseCenter R k) 0
  · simp only [hk, true_implies]
    exact (measurableSet_clusterAtLeast (starGraph d)
      (fun h v => ¬goodLabel K ρ R r0 s h v)
      (fun v => (measurableSet_goodLabel K ρ R r0 s v hr0).compl)
      k (Nat.floor L + 1) (by omega)).compl
  · simp only [hk, false_implies, Set.setOf_true]
    exact MeasurableSet.univ

theorem initialRadius_pos (R : ℕ) (hR : 2 ≤ R) : 0 < initialRadius R := by
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < R))
  exact_mod_cast (lt_of_lt_of_le (sq_pos_of_pos hlog)
    (Nat.le_ceil ((Real.log (R : ℝ)) ^ 2)))

/-- The radius window stipulated in the paper is nonempty at every
sufficiently large scale. -/
theorem eventually_initialRadius_le_eighth :
    ∀ᶠ R : ℕ in atTop, initialRadius R ≤ R / 8 := by
  have hcast : Tendsto (fun R : ℕ => (R : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun R : ℕ => (Real.log (R : ℝ)) ^ 2 / R) atTop (𝓝 0) := by
    simpa only [one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp hcast
  have hinv : Tendsto (fun R : ℕ => (1 : ℝ) / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcast
  have hsum := hlog.add hinv
  simp only [add_zero] at hsum
  have hevent := hsum.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  filter_upwards [hevent, eventually_ge_atTop (1 : ℕ)] with R hsmall hR
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hceil : (initialRadius R : ℝ) < (Real.log (R : ℝ)) ^ 2 + 1 :=
    Nat.ceil_lt_add_one (sq_nonneg _)
  rw [← add_div] at hsmall
  have hm := (div_lt_iff₀ hR0).mp hsmall
  have hnat : initialRadius R * 8 ≤ R := by
    exact_mod_cast (show (initialRadius R : ℝ) * 8 ≤ R by linarith)
  exact (Nat.le_div_iff_mul_le (by norm_num)).mpr hnat

/-- Measurability of the exact integer bad-cluster event consumed by the
block-covering and upper-bound theorems. -/
theorem measurableSet_smallClusters {d : ℕ} (K ρ : ℝ) (R r0 s n L : ℕ)
    (hr0 : 0 < r0) :
    MeasurableSet {h : LatticeGeometry.Point d → ℝ |
      BlockCovering.SmallClusters (goodLabel K ρ R r0 s h) n s L} := by
  have heq : {h : LatticeGeometry.Point d → ℝ |
      BlockCovering.SmallClusters (goodLabel K ρ R r0 s h) n s L} =
      ⋂ k : LatticeGeometry.Point d,
        {h | BlockCovering.Near (n + 8 * s) (BlockCovering.center s k) 0 →
          ¬clusterAtLeast (starGraph d) (fun v => ¬goodLabel K ρ R r0 s h v) k (L + 1)} := by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_iInter, BlockCovering.SmallClusters]
    apply forall_congr'
    intro k
    apply imp_congr_right
    intro hk
    rw [not_clusterAtLeast_iff, ← block_clusterSet_eq]
  rw [heq]
  apply MeasurableSet.iInter
  intro k
  by_cases hk : BlockCovering.Near (n + 8 * s) (BlockCovering.center s k) 0
  · simp only [hk, true_implies]
    exact (measurableSet_clusterAtLeast (starGraph d)
      (fun h v => ¬goodLabel K ρ R r0 s h v)
      (fun v => (measurableSet_goodLabel K ρ R r0 s v hr0).compl)
      k (L + 1) (by omega)).compl
  · simp only [hk, false_implies, Set.setOf_true]
    exact MeasurableSet.univ

/-- The complement probability form of the actual Lemma 3.2 event, ready
for the upper-bound failure union. No cluster-tail certificate is a premise. -/
theorem lemma_3_2_failure {d : ℕ} (hd : 0 < d) (σ K ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρsmall : ρ < 1 / (40 * (d : ℝ)))
    (hweak : (Gaussian.law σ).real {x | |x| ≤ K} < 1 / (40 * (d : ℝ))) :
    ∃ R0 : ℕ, ∃ κ : ℝ, 0 < κ ∧ ∀ R n L : ℕ,
      R0 ≤ R → R ≤ n → 8 ∣ R → κ * Real.log (n : ℝ) ≤ L →
        (RFIM.environmentLaw d σ).real {h | ¬BlockCovering.SmallClusters
          (goodLabel K ρ R (initialRadius R) (R / 8) h) n (R / 8) L} ≤
            Real.exp (-(L : ℝ)) := by
  obtain ⟨R0, κ, hκ, hgood⟩ := lemma_3_2 hd σ K ρ hρ hρsmall hweak
  refine ⟨max 4 R0, κ, hκ, ?_⟩
  intro R n L hR hRn hdiv hL
  have hR0 : R0 ≤ R := (le_max_right _ _).trans hR
  have hR4 : 4 ≤ R := (le_max_left _ _).trans hR
  have hprob := hgood R n L hR0 hRn hdiv hL
  have hmeas := measurableSet_smallClusters (d := d) K ρ R (initialRadius R) (R / 8) n L
    (initialRadius_pos R (by omega))
  have hcompl := measureReal_compl (μ := RFIM.environmentLaw d σ) hmeas
  simp only [measureReal_univ_eq_one] at hcompl
  have heq : {h : LatticeGeometry.Point d → ℝ | ¬BlockCovering.SmallClusters
      (goodLabel K ρ R (initialRadius R) (R / 8) h) n (R / 8) L} =
      {h : LatticeGeometry.Point d → ℝ | BlockCovering.SmallClusters
        (goodLabel K ρ R (initialRadius R) (R / 8) h) n (R / 8) L}ᶜ := rfl
  rw [heq, hcompl]
  linarith

end Paper09.Percolation
