import Paper08.LowerBoundLip
import Paper08.LowerBoundMass
import Paper08.LowerBoundOracle

/-! # The actual deterministic adaptive exact-value lower bound of Proposition B.1

An instance has `m` disjoint blocks of `r` real coordinates. Its partition
function is the Bochner integral of the product against the product of the
restricted Lebesgue measures. The adversary below is constructed explicitly
from the finite transcript. Its regularity, range, Euclidean Lipschitz bound,
and integral mass are all proved for that concrete function.
-/
noncomputable section
open scoped Real BigOperators ENNReal
open MeasureTheory Set
namespace Paper08.LowerBound

abbrev BlockFactors (m r : ℕ) := Fin m → (Fin r → ℝ) → ℝ
abbrev BlockQuery (m r : ℕ) := Fin m × (Fin r → ℝ)

def blockOracle {m r : ℕ} (ψ : BlockFactors m r) (q : BlockQuery m r) : ℝ := ψ q.1 q.2

/-- The actual integral on pairwise disjoint coordinate blocks. -/
def blockPartition {m r : ℕ} (ψ : BlockFactors m r) : ℝ :=
  ∫ x : Fin m → (Fin r → ℝ), ∏ e, ψ e (x e)
    ∂Measure.pi (fun _ : Fin m => (volume : Measure (Fin r → ℝ)).restrict (Integral.cube r))

lemma blockPartition_eq_prod {m r : ℕ} (ψ : BlockFactors m r) :
    blockPartition ψ = ∏ e, Integral.cubeIntegral (ψ e) :=
  integral_fintype_prod_eq_prod ψ

lemma blockPartition_one (m r : ℕ) :
    blockPartition (fun _ : Fin m => fun _ : Fin r → ℝ => (1 : ℝ)) = 1 := by
  rw [blockPartition_eq_prod]
  simp

/-- The paper's range, Euclidean Lipschitz, and `C¹` promises on every factor. -/
def BlockPromises {m r : ℕ} (K U : ℝ) (ψ : BlockFactors m r) : Prop :=
  ∀ e, ContDiff ℝ 1 (ψ e) ∧
    (∀ x ∈ Integral.cube r, 1 ≤ ψ e x ∧ ψ e x ≤ U) ∧
    (LocalFunc.mk (ψ e)).LipLe K

/-- A deterministic algorithm's ordinary universal logarithmic accuracy promise.
No premise states a lower bound, a mass estimate, or an indistinguishability certificate. -/
def BlockAccurate {m r : ℕ} (A : ValuePolicy (BlockQuery m r)) (K U ε : ℝ) : Prop :=
  ∀ ψ : BlockFactors m r, BlockPromises K U ψ →
    ∀ n z, A (valueTranscript A (blockOracle ψ) n) = .inr z →
      0 < z ∧ |Real.log (z / blockPartition ψ)| ≤ ε

/-- The distinct points queried to a given factor. -/
def factorQuerySet {m r : ℕ} (qs : Finset (BlockQuery m r)) (e : Fin m) :
    Finset (Fin r → ℝ) := by
  classical
  exact (qs.filter fun q => q.1 = e).image Prod.snd

lemma factorQuerySet_mem {m r : ℕ} {qs : Finset (BlockQuery m r)} {e : Fin m}
    {x : Fin r → ℝ} : x ∈ factorQuerySet qs e ↔ (e, x) ∈ qs := by
  classical
  simp only [factorQuerySet, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨f, y⟩, ⟨hmem, hfe⟩, hxy⟩
    change f = e at hfe
    change y = x at hxy
    subst f
    subst y
    exact hmem
  · intro h
    exact ⟨(e, x), ⟨h, rfl⟩, rfl⟩

lemma sum_factorQuerySet_card {m r : ℕ} (qs : Finset (BlockQuery m r)) :
    (∑ e, (factorQuerySet qs e).card) = qs.card := by
  classical
  have hc (e : Fin m) : (factorQuerySet qs e).card = (qs.filter fun q => q.1 = e).card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    exact Prod.ext (hx'.trans hy'.symm) hxy
  simp_rw [hc]
  exact (Finset.card_eq_sum_card_fiberwise (s := qs) (t := Finset.univ)
    (f := Prod.fst) (fun _ _ => Finset.mem_univ _)).symm

/-- Using `N+1` in the grid size treats the zero-query case uniformly. -/
def foolingGridSize (r N : ℕ) : ℕ := ⌈(↑(2 * (N + 1)) : ℝ) ^ ((1 : ℝ) / r)⌉₊

lemma foolingGridSize_pos (r N : ℕ) : 0 < foolingGridSize r N := by
  have hp : 0 < (↑(2 * (N + 1)) : ℝ) ^ ((1 : ℝ) / r) := Real.rpow_pos_of_pos (by positivity) _
  have hh := Nat.le_ceil ((↑(2 * (N + 1)) : ℝ) ^ ((1 : ℝ) / r))
  have : 0 < (foolingGridSize r N : ℝ) := hp.trans_le hh
  exact_mod_cast this

lemma foolingGridSize_count {r N : ℕ} (hr : 1 ≤ r) :
    2 * N ≤ foolingGridSize r N ^ r := by
  have h := ceil_rpow_pow_ge (N + 1) r hr
  have hn : 2 * (N + 1) ≤ foolingGridSize r N ^ r := by
    exact_mod_cast h
  omega

/-- The concrete alternative factor family generated from a finite query set. -/
def alternativeFactors {m r : ℕ} (K U : ℝ) (qs : Finset (BlockQuery m r)) : BlockFactors m r :=
  fun e x => 1 + foolingBump (L := foolingGridSize r (factorQuerySet qs e).card)
    (a0 r K U) (factorQuerySet qs e) x

lemma alternativeFactors_at_query {m r : ℕ} (K U : ℝ)
    (qs : Finset (BlockQuery m r)) {q : BlockQuery m r} (hq : q ∈ qs) :
    blockOracle (alternativeFactors K U qs) q = 1 := by
  unfold blockOracle alternativeFactors
  rw [foolingBump_at_query _ _ (factorQuerySet_mem.mpr hq), add_zero]

lemma alternativeFactors_promises {m r : ℕ} {K U : ℝ}
    (hr : 1 ≤ r) (hK : 0 < K) (hU : 1 < U) (qs : Finset (BlockQuery m r)) :
    BlockPromises K U (alternativeFactors K U qs) := by
  have ha := (a0_pos hr hK hU).le
  have hs : 0 < 8 * Real.sqrt (r : ℝ) := by positivity
  have hLip : 8 * a0 r K U * Real.sqrt r ≤ K := by
    have hh := (le_div_iff₀ hs).mp (a0_le_K_div r K U)
    nlinarith
  intro e
  refine ⟨contDiff_const.add (contDiff_foolingBump _ _), ?_, ?_⟩
  · intro x _
    exact foolingFactor_range ha (a0_le_U_sub_one r K U) (foolingGridSize_pos r _) _ x
  · intro x y _ _
    have hh := foolingBump_euclidean_lipschitz ha (foolingGridSize_pos r
      (factorQuerySet qs e).card) (factorQuerySet qs e) x y
    change |(1 + _) - (1 + _)| ≤ _
    rw [add_sub_add_left_eq_sub]
    exact hh.trans (mul_le_mul_of_nonneg_right hLip (norm_nonneg _))

lemma alternativeFactors_mass {m r : ℕ} {K U : ℝ}
    (hr : 1 ≤ r) (hK : 0 < K) (hU : 1 < U) (qs : Finset (BlockQuery m r)) (e : Fin m) :
    c0 r K U * (((factorQuerySet qs e).card : ℝ) + 1) ^ negInvR r ≤
      Integral.cubeIntegral (foolingBump (L := foolingGridSize r (factorQuerySet qs e).card)
        (a0 r K U) (factorQuerySet qs e)) := by
  let N := (factorQuerySet qs e).card
  have hm := cubeIntegral_foolingBump_ge (foolingGridSize_pos r N)
    (a0_pos hr hK hU).le (factorQuerySet qs e) (foolingGridSize_count hr)
  have hc := mu_bound_core hr (show 1 ≤ N + 1 by omega) (a0_pos hr hK hU) (J_pos r)
    (Nat.le_ceil _) (ceil_two_rpow_le (N + 1) r (by omega) hr)
  have hh := hc.trans hm
  simpa only [c0, Nat.cast_add, Nat.cast_one] using hh

/-- Proposition B.1, lower-bound half: every finite terminating all-one run of
an accurate deterministic adaptive exact-value algorithm uses at least (B.1).
The alternative instance in the proof is explicitly built from that run. -/
theorem prop_B1_adaptive {r m : ℕ} {K U ε : ℝ}
    (hr : 1 ≤ r) (hm : 1 ≤ m) (hK : 0 < K) (hU : 1 < U)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (A : ValuePolicy (BlockQuery m r)) (hcorrect : BlockAccurate A K U ε)
    (n : ℕ) (z : ℝ) (hhalt : A (valueTranscript A (fun _ => 1) n) = .inr z) :
    ((valueTranscript A (fun _ => 1) n).length : ℝ) ≥
      (c0 r K U / (2 * U * ε)) ^ r * (m : ℝ) ^ (r + 1) - m := by
  classical
  let qs := allOneQueries A n
  let ψ := alternativeFactors K U qs
  let N : Fin m → ℕ := fun e => (factorQuerySet qs e).card
  let μ : Fin m → ℝ := fun e => Integral.cubeIntegral
    (foolingBump (L := foolingGridSize r (N e)) (a0 r K U) (factorQuerySet qs e))
  have ha := (a0_pos hr hK hU).le
  have hInt (e : Fin m) : IntegrableOn
      (foolingBump (L := foolingGridSize r (N e)) (a0 r K U) (factorQuerySet qs e))
      (Integral.cube r) := by
    apply Integral.integrableOn_cube_of_bound (contDiff_foolingBump _ _).continuous.measurable
    intro x _
    rw [abs_of_nonneg (foolingBump_nonneg ha _ _)]
    exact foolingBump_le ha _ _
  have hμ0 (e : Fin m) : 0 ≤ μ e :=
    Integral.le_cubeIntegral (hInt e) (fun x _ => foolingBump_nonneg ha _ x)
  have hμU (e : Fin m) : μ e ≤ U - 1 := by
    apply Integral.cubeIntegral_le (hInt e)
    intro x _
    have hh := (foolingFactor_range ha (a0_le_U_sub_one r K U)
      (foolingGridSize_pos r (N e)) (factorQuerySet qs e) x).2
    linarith
  have hμmass (e : Fin m) : c0 r K U * ((N e : ℝ) + 1) ^ negInvR r ≤ μ e :=
    alternativeFactors_mass hr hK hU qs e
  have hZ : blockPartition ψ = ∏ e, (1 + μ e) := by
    rw [blockPartition_eq_prod]
    apply Finset.prod_congr rfl
    intro e _
    change Integral.cubeIntegral (fun x => 1 + _) = 1 + μ e
    rw [Integral.cubeIntegral_add (integrableOn_const (Integral.volume_cube_lt_top r).ne) (hInt e),
      Integral.cubeIntegral_const]
  have hZpos : 0 < blockPartition ψ := by
    rw [hZ]
    exact Finset.prod_pos fun e _ => by linarith [hμ0 e]
  have hbaseline : BlockPromises (m := m) (r := r) K U (fun _ _ => 1) := by
    intro e
    refine ⟨contDiff_const, fun _ _ => ⟨le_refl _, hU.le⟩, ?_⟩
    intro x y _ _
    simp only [LocalFunc.mk, sub_self, abs_zero]
    positivity
  have h₀ := hcorrect (fun _ _ => 1) hbaseline n z hhalt
  have haltψ : A (valueTranscript A (blockOracle ψ) n) = .inr z :=
    same_output_of_allOneQueries A n (blockOracle ψ)
      (fun q hq => alternativeFactors_at_query K U qs hq) hhalt
  have h₁ := hcorrect ψ (alternativeFactors_promises hr hK hU qs) n z haltψ
  have hgap := common_output_forces_log_gap h₀.1 (show 0 < blockPartition
    (fun _ : Fin m => fun _ : Fin r → ℝ => 1) by rw [blockPartition_one]; norm_num) hZpos h₀.2 h₁.2
  rw [blockPartition_one, Real.log_one, sub_zero] at hgap
  have hlog : Real.log (blockPartition ψ) ≤ 2 * ε := (le_abs_self _).trans hgap
  have hterms (e : Fin m) : (c0 r K U / U) * ((N e : ℝ) + 1) ^ negInvR r ≤
      Real.log (1 + μ e) := by
    calc
      _ = (c0 r K U * ((N e : ℝ) + 1) ^ negInvR r) / U := by ring
      _ ≤ μ e / U := div_le_div_of_nonneg_right (hμmass e) (by linarith)
      _ ≤ Real.log (1 + μ e) := log_one_add_ge_div_U (hμ0 e) hU.le (hμU e)
  have hsumlog := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hterms e)
  rw [← Finset.mul_sum, ← Real.log_prod Finset.univ (fun e => 1 + μ e)
    (fun e _ => (show 0 < 1 + μ e by linarith [hμ0 e]).ne'), ← hZ] at hsumlog
  have hcount := prop_B1 hr hm hK hU hε0 hε1 N
    (show (∑ e, (N e : ℝ)) = (qs.card : ℝ) by
      rw [← Nat.cast_sum]; exact_mod_cast sum_factorQuerySet_card qs)
    (hsumlog.trans hlog)
  have hcard : qs.card ≤ (valueTranscript A (fun _ => 1) n).length := by
    letI : DecidableEq (BlockQuery m r) := Classical.decEq _
    have hh := List.toFinset_card_le ((valueTranscript A (fun _ => 1) n).map Prod.fst)
    simpa only [qs, allOneQueries, List.length_map] using hh
  exact hcount.trans (by exact_mod_cast hcard)

end Paper08.LowerBound
