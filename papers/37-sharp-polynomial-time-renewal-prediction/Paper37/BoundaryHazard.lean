import Paper37.RiskBounds

/-!
# The ordinary-hazard substitution at the stationary boundary

The two-point gap laws below belong to the genuine finite-mean renewal class.
Their all-zero histories keep probability tending to one while their substituted
hazards remain fixed. This is the mechanism behind Proposition A.1.
-/
noncomputable section
open scoped ENNReal
open MeasureTheory

namespace Paper37.Boundary
open Paper37.Renewal

/-- A finite two-point distribution on actual gap indices `a` and `b`. -/
def mixedLaw (a b : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) : Law where
  mass d := (if d = a then 1 - δ else 0) + (if d = b then δ else 0)
  nonneg d := by split_ifs <;> linarith
  total := by simpa using (hasSum_ite_eq a (1 - δ)).add (hasSum_ite_eq b δ)
  finiteMean := by
    have heq : (fun d : ℕ => ((d : ℝ) + 1) *
        ((if d = a then 1 - δ else 0) + (if d = b then δ else 0))) =
        (fun d : ℕ => (if d = a then ((a : ℝ) + 1) * (1 - δ) else 0) +
          (if d = b then ((b : ℝ) + 1) * δ else 0)) := by
      funext d
      by_cases ha : d = a <;> by_cases hb : d = b <;> simp_all <;> ring
    rw [heq]
    exact (hasSum_ite_eq a (((a : ℝ) + 1) * (1 - δ))).summable.add
      (hasSum_ite_eq b (((b : ℝ) + 1) * δ)).summable

 theorem mixedLaw_tsum (a b : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (f : ℕ → ℝ) :
    (∑' d, f d * (mixedLaw a b δ hδ0 hδ1).mass d) = f a * (1 - δ) + f b * δ := by
  have heq : (fun d : ℕ => f d * (mixedLaw a b δ hδ0 hδ1).mass d) =
      (fun d : ℕ => (if d = a then f a * (1 - δ) else 0) +
        (if d = b then f b * δ else 0)) := by
    funext d
    by_cases ha : d = a <;> by_cases hb : d = b <;> simp_all [mixedLaw] <;> ring
  rw [heq, Summable.tsum_add (hasSum_ite_eq a (f a * (1 - δ))).summable
    (hasSum_ite_eq b (f b * δ)).summable]
  simp

 theorem mixedLaw_mean (a b : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    mean (mixedLaw a b δ hδ0 hδ1) = ((a : ℝ) + 1) * (1 - δ) + ((b : ℝ) + 1) * δ :=
  mixedLaw_tsum a b δ hδ0 hδ1 (fun d => (d : ℝ) + 1)

 theorem mixedLaw_residual (a b n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    residual (mixedLaw a b δ hδ0 hδ1) n =
      ((a + 1 - n : ℕ) : ℝ) * (1 - δ) + ((b + 1 - n : ℕ) : ℝ) * δ :=
  mixedLaw_tsum a b δ hδ0 hδ1 (fun d => ((d + 1 - n : ℕ) : ℝ))

 theorem mixedLaw_tail (a b n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    tail (mixedLaw a b δ hδ0 hδ1) n =
      (if n ≤ a then 1 - δ else 0) + (if n ≤ b then δ else 0) := by
  calc
    tail (mixedLaw a b δ hδ0 hδ1) n =
        ∑' d, (if n ≤ d then (1 : ℝ) else 0) * (mixedLaw a b δ hδ0 hδ1).mass d := by
      apply tsum_congr
      intro d
      split_ifs <;> simp
    _ = _ := by
      rw [mixedLaw_tsum]
      split_ifs <;> ring

 theorem ageFrom_zeros (a n : ℕ) : ageFrom a (List.replicate n false) = a + n := by
  induction n generalizing a with
  | zero => simp [ageFrom]
  | succ n ih => simpa [ageFrom, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (a + 1)

 theorem mixedLaw_substituted_target (n m : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    Paper37.Prediction.substitutedTarget (mixedLaw n (n + m + 1) δ hδ0 hδ1)
      (List.replicate n false) = 1 - δ := by
  unfold Paper37.Prediction.substitutedTarget
  rw [ageFrom_zeros]
  simp only [zero_add, mixedLaw_tail, le_refl, if_true, show n ≤ n + m + 1 by omega]
  have hne : n ≠ n + m + 1 := by omega
  simp [mixedLaw, hne]

/-- The precise all-zero event probability for the Appendix A hard family. -/
theorem mixedLaw_zero_mass (n m : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    blockMass (mixedLaw n (n + m + 1) δ hδ0 hδ1) (List.replicate n false) =
      (1 + δ * ((m : ℝ) + 1)) / (1 + δ * ((m : ℝ) + 1) + n) := by
  rw [blockMass_zeros, mixedLaw_residual, mixedLaw_mean]
  have hsub : n + m + 1 + 1 - n = m + 2 := by omega
  simp only [Nat.add_sub_cancel_left, hsub, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat]
  congr 1 <;> ring

/-- At every fixed positive mixture weight, the equilibrium all-zero
probability tends to one as the long gap tends to infinity. -/
theorem mixedLaw_zero_mass_tendsto (n : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Filter.Tendsto
      (fun m : ℕ => blockMass (mixedLaw n (n + m + 1) δ hδ0.le hδ1) (List.replicate n false))
      Filter.atTop (nhds 1) := by
  have hi := tendsto_one_div_add_atTop_nhds_zero_nat
  have hnum : Filter.Tendsto (fun m : ℕ => δ + 1 / ((m : ℝ) + 1)) Filter.atTop (nhds δ) := by
    simpa using tendsto_const_nhds.add hi
  have hden : Filter.Tendsto (fun m : ℕ => δ + ((n : ℝ) + 1) * (1 / ((m : ℝ) + 1)))
      Filter.atTop (nhds δ) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hi)
  have hdiv := hnum.div hden (ne_of_gt hδ0)
  have heq : (fun m : ℕ => blockMass (mixedLaw n (n + m + 1) δ hδ0.le hδ1) (List.replicate n false)) =
      (fun m : ℕ => (δ + 1 / ((m : ℝ) + 1)) /
        (δ + ((n : ℝ) + 1) * (1 / ((m : ℝ) + 1)))) := by
    funext m
    rw [mixedLaw_zero_mass]
    have hm : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    <;> ring
  rw [heq]
  simpa [div_self (ne_of_gt hδ0)] using hdiv

end Paper37.Boundary

namespace Paper37.Boundary

/-- The complementary deterministic-period sequence approaches the second
Bernoulli endpoint, with the same extended-value lower semicontinuity. -/
theorem kl_one_le_liminf_complement (q : ℝ) :
    kl 1 q ≤ Filter.liminf (fun k : ℕ => kl (1 - 1 / ((k : ℝ) + 1)) q) Filter.atTop := by
  by_cases h1 : q = 1
  · subst q; simp
  by_cases h0 : q = 0
  · subst q
    have hevent : ∀ᶠ k : ℕ in Filter.atTop, kl (1 - 1 / ((k : ℝ) + 1)) 0 = ∞ := by
      filter_upwards [Filter.eventually_ge_atTop 1] with k hk
      apply kl_right_zero
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
      have hlt : 1 / ((k : ℝ) + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
      exact ne_of_gt (by linarith)
    have hlim : Filter.Tendsto (fun k : ℕ => kl (1 - 1 / ((k : ℝ) + 1)) 0)
        Filter.atTop (nhds ∞) := tendsto_const_nhds.congr' (hevent.mono fun _ h => h.symm)
    rw [hlim.liminf_eq]
    exact le_top
  have hp : Filter.Tendsto (fun k : ℕ => 1 - 1 / ((k : ℝ) + 1)) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Filter.Tendsto (fun k : ℕ => kl (1 - 1 / ((k : ℝ) + 1)) q)
      Filter.atTop (nhds (kl 1 q)) := (continuous_kl_left h0 h1).continuousAt.tendsto.comp hp
  rw [hlim.liminf_eq]

end Paper37.Boundary

namespace Paper37.Prediction
open Paper37.Renewal

/-- A single all-zero history contributes its actual stationary probability
times its private-randomization expected loss. -/
theorem substituted_zero_contribution_le (n : ℕ) (q : RandomizedPredictor) (μ : Law) :
    ENNReal.ofReal (blockMass μ (List.replicate n false)) *
      (∫⁻ r : Set.Icc (0 : ℝ) 1, Boundary.kl
        (substitutedTarget μ (List.replicate n false)) r.val ∂(q (List.replicate n false)).toMeasure) ≤
      substitutedRisk n q μ := by
  unfold substitutedRisk
  refine Finset.single_le_sum (s := (words n).toFinset)
    (f := fun x : List Bool => ENNReal.ofReal (blockMass μ x) *
      ∫⁻ r : Set.Icc (0 : ℝ) 1, Boundary.kl (substitutedTarget μ x) r.val ∂(q x).toMeasure)
    (a := List.replicate n false) (fun x hx => zero_le _) ?_
  exact (List.mem_toFinset).mpr ((mem_words n (List.replicate n false)).mpr (by simp))

/-- Each fixed substituted hazard `1-δ`, for `δ>0`, is seen on histories of
stationary probability tending to one. This step takes the long-gap limit
inside no integral and makes no integrability assumption. -/
theorem substituted_sup_ge_target (n : ℕ) (q : RandomizedPredictor)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (∫⁻ r : Set.Icc (0 : ℝ) 1, Boundary.kl (1 - δ) r.val ∂(q (List.replicate n false)).toMeasure) ≤
      ⨆ μ : Law, substitutedRisk n q μ := by
  let L := ∫⁻ r : Set.Icc (0 : ℝ) 1, Boundary.kl (1 - δ) r.val ∂(q (List.replicate n false)).toMeasure
  have hw : Filter.Tendsto (fun m : ℕ => ENNReal.ofReal
      (blockMass (Boundary.mixedLaw n (n + m + 1) δ hδ0.le hδ1) (List.replicate n false)))
      Filter.atTop (nhds 1) := by
    simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (Boundary.mixedLaw_zero_mass_tendsto n δ hδ0 hδ1)
  have hmul := ENNReal.Tendsto.mul_const (b := L) hw (Or.inl one_ne_zero)
  have hb : ∀ m : ℕ, ENNReal.ofReal
      (blockMass (Boundary.mixedLaw n (n + m + 1) δ hδ0.le hδ1) (List.replicate n false)) * L ≤
        ⨆ μ : Law, substitutedRisk n q μ := by
    intro m
    have h := substituted_zero_contribution_le n q (Boundary.mixedLaw n (n + m + 1) δ hδ0.le hδ1)
    rw [Boundary.mixedLaw_substituted_target] at h
    exact h.trans (le_iSup (fun μ : Law => substitutedRisk n q μ) _)
  simpa only [one_mul] using le_of_tendsto' hmul hb

/-- Proposition A.1 lower bound for arbitrary privately randomized kernels. -/
theorem substituted_sup_ge_log_two (n : ℕ) (q : RandomizedPredictor) :
    ENNReal.ofReal (Real.log 2) ≤ ⨆ μ : Law, substitutedRisk n q μ := by
  have hzero : (∫⁻ r : Set.Icc (0 : ℝ) 1, Boundary.kl 0 r.val
      ∂(q (List.replicate n false)).toMeasure) ≤ ⨆ μ : Law, substitutedRisk n q μ := by
    simpa using substituted_sup_ge_target n q 1 zero_lt_one le_rfl
  have hone : (∫⁻ r : Set.Icc (0 : ℝ) 1, Boundary.kl 1 r.val
      ∂(q (List.replicate n false)).toMeasure) ≤ ⨆ μ : Law, substitutedRisk n q μ := by
    calc
      _ ≤ ∫⁻ r : Set.Icc (0 : ℝ) 1,
          Filter.liminf (fun k : ℕ => Boundary.kl (1 - 1 / ((k : ℝ) + 1)) r.val) Filter.atTop
          ∂(q (List.replicate n false)).toMeasure :=
        lintegral_mono fun r => Boundary.kl_one_le_liminf_complement r.val
      _ ≤ Filter.liminf (fun k : ℕ => ∫⁻ r : Set.Icc (0 : ℝ) 1,
          Boundary.kl (1 - 1 / ((k : ℝ) + 1)) r.val ∂(q (List.replicate n false)).toMeasure) Filter.atTop :=
        lintegral_liminf_le fun k => (Boundary.measurable_kl_right _).comp measurable_subtype_coe
      _ ≤ _ := by
        rw [Filter.liminf_eq_iSup_iInf_of_nat]
        apply iSup_le
        intro k
        refine (iInf₂_le k le_rfl).trans ?_
        apply substituted_sup_ge_target
        · positivity
        · apply (div_le_one (by positivity : (0 : ℝ) < (k : ℝ) + 1)).mpr
          have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          linarith
  exact (Boundary.randomized_endpoint_radius (q (List.replicate n false)).toMeasure
    (fun r : Set.Icc (0 : ℝ) 1 => r.val) measurable_subtype_coe (fun r => r.property)).trans
      (max_le hzero hone)

/-- Proposition A.1 lower minimax inequality, with all source quantifiers. -/
theorem substitutedMinimaxRisk_ge_log_two (n : ℕ) :
    ENNReal.ofReal (Real.log 2) ≤ substitutedMinimaxRisk n := by
  exact le_iInf fun q => substituted_sup_ge_log_two n q

end Paper37.Prediction

namespace Paper37.Prediction

/-- Proposition A.1: the integrated minimax value for the auxiliary ordinary
hazard substitution is exactly log 2, including arbitrary private randomization. -/
theorem substitutedMinimaxRisk_eq_log_two (n : ℕ) :
    substitutedMinimaxRisk n = ENNReal.ofReal (Real.log 2) :=
  le_antisymm (substitutedMinimaxRisk_le_log_two n) (substitutedMinimaxRisk_ge_log_two n)

end Paper37.Prediction
