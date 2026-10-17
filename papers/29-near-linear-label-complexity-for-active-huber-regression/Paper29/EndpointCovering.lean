import Paper29.ExternalCovering
import Paper29.ScaleBookkeeping

noncomputable section
open scoped BigOperators Classical ENNReal
namespace Paper29.Chaining
open WeightConstruction ExternalCovering ProcessTools

/-- The exact endpoint scheme has the actual weighted leverage at every scale. -/
def endpointWeights {n : ℕ} (w : PositiveWeights n) (p : ℕ) (j : ℤ) : PositiveWeights n :=
  rescale (Leverage.endpointFactor p j) (Leverage.endpointFactor_pos p j) w

theorem endpointWeights_leverage {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (hA : A.rank = d) (w : PositiveWeights n) (p : ℕ) (j : ℤ) (i : Fin n) :
    Leverage.leverage A (endpointWeights w p j) i = Leverage.leverage A w i :=
  Leverage.endpoint_leverage A w (Leverage.mulVec_injective_of_rank_eq A hA) w.property p j i

theorem endpointWeights_normalized {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (hA : A.rank = d) (w : PositiveWeights n) (p : ℕ) (hp : 0 < p)
    (hbase : ∀ i, (Leverage.radius A w i)^(p:ℝ) / Leverage.leverage A w i = 1)
    (j : ℤ) (i : Fin n) :
    |Leverage.radius A (endpointWeights w p j) i|^p /
      Leverage.leverage A (endpointWeights w p j) i = (2:ℝ)^j := by
  have h := Leverage.endpoint_power_identity A w
    (Leverage.mulVec_injective_of_rank_eq A hA) w.property p j (by exact_mod_cast hp) i (hbase i)
  have hr : 0 ≤ Leverage.radius A (endpointWeights w p j) i := Real.sqrt_nonneg _
  rw [abs_of_nonneg hr, ← Real.rpow_natCast, ← Real.rpow_intCast]
  exact h

theorem maxScore_endpoint {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (hA : A.rank = d) (w : PositiveWeights n) (p : ℕ) (s : Finset ℤ) (hs : s.Nonempty) :
    maxScore A s (endpointWeights w p) = Leverage.leverage A w := by
  haveI : Nonempty {j : ℤ // j ∈ s} := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  funext i
  apply le_antisymm
  · apply supremum_le
    intro j
    exact (endpointWeights_leverage A hA w p j i).le
  · obtain ⟨j, hj⟩ := hs
    have hh := le_supremum (fun j : {j : ℤ // j ∈ s} =>
      Leverage.leverage A (endpointWeights w p j) i) ((Set.finite_range _).bddAbove) ⟨j, hj⟩
    change Leverage.leverage A w i ≤ _
    rw [endpointWeights_leverage A hA w p j i] at hh
    exact hh

/-- Lemma3.3 from only its imported power cover: exact scheme algebra, leverage
mass, every-radius restriction and dyadic constants are proved locally. -/
theorem endpoint_cover_all_radii {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (hn : 1 ≤ n) (hA : A.rank = d) (hrows : ∀ i, A i ≠ 0)
    (w : PositiveWeights n) (p : ℕ) (hp : p = 1 ∨ p = 2)
    (hbase : ∀ i, (Leverage.radius A w i)^(p:ℝ) / Leverage.leverage A w i = 1)
    (C : ℝ) (hC : 0 ≤ C) (external : PowerPrimitive C) :
    (∑ i, Leverage.leverage A w i) = (d:ℝ) ∧
      EndpointCover A p (Leverage.leverage A w) (2*C*ProcessTools.logFactor n) := by
  refine ⟨Leverage.leverage_sum_of_rank_eq A w hA w.property, ?_⟩
  intro S hS
  let k : ℤ := ⌈Real.logb 2 S⌉
  let L : ℕ := transitionLength n
  let a : ℤ := k - L
  let b : ℤ := k - 1
  have hp0 : 0 < p := by rcases hp with rfl | rfl <;> norm_num
  have hab : a ≤ b := by have hh := transitionLength_pos n; dsimp [a,b,L]; omega
  have hs : (Finset.Icc a b).Nonempty := Finset.nonempty_Icc.mpr hab
  have hcard : 4*Real.log (2*(n:ℝ)) ≤ ((Finset.Icc a b).card : ℝ) := by
    change _ ≤ ((radiusBlock n S).card : ℝ)
    rw [radiusBlock_card]
    exact transitionLength_large n
  have raw := external n d p hp A hA hrows a b hab hcard (endpointWeights w p)
    (fun j _ i => endpointWeights_normalized A hA w p hp0 hbase j i)
    (by
      intro j _ _ i
      change Leverage.endpointFactor p ((j+1:ℤ):ℝ) * w i ≤
        Leverage.endpointFactor p (j:ℝ) * w i
      simpa only [Int.cast_add, Int.cast_one] using
        Leverage.endpoint_weight_step_le w (fun i => (w.property i).le)
          p j (by exact_mod_cast hp0) i)
  rw [maxScore_endpoint A hA w p _ hs] at raw
  have hbk : b+1 = k := by dsimp [b]; omega
  rw [hbk] at raw
  let f : PowerBall A p S → PowerBall A p ((2:ℝ)^k) :=
    fun h => ⟨h, h.property.trans (dyadic_ceiling hS).1⟩
  have hmono := gamma2_pullback f (fun x y => powerMetric A p (Leverage.leverage A w) x y)
    (fun x y => powerMetric A p (Leverage.leverage A w) x y) (fun _ _ => le_rfl)
  apply (hmono.trans raw).trans
  apply ENNReal.ofReal_le_ofReal
  have hroot : Real.sqrt ((2:ℝ)^k) ≤ 2*Real.sqrt S := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1
    rw [Real.sq_sqrt (zpow_pos (by norm_num) k).le, mul_pow, Real.sq_sqrt hS.le]
    have hh := (dyadic_ceiling hS).2
    change (2:ℝ)^k < 2*S at hh
    nlinarith
  have hlog : 0 ≤ ProcessTools.logFactor n := (ProcessTools.logFactor_pos hn).le
  nlinarith [mul_le_mul_of_nonneg_left hroot (mul_nonneg hC hlog)]

end Paper29.Chaining
