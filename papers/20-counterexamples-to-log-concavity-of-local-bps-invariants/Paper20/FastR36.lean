import Paper20.Certs.QuantumCache36
import Paper20.ScaledIntegration
import Paper20.RSeriesSemantics
import Paper20.HookBound

namespace Paper20.FastR36
open Paper20.Cert.QuantumCache36 Paper20.LogSeries
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def scaledGamma (hooks : List ℕ) (e : ℕ) : List ℤ :=
  0 :: (List.range 22).map (fun i =>
    (hooks.map (fun a => (gCached a).getD i 0)).sum+
      (e/2:ℕ)*(-1:ℤ)^(i+1)*(scale/4:ℕ)^(i+1))

theorem cached_sum (hooks : List ℕ) (i : ℕ) (hi : i < 22)
    (hp : ∀ a ∈ hooks, 1 ≤ a) (hb : ∀ a ∈ hooks, a ≤ 36) :
    ((hooks.map (fun a => (gCached a).getD i 0)).sum:ℚ) =
      (scale:ℚ)^(i+1)*(hooks.map (fun a =>
        PowerSeries.coeff i (negativeLog (Dpoly a)))).sum := by
  induction hooks with
  | nil => simp
  | cons a hooks ih =>
    simp only [List.map_cons, List.sum_cons, Int.cast_add]
    rw [negDLog_scaled a i (hp a (by simp)) (hb a (by simp)) hi,
      negDLog_correct _ (ne_of_gt (Dconst_pos a (hp a (by simp)))) 22 i hi,
      ih (fun b h => hp b (by simp [h])) (fun b h => hb b (by simp [h]))]
    ring

lemma scale_div_four : ((scale/4:ℕ):ℚ) = (scale:ℚ)/4 := by
  apply (eq_div_iff (by norm_num : (4:ℚ) ≠ 0)).2
  exact_mod_cast Nat.div_mul_cancel four_dvd_scale

lemma scaled_parity_term (m j : ℕ) :
    (((m:ℤ)*(-1:ℤ)^j*((scale/4:ℕ):ℤ)^j):ℚ) =
      (scale:ℚ)^j*((m:ℚ)*(if j%2=0 then 1 else -1)/(4^j:ℕ)) := by
  simp only [Int.cast_mul,Int.cast_pow,Int.cast_natCast,Int.cast_neg,Int.cast_one,Nat.cast_pow]
  rw [scale_div_four, neg_one_pow_eq_ite]
  simp only [Nat.even_iff]
  rw [div_pow]
  ring

theorem scaledGamma_correct (hooks : List ℕ) (e i : ℕ) (hi : i < 22)
    (hp : ∀ a ∈ hooks, 1 ≤ a) (hb : ∀ a ∈ hooks, a ≤ 36) :
    ((scaledGamma hooks e).getD (i+1) 0:ℚ) =
      (scale:ℚ)^(i+1)*PowerSeries.coeff i (logProduct hooks e) := by
  unfold scaledGamma
  rw [List.getD_cons_succ, List.getD_eq_getD_getElem?, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]
  rw [Int.cast_add, cached_sum hooks i hi hp hb, logProduct_coeff]
  have ht := scaled_parity_term (e/2) (i+1)
  simp only [Int.cast_mul,Int.cast_pow,Int.cast_natCast,Int.cast_neg,Int.cast_one,Nat.cast_pow] at ht ⊢
  linear_combination (norm := ring_nf) ht

def values (hooks : List ℕ) (e H : ℕ) : List ℤ :=
  ScaledIntegration.integrate (scaledGamma hooks e) H

/-- The integer optimized recurrence computes the same genuine R product
as the paper's actual implementation, through degree 22. -/
theorem values_coeff (hooks : List ℕ) (e H j : ℕ)
    (hp : ∀ a ∈ hooks, 1 ≤ a) (hb : ∀ a ∈ hooks, a ≤ 36)
    (hH : H ≤ 22) (hj : j ≤ H) :
    ((values hooks e H).getD j 0:ℚ) =
      (scale:ℚ)^j*(j.factorial:ℚ)*PowerSeries.coeff j (Rproduct hooks e) := by
  apply ScaledIntegration.integrate_correct _ scale (Rproduct hooks e) (logProduct hooks e)
    (Rproduct_constant hooks e hp) (Rproduct_derivative hooks e) H _ j hj
  intro i hi
  exact scaledGamma_correct hooks e i (by omega) hp hb

theorem values_eq_Rseries (hooks : List ℕ) (e H j : ℕ)
    (hp : ∀ a ∈ hooks, 1 ≤ a) (hb : ∀ a ∈ hooks, a ≤ 36)
    (hH : H ≤ 22) (hj : j ≤ H) :
    ((values hooks e H).getD j 0:ℚ)/((scale:ℚ)^j*(j.factorial:ℚ)) =
      (Rseries hooks e H).getD j 0 := by
  rw [Rseries_correct hooks e H j hp hj]
  apply (div_eq_iff (by have := scale_pos; positivity)).2
  rw [values_coeff hooks e H j hp hb hH hj]
  ring

theorem actual_partition_values {ps : List ℕ} (hp : ps ∈ partitionsOf 36)
    (H j : ℕ) (hH : H ≤ 22) (hj : j ≤ H) :
    ((values (hooksOf ps) (partsEvenHooks ps) H).getD j 0:ℚ)/
      ((scale:ℚ)^j*(j.factorial:ℚ)) =
      (Rseries (hooksOf ps) (partsEvenHooks ps) H).getD j 0 :=
  values_eq_Rseries _ _ H j (hooksOf_positive_of_mem_partitionsOf hp)
    (hooksOf_le_of_mem_partitionsOf hp) hH hj

end
end Paper20.FastR36
