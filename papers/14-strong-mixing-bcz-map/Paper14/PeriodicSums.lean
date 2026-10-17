import Paper14.SieveVariance
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology Function
namespace Paper14
noncomputable section

lemma periodic_sum_blocks {f : ℕ → ℝ} {M : ℕ} (hf : Periodic f M) (k : ℕ) :
    (∑ i ∈ Finset.range (k*M), f i) = (k : ℝ)*(∑ i ∈ Finset.range M, f i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul,Finset.sum_range_add,ih]
    have hshift : (∑ i ∈ Finset.range M, f (k*M+i)) = ∑ i ∈ Finset.range M, f i := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [Nat.add_comm] using hf.nat_mul k i
    rw [hshift,Nat.cast_add,Nat.cast_one]
    ring

/-- A bounded periodic arithmetic sequence has its exact period average
as its Cesaro limit, with a uniform remainder bound. -/
theorem periodic_cesaro_limit {f : ℕ → ℝ} {M : ℕ} (hM : 0 < M)
    (hf : Periodic f M) (h0 : ∀ i, 0 ≤ f i) (h1 : ∀ i, f i ≤ 1) :
    Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, f i)/(n : ℝ)) atTop
      (𝓝 ((∑ i ∈ Finset.range M, f i)/(M : ℝ))) := by
  let S := ∑ i ∈ Finset.range M, f i
  let L := S/(M : ℝ)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => h0 i)
  have hS1 : S ≤ M := by
    calc S ≤ ∑ _i ∈ Finset.range M, (1 : ℝ) := Finset.sum_le_sum (fun i _ => h1 i)
         _ = M := by simp
  have hL0 : 0 ≤ L := div_nonneg hS0 hMr.le
  have hL1 : L ≤ 1 := (div_le_one hMr).mpr hS1
  have hdecomp (n : ℕ) : (∑ i ∈ Finset.range n, f i) =
      (n/M : ℕ)*S + ∑ i ∈ Finset.range (n%M), f i := by
    have hnateq : n = (n/M)*M+n%M := by nlinarith only [Nat.div_add_mod n M]
    conv_lhs => rw [hnateq]
    rw [Finset.sum_range_add,periodic_sum_blocks hf]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [Nat.add_comm] using hf.nat_mul (n/M) i
  have herr (n : ℕ) : |(∑ i ∈ Finset.range n, f i)-(n : ℝ)*L| ≤ M := by
    have hr : ((n%M : ℕ) : ℝ) ≤ M := by exact_mod_cast (Nat.mod_lt n hM).le
    have hrem0 : 0 ≤ ∑ i ∈ Finset.range (n%M), f i := Finset.sum_nonneg (fun i _ => h0 i)
    have hrem1 : (∑ i ∈ Finset.range (n%M), f i) ≤ M := by
      calc _ ≤ ∑ _i ∈ Finset.range (n%M), (1 : ℝ) := Finset.sum_le_sum (fun i _ => h1 i)
           _ = ((n%M : ℕ) : ℝ) := by simp
           _ ≤ M := hr
    have hnat : (n : ℝ) = (n/M : ℕ)*(M : ℝ)+((n%M : ℕ) : ℝ) := by
      have hnateq : n = (n/M)*M+n%M := by nlinarith only [Nat.div_add_mod n M]
      exact_mod_cast hnateq
    have heq : (∑ i ∈ Finset.range n, f i)-(n : ℝ)*L =
        (∑ i ∈ Finset.range (n%M), f i)-((n%M : ℕ) : ℝ)*L := by
      rw [hdecomp,hnat]
      dsimp [L]
      field_simp
      ring
    rw [heq,abs_le]
    have hprod : ((n%M : ℕ) : ℝ)*L ≤ M :=
      (mul_le_mul_of_nonneg_left hL1 (Nat.cast_nonneg _)).trans (by simpa using hr)
    constructor <;> nlinarith [mul_nonneg (Nat.cast_nonneg (n%M)) hL0]
  have hbound (n : ℕ) : |(∑ i ∈ Finset.range (n+1), f i)/((n+1 : ℕ) : ℝ)-L| ≤ M/((n+1 : ℕ) : ℝ) := by
    have heq : (∑ i ∈ Finset.range (n+1), f i)/((n+1 : ℕ) : ℝ)-L =
        ((∑ i ∈ Finset.range (n+1), f i)-((n+1 : ℕ) : ℝ)*L)/((n+1 : ℕ) : ℝ) := by
      field_simp
    rw [heq,abs_div,abs_of_nonneg (show (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) from Nat.cast_nonneg _)]
    exact div_le_div_of_nonneg_right (herr (n+1)) (Nat.cast_nonneg _)
  have hzero := squeeze_zero (fun _ => abs_nonneg _) hbound
    ((tendsto_const_div_atTop_nhds_zero_nat (M : ℝ)).comp (tendsto_add_atTop_nat 1))
  have hd : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range (n+1), f i)/((n+1 : ℕ) : ℝ)-L) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hzero)
  have hl := hd.add_const L
  simp only [zero_add,sub_add_cancel] at hl
  exact (tendsto_add_atTop_iff_nat 1).mp hl

lemma varrho_periodic (M : ℕ) : Periodic (varrho M) M := by
  intro q
  simp only [varrho,Nat.gcd_add_self_left]

/-- The arithmetic sequence in beta has the exact mean of its period. -/
theorem varrho_cesaro_limit {M : ℕ} (hM : 0 < M) :
    Tendsto (fun Q : ℕ => (∑ q ∈ Finset.range Q, varrho M (q+1))/(Q : ℝ)) atTop
      (𝓝 ((∑ q ∈ Finset.range M, varrho M (q+1))/(M : ℝ))) := by
  apply periodic_cesaro_limit hM
  · intro q
    have heq : q+M+1 = (q+1)+M := by omega
    change varrho M (q+M+1) = varrho M (q+1)
    rw [heq,varrho_periodic M (q+1)]
  · exact fun q => varrho_nonneg M (q+1)
  · exact fun q => varrho_le_one M (q+1)

/-- The floor in Q_n has the actual required linear asymptotic. -/
theorem sieve_Q_ratio {K : ℝ} (hK : 0 < K) :
    Tendsto (fun n : ℕ => (⌊2*(n : ℝ)/K⌋₊ : ℝ)/(n : ℝ)) atTop (𝓝 (2/K)) := by
  have hlin : Tendsto (fun n : ℕ => 2*(n : ℝ)/K) atTop atTop := by
    exact (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).atTop_div_const hK
  have hfloor := (tendsto_nat_floor_div_atTop.comp hlin).mul_const (2/K)
  apply (tendsto_congr' ?_).mpr (by simpa using hfloor)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hK.ne',hnr]

/-- The beta asymptotic before identifying its period mean by CRT. -/
theorem betaN_period_mean_limit {M : ℕ} (hM : 0 < M) {K : ℝ} (hK : 0 < K) (α : ℝ) :
    Tendsto (fun n : ℕ => betaN M ⌊2*(n : ℝ)/K⌋₊ (α/(n : ℝ))) atTop
      (𝓝 ((2*α/K)*((∑ q ∈ Finset.range M, varrho M (q+1))/(M : ℝ)))) := by
  let Q : ℕ → ℕ := fun n => ⌊2*(n : ℝ)/K⌋₊
  have hlin : Tendsto (fun n : ℕ => 2*(n : ℝ)/K) atTop atTop := by
    exact (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).atTop_div_const hK
  have hQ : Tendsto Q atTop atTop := tendsto_nat_floor_atTop.comp hlin
  have hmean := (varrho_cesaro_limit hM).comp hQ
  have hratio := sieve_Q_ratio hK
  have hprod := (hratio.const_mul α).mul hmean
  apply (tendsto_congr' ?_).mpr (by convert hprod using 1 <;> ring)
  filter_upwards [eventually_gt_atTop (0 : ℕ),hQ.eventually (eventually_gt_atTop (0 : ℕ))] with n hn hQn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hQ0 : (Q n : ℝ) ≠ 0 := by exact_mod_cast hQn.ne'
  change α/(n : ℝ)*(∑ q ∈ Finset.range (Q n), varrho M (q+1)) =
    (α*((Q n : ℝ)/(n : ℝ)))*((∑ q ∈ Finset.range (Q n), varrho M (q+1))/(Q n : ℝ))
  field_simp [hn0,hQ0]

end
end Paper14
