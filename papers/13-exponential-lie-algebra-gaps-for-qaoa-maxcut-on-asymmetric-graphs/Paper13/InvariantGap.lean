import Paper13.GadgetAssembly
import Paper13.Arithmetic
noncomputable section
namespace Paper13
open scoped BigOperators

/-- The actual largest irreducible dimension, rather than a numerical proxy. -/
theorem Gk_largestIrrep_bound (k : ℕ) (hk : 1 ≤ k) : largestIrrep (GkOrdinal k) ≤ 126^k/2 := by
  apply csSup_le'
  rintro d ⟨W,hplus,hW,hd⟩
  rw [← hd]
  exact Gk_irreducible_dimension k hk W hW

lemma Gk_parity_dimension_number (k : ℕ) (hk : 1 ≤ k) : 2^(k*7-1) = 128^k/2 := by
  have hp : (2 : ℕ)^(k*7-1)*2 = 128^k := by
    calc _ = 2^((k*7-1)+1) := (pow_succ _ _).symm
         _ = 2^(k*7) := by congr 1; omega
         _ = (2^7)^k := by rw [Nat.mul_comm k 7,pow_mul]
         _ = 128^k := by norm_num
  omega

/-- The actual additive invariant-component deficit of Corollary 2. -/
theorem Gk_deficit_bound (k : ℕ) (hk : 1 ≤ k) :
    (128^k-126^k)/2 ≤ invariantDeficit (GkOrdinal k) := by
  have hm := Gk_largestIrrep_bound k hk
  have hp := Gk_parity_dimension_number k hk
  have hpow : (126 : ℕ)^k ≤ 128^k := by gcongr; norm_num
  change (128^k-126^k)/2 ≤ 2^(k*7-1)-largestIrrep (GkOrdinal k)
  rw [hp]
  omega

/-- Full finite-k Corollary 2 for the actual representation. -/
theorem corollary2_actual (k : ℕ) (hk : 7 ≤ k) : Corollary2Claim k :=
  ⟨Gk_largestIrrep_bound k (by omega), Gk_deficit_bound k (by omega)⟩

lemma Gk_largestIrrep_le_parity (k : ℕ) (hk : 1 ≤ k) :
    largestIrrep (GkOrdinal k) ≤ 2^(k*7-1) := by
  rw [Gk_parity_dimension_number k hk]
  have hm := Gk_largestIrrep_bound k hk
  have hpow : (126 : ℕ)^k ≤ 128^k := by gcongr; norm_num
  omega

/-- The actual normalized deficit has the geometric lower envelope from the paper. -/
lemma Gk_deficit_ratio_lower (k : ℕ) (hk : 1 ≤ k) :
    1-(63/64 : ℝ)^k ≤ (invariantDeficit (GkOrdinal k) : ℝ)/(2 : ℝ)^(7*k-1) := by
  have hle := Gk_deficit_bound k hk
  have hbase : (0 : ℝ) < 2^(7*k-1) := by positivity
  have hpow : (126 : ℕ)^k ≤ 128^k := by gcongr; norm_num
  have heven : 2 ∣ (128 : ℕ)^k - 126^k := by
    have h1 : 2 ∣ (128 : ℕ)^k := dvd_pow (by norm_num) (by omega : k ≠ 0)
    have h2 : 2 ∣ (126 : ℕ)^k := dvd_pow (by norm_num) (by omega : k ≠ 0)
    exact Nat.dvd_sub' h1 h2
  have hcast : (((128^k-126^k)/2 : ℕ) : ℝ) = ((128 : ℝ)^k-126^k)/2 := by
    rw [Nat.cast_div heven (by norm_num),Nat.cast_sub hpow]
    push_cast
    rfl
  have hq := congrArg (fun z : ℚ => (z : ℝ)) (Arith.cor2_main_ineq k)
  have hf : ((128 : ℝ)^k-126^k)/2 = 2^(7*k-1)*(1-(63/64 : ℝ)^k) := by
    simpa only [Rat.cast_div,Rat.cast_sub,Rat.cast_pow,Rat.cast_mul,Rat.cast_one,Rat.cast_ofNat] using hq
  have hreal : ((128 : ℝ)^k-126^k)/2 ≤ (invariantDeficit (GkOrdinal k) : ℝ) := by
    rw [← hcast]
    exact_mod_cast hle
  rw [le_div_iff₀ hbase]
  nlinarith [hf]

lemma Gk_deficit_ratio_upper (k : ℕ) :
    (invariantDeficit (GkOrdinal k) : ℝ)/(2 : ℝ)^(7*k-1) ≤ 1 := by
  have h : invariantDeficit (GkOrdinal k) ≤ 2^(7*k-1) := by
    change 2^(k*7-1)-largestIrrep (GkOrdinal k) ≤ 2^(7*k-1)
    calc _ ≤ 2^(k*7-1) := Nat.sub_le _ _
         _ = 2^(7*k-1) := by congr 1; omega
  apply (div_le_one (by positivity : (0 : ℝ) < 2^(7*k-1))).mpr
  exact_mod_cast h

/-- Corollary 2's limit for the actual invariant deficit. -/
theorem corollary2_actual_limit : Filter.Tendsto
    (fun k : ℕ => (invariantDeficit (GkOrdinal k) : ℝ)/(2 : ℝ)^(7*k-1))
    Filter.atTop (nhds 1) := by
  have hlow : Filter.Tendsto (fun k : ℕ => 1-(63/64 : ℝ)^k) Filter.atTop (nhds 1) := by
    convert tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 63/64) (by norm_num : (63/64 : ℝ) < 1)) using 1 <;> simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with k hk
    exact Gk_deficit_ratio_lower k hk
  · exact Filter.Eventually.of_forall Gk_deficit_ratio_upper
end Paper13
