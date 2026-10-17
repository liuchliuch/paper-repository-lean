import Paper09.RareScale
import Paper09.Covering
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

open Real Filter Asymptotics
open scoped Topology
noncomputable section
namespace Paper09.UpperScale

/-- We choose the paper's allowed fixed constant `C₁ = 32 > 16`. -/
def roundedRadius (L : ℝ) : ℕ := 8 * Nat.ceil (4 * log L)

/-- The actual integer bad-cluster cutoff. -/
def clusterCutoff (κ : ℝ) (n : ℕ) : ℕ := Nat.ceil (κ * log n)

lemma roundedRadius_bounds {L : ℝ} (hL : 1 ≤ log L) :
    32 * log L ≤ (roundedRadius L : ℝ) ∧ (roundedRadius L : ℝ) ≤ 40 * log L := by
  have hlow := Nat.le_ceil (4 * log L)
  have hupp := (Nat.ceil_lt_add_one (by linarith : 0 ≤ 4 * log L)).le
  dsimp [roundedRadius]
  push_cast
  constructor <;> linarith

theorem roundedRadius_tendsto :
    Tendsto (fun L : ℝ => (roundedRadius L : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (Real.tendsto_log_atTop.const_mul_atTop (by norm_num : (0:ℝ)<32))
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)] with L hL
  exact (roundedRadius_bounds hL).1

lemma radius_tail_bound {L : ℝ} (hLp : 0 < L) (hL : 1 ≤ log L) :
    exp (-(roundedRadius L : ℝ)/8) ≤ (L ^ 4)⁻¹ := by
  have hr := (roundedRadius_bounds hL).1
  have he : exp (-(roundedRadius L : ℝ)/8) ≤ exp (-(4 * log L)) :=
    Real.exp_le_exp.mpr (by linarith)
  apply he.trans_eq
  rw [Real.exp_neg, show (4:ℝ)*log L = (4:ℕ)*log L by norm_num,
    Real.exp_nat_mul, Real.exp_log hLp]

/-- Real-variable version of the second term in (3.11), with the integer
rounded radius and any fixed dimension. -/
lemma tail_ratio_bound (d : ℕ) (hd : 1 ≤ d) {L : ℝ} (hLp : 0 < L) (hL : 1 ≤ log L) :
    L * (roundedRadius L : ℝ) ^ d * exp (-(roundedRadius L : ℝ)/8) /
      (roundedRadius L : ℝ) ≤
      40 ^ (d-1) * (log L) ^ (d-1) / L ^ 3 := by
  let R : ℝ := roundedRadius L
  have hR : 0 < R := by have hh := (roundedRadius_bounds hL).1; dsimp [R]; linarith
  have hpow := pow_le_pow_left₀ hR.le (roundedRadius_bounds hL).2 (d-1)
  have htail := radius_tail_bound hLp hL
  have heq : L * R ^ d * exp (-R/8) / R = L * R ^ (d-1) * exp (-R/8) := by
    have hde : d = (d-1)+1 := by omega
    conv_lhs => rw [hde, pow_succ]
    field_simp
  change L * R ^ d * exp (-R/8) / R ≤ _
  rw [heq]
  calc
    L * R ^ (d-1) * exp (-R/8) ≤ L * (40 * log L) ^ (d-1) * (L ^ 4)⁻¹ := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hpow hLp.le
      · exact htail
      · exact (exp_pos _).le
      · positivity
    _ = _ := by rw [mul_pow]; field_simp

/-- Equation (3.11): the actual rounded radius makes the maximal
influence `H_R` negligible relative to `R`. -/
theorem influence_ratio_tendsto (d : ℕ) (hd : 1 ≤ d) (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun L : ℝ =>
      (C * (log (roundedRadius L)) ^ 2 +
        C * (L * (roundedRadius L : ℝ) ^ d) * exp (-(roundedRadius L : ℝ)/8)) /
          (roundedRadius L : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun R : ℝ => (log R)^2/R) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_ofNat, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero
  have hfirst := (hlog.comp roundedRadius_tendsto).const_mul C
  have htail : Tendsto (fun L : ℝ =>
      L * (roundedRadius L : ℝ)^d * exp (-(roundedRadius L : ℝ)/8) /
        (roundedRadius L : ℝ)) atTop (𝓝 0) := by
    have hbound : Tendsto (fun L : ℝ => 40^(d-1) * (log L)^(d-1) / L^3) atTop (𝓝 0) := by
      have hh := (isLittleO_log_rpow_rpow_atTop ((d-1:ℕ):ℝ)
        (by norm_num : (0:ℝ)<3)).tendsto_div_nhds_zero.const_mul (40^(d-1):ℝ)
      simpa only [Real.rpow_natCast, Real.rpow_ofNat, mul_div_assoc, mul_zero] using hh
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
      positivity
    · filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
      eventually_gt_atTop (0:ℝ)] with L hL hLp
      exact tail_ratio_bound d hd hLp hL
  have h := hfirst.add (htail.const_mul C)
  convert h using 1 <;> try simp
  ext L
  dsimp
  ring

/-- The coverage/boundary overlap can absorb the complete influence term,
uniformly over every block volume bounded by `L R^d`. -/
theorem overlap_absorption (d : ℕ) (hd : 1 ≤ d) (C A : ℝ)
    (hC : 0 ≤ C) (hA : 0 < A) :
    ∀ᶠ L : ℝ in atTop, ∀ M I J : ℝ,
      0 ≤ M → M ≤ L*(roundedRadius L:ℝ)^d → 0 < I → 0 ≤ J →
      J*(roundedRadius L:ℝ) ≤ A*I →
      (C*(log (roundedRadius L))^2+C*M*exp (-(roundedRadius L:ℝ)/8))*J ≤ I/2 := by
  have hs := (influence_ratio_tendsto d hd C hC).eventually
    (gt_mem_nhds (show (0:ℝ) < 1/(2*A) by positivity))
  filter_upwards [hs, Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)] with L hsmall hL
  intro M I J hM hMb hI hJ hJI
  have hR : 0 < (roundedRadius L:ℝ) := by have hh := (roundedRadius_bounds hL).1; linarith
  have hbound : C*(log (roundedRadius L))^2+C*M*exp (-(roundedRadius L:ℝ)/8) ≤
      C*(log (roundedRadius L))^2+C*(L*(roundedRadius L:ℝ)^d)*exp (-(roundedRadius L:ℝ)/8) := by
    nlinarith [mul_le_mul_of_nonneg_left hMb (mul_nonneg hC (exp_pos (-(roundedRadius L:ℝ)/8)).le)]
  have hlarge := (div_lt_iff₀ hR).mp hsmall
  have hratio := mul_le_mul_of_nonneg_left hJI (show 0 ≤ 1/(2*A) by positivity)
  have hcancel : 1/(2*A)*(A*I) = I/2 := by field_simp
  rw [hcancel] at hratio
  have hmul := mul_le_mul_of_nonneg_right (hbound.trans hlarge.le) hJ
  nlinarith

/-- Physical duration of a simulated color step, as in (3.18). -/
def stepTime (d : ℕ) (C R L M N : ℝ) : ℝ :=
  C * exp (C * (R ^ (d-1) * L ^ exponentA d)) *
    (M*(1+sqrt (log N))+2*log M+1)

/-- Number of simulated steps in (3.20), including its integer ceiling. -/
def stepCount (C M N : ℝ) : ℕ := Nat.ceil (C*M*log (16*N))

/-- Deterministic real-scale absorption of all prefactors in (3.18)--(3.20).
Only elementary size constraints are hypotheses; the final time estimate is
proved from them. These constraints are discharged for the actual ceil scales below. -/
theorem log_total_time_le (d : ℕ) (hd : 2 ≤ d) (C L R M N : ℝ)
    (hC : 1 ≤ C) (hL : 1 ≤ L) (hR : 1 ≤ R) (hRL : R ≤ L)
    (hM : 1 ≤ M) (hMb : M ≤ L*R^d) (hN : 1 ≤ N) (hNl : log N ≤ L)
    (hlogL : log L ≤ L ^ exponentA d) :
    log ((stepCount C M N : ℝ)*stepTime d C R L M N) ≤
      (log (100*C^2)+C+2*(d+2)) * (R^(d-1)*L^exponentA d) := by
  have hCp : 0 < C := by linarith
  have hLp : 0 < L := by linarith
  have hMp : 0 < M := by linarith
  have hNp : 0 < N := by linarith
  have hlogM : 0 ≤ log M := Real.log_nonneg hM
  have hsqrt : sqrt (log N) ≤ L := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨hLp.le, by nlinarith⟩
  have hMpoly : M ≤ L^(d+1) := by
    calc M ≤ L*R^d := hMb
      _ ≤ L*L^d := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hRL d) hLp.le
      _ = _ := by rw [pow_succ]; ring
  have hML : M*L ≤ L^(d+2) := by
    have hh := mul_le_mul_of_nonneg_right hMpoly hLp.le
    simpa only [show d+2 = (d+1)+1 by omega, pow_succ] using hh
  have hP : 1 ≤ L^(d+2) := one_le_pow₀ hL
  have hbracket : M*(1+sqrt (log N))+2*log M+1 ≤ 5*L^(d+2) := by
    have hh := Real.log_le_self hMp.le
    have hh1 := mul_le_mul_of_nonneg_left hsqrt hMp.le
    nlinarith [hML]
  have hbracketpos : 0 < M*(1+sqrt (log N))+2*log M+1 := by positivity
  have hlog16 : log (16*N) ≤ 17*L := by
    rw [Real.log_mul (by norm_num) hNp.ne']
    have hh := Real.log_le_self (show (0:ℝ)≤16 by norm_num)
    linarith
  have hlog16pos : 0 < log (16*N) := Real.log_pos (by linarith)
  have hk1 : 1 ≤ stepCount C M N := Nat.one_le_ceil_iff.mpr (by positivity)
  have hkpos : 0 < (stepCount C M N : ℝ) := by exact_mod_cast (by omega : 0 < stepCount C M N)
  have hk : (stepCount C M N : ℝ) ≤ 20*C*L^(d+2) := by
    have hh := (Nat.ceil_lt_add_one (show 0 ≤ C*M*log (16*N) by positivity)).le
    have hh2 := mul_le_mul_of_nonneg_left hlog16 (mul_nonneg hCp.le hMp.le)
    have hh3 := mul_le_mul_of_nonneg_left hML (show 0 ≤ 17*C by positivity)
    have hh4 : 1 ≤ C*L^(d+2) := by
      simpa using mul_le_mul hC hP (by norm_num : (0:ℝ)≤1) hCp.le
    change (Nat.ceil (C*M*log (16*N)) : ℝ) ≤ _
    nlinarith only [hh, hh2, hh3, hh4]
  let S : ℝ := R^(d-1)*L^exponentA d
  have hS : 1 ≤ S := by
    simpa [S] using mul_le_mul (one_le_pow₀ (n := d-1) hR)
      (Real.one_le_rpow hL (exponentA_pos hd).le) (by norm_num : (0:ℝ)≤1)
      (pow_nonneg (by linarith : (0:ℝ)≤R) (d-1))
  have hLS : L^exponentA d ≤ S := by
    have hh := mul_le_mul_of_nonneg_right (one_le_pow₀ (n := d-1) hR)
      (Real.rpow_nonneg hLp.le (exponentA d))
    simpa [S] using hh
  have hlogS : log L ≤ S := hlogL.trans hLS
  have htotpos : 0 < (stepCount C M N : ℝ)*stepTime d C R L M N := by
    unfold stepTime
    positivity
  have htot : (stepCount C M N : ℝ)*stepTime d C R L M N ≤
      100*C^2*(L^(d+2))^2*exp (C*S) := by
    unfold stepTime
    change _ * (C*exp (C*S)*_) ≤ _
    calc
      _ ≤ (20*C*L^(d+2))*(C*exp (C*S)*(5*L^(d+2))) := by gcongr
      _ = _ := by ring
  have hlog := Real.log_le_log htotpos htot
  have hClog : 0 ≤ log (100*C^2) := Real.log_nonneg (by nlinarith)
  have hupper : log (100*C^2*(L^(d+2))^2*exp (C*S)) =
      log (100*C^2)+2*((d+2:ℕ):ℝ)*log L+C*S := by
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_exp]
    ring
  rw [hupper] at hlog
  have hconst := mul_le_mul_of_nonneg_left hS hClog
  have hlogterm := mul_le_mul_of_nonneg_left hlogS
    (show 0 ≤ 2*((d+2:ℕ):ℝ) by positivity)
  push_cast at hlogterm hlog
  change _ ≤ (log (100*C^2)+C+2*(d+2))*S
  nlinarith only [hlog, hconst, hlogterm]

/-- The ceil cutoff has logarithmic size, with its rounding error retained. -/
lemma clusterCutoff_bounds {κ : ℝ} (hκ : 0 ≤ κ) {n : ℕ} (hn : 3 ≤ n) :
    κ*log n ≤ (clusterCutoff κ n:ℝ) ∧
      (clusterCutoff κ n:ℝ) ≤ (κ+1)*log n := by
  have hln : 1 ≤ log (n:ℝ) := (one_lt_log_of_three_le (by exact_mod_cast hn)).le
  have hlo := Nat.le_ceil (κ*log n)
  have hhi := (Nat.ceil_lt_add_one (mul_nonneg hκ (by linarith : 0 ≤ log (n:ℝ)))).le
  change _ ≤ (Nat.ceil (κ*log n):ℝ) ∧ (Nat.ceil (κ*log n):ℝ) ≤ _
  constructor
  · exact hlo
  · nlinarith

theorem clusterCutoff_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => (clusterCutoff κ n:ℝ)) atTop atTop := by
  apply tendsto_atTop_mono' atTop _
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hκ)
  exact Eventually.of_forall (fun n => Nat.le_ceil (κ*log n))

/-- All elementary constraints used in the real-scale physical-time bound
hold eventually for the actual integer scales. -/
theorem rounded_constraints (d : ℕ) (hd : 2 ≤ d) {κ : ℝ}
    (hκ : 1 ≤ κ) (hκd : 4*(d:ℝ) ≤ κ) :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ (clusterCutoff κ n:ℝ) ∧
      1 ≤ (roundedRadius (clusterCutoff κ n):ℝ) ∧
      (roundedRadius (clusterCutoff κ n):ℝ) ≤ clusterCutoff κ n ∧
      log (((2*n+1)^d:ℕ):ℝ) ≤ clusterCutoff κ n ∧
      log (clusterCutoff κ n) ≤ (clusterCutoff κ n:ℝ)^exponentA d := by
  have hκp : 0 < κ := by linarith
  have hLtop := clusterCutoff_tendsto hκp
  have hRtop := roundedRadius_tendsto.comp hLtop
  have hsmall := Real.isLittleO_log_id_atTop.bound (show (0:ℝ)<1/40 by norm_num)
  have hlogpow := (isLittleO_log_rpow_atTop (exponentA_pos hd)).bound (show (0:ℝ)<1 by norm_num)
  filter_upwards [hLtop.eventually (eventually_ge_atTop (Real.exp 1)),
    hRtop.eventually (eventually_ge_atTop 1), hLtop.eventually hsmall,
    hLtop.eventually hlogpow, eventually_ge_atTop (3:ℕ)] with n hL hR hsmall hpow hn
  let L : ℝ := clusterCutoff κ n
  have hLe : 1 ≤ L := by
    have hh : 1 ≤ exp (1:ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
    exact hh.trans hL
  have hLp : 0 < L := by linarith
  have hlogL : 1 ≤ log L := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hL
  have hln : 1 ≤ log (n:ℝ) := (one_lt_log_of_three_le (by exact_mod_cast hn)).le
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have hLN : log (((2*n+1)^d:ℕ):ℝ) ≤ L := by
    push_cast
    rw [Real.log_pow]
    have hnsize : 2*(n:ℝ)+1 ≤ 3*n := by nlinarith [show (3:ℝ)≤n by exact_mod_cast hn]
    have hh := Real.log_le_log (show 0<2*(n:ℝ)+1 by positivity) hnsize
    rw [Real.log_mul (by norm_num) hnpos.ne'] at hh
    have h3 := Real.log_le_self (show (0:ℝ)≤3 by norm_num)
    have hfactor : log (2*(n:ℝ)+1) ≤ 4*log n := by linarith
    have hh1 := mul_le_mul_of_nonneg_left hfactor (Nat.cast_nonneg d : (0:ℝ)≤d)
    have hh2 := mul_le_mul_of_nonneg_right hκd (show 0≤log (n:ℝ) by linarith)
    have hh3 := (clusterCutoff_bounds (show 0≤κ by linarith) hn).1
    change _ ≤ L
    dsimp [L]
    nlinarith
  refine ⟨hLe, hR, ?_, hLN, ?_⟩
  · have hrad := (roundedRadius_bounds hlogL).2
    change (roundedRadius L:ℝ) ≤ L
    change ‖log L‖ ≤ (1/40:ℝ)*‖L‖ at hsmall
    rw [Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hLp.le] at hsmall
    linarith
  · change log L ≤ L^exponentA d
    change ‖log L‖ ≤ (1:ℝ)*‖L^exponentA d‖ at hpow
    rw [Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (Real.rpow_nonneg hLp.le _), one_mul] at hpow
    exact hpow

/-- The two integer scales have the claimed `log n` / `log log n` upper
bounds, with explicit constants depending only on `κ`. -/
theorem rounded_growth_bounds {κ : ℝ} (hκ : 1 ≤ κ) :
    ∀ᶠ n : ℕ in atTop,
      0 < log n ∧ 0 < log (log n) ∧
      (clusterCutoff κ n:ℝ) ≤ (κ+1)*log n ∧
      (roundedRadius (clusterCutoff κ n):ℝ) ≤
        (40*(log (κ+1)+1))*log (log n) := by
  have hκp : 0 < κ := by linarith
  have hLtop := clusterCutoff_tendsto hκp
  filter_upwards [hLtop.eventually (Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)),
    tendsto_natCast_atTop_atTop.eventually
      (tendsto_loglog_atTop.eventually (eventually_ge_atTop 1)),
    eventually_ge_atTop (3:ℕ)] with n hlogL hll hn
  have hln : 0 < log (n:ℝ) := by linarith [one_lt_log_of_three_le (show (3:ℝ)≤n by exact_mod_cast hn)]
  have hLpos : 0 < (clusterCutoff κ n:ℝ) :=
    (mul_pos hκp hln).trans_le (Nat.le_ceil _)
  have hLu := (clusterCutoff_bounds hκp.le hn).2
  have hlog := Real.log_le_log hLpos hLu
  rw [Real.log_mul (by linarith : κ+1 ≠ 0) hln.ne'] at hlog
  have hκlog : 0 ≤ log (κ+1) := Real.log_nonneg (by linarith)
  have hh := (roundedRadius_bounds hlogL).2
  refine ⟨hln, by linarith, hLu, ?_⟩
  have hm := mul_le_mul_of_nonneg_left hll hκlog
  nlinarith

/-- The complete final time absorption with the exact integer choices in
(3.10) and (3.20). The result is uniform in every admissible block volume. -/
theorem final_time_bound (d : ℕ) (hd : 2 ≤ d) (κ C : ℝ)
    (hκ : 1 ≤ κ) (hκd : 4*(d:ℝ) ≤ κ) (hC : 1 ≤ C) :
    ∃ C' > 0, ∀ᶠ n : ℕ in atTop, ∀ M : ℝ,
      1 ≤ M → M ≤ (clusterCutoff κ n:ℝ)*(roundedRadius (clusterCutoff κ n):ℝ)^d →
      log ((stepCount C M (((2*n+1)^d:ℕ):ℝ):ℝ) *
        stepTime d C (roundedRadius (clusterCutoff κ n)) (clusterCutoff κ n) M (((2*n+1)^d:ℕ):ℝ)) ≤
      C'*(log (n:ℝ))^exponentA d*(log (log (n:ℝ)))^(d-1) := by
  let D : ℝ := log (100*C^2)+C+2*(d+2)
  let A : ℝ := κ+1
  let B : ℝ := 40*(log (κ+1)+1)
  have hCp : 0 < C := by linarith
  have hD : 0 < D := by
    have hh : 0 ≤ log (100*C^2) := Real.log_nonneg (by nlinarith)
    dsimp [D]
    positivity
  have hA : 0 < A := by dsimp [A]; linarith
  have hB : 0 < B := by
    have hh : 0 ≤ log (κ+1) := Real.log_nonneg (by linarith)
    dsimp [B]
    positivity
  refine ⟨D*B^(d-1)*A^exponentA d, by positivity, ?_⟩
  filter_upwards [rounded_constraints d hd hκ hκd, rounded_growth_bounds hκ] with n hn hg
  intro M hM hMb
  have hN : 1 ≤ (((2*n+1)^d:ℕ):ℝ) := by exact_mod_cast (one_le_pow₀ (show 1≤2*n+1 by omega) : 1≤(2*n+1)^d)
  have hh := log_total_time_le d hd C (clusterCutoff κ n) (roundedRadius (clusterCutoff κ n))
    M (((2*n+1)^d:ℕ):ℝ) hC hn.1 hn.2.1 hn.2.2.1 hM hMb hN hn.2.2.2.1 hn.2.2.2.2
  apply hh.trans
  have hLpow := Real.rpow_le_rpow (show (0:ℝ)≤clusterCutoff κ n by positivity) hg.2.2.1 (exponentA_pos hd).le
  have hRpow := pow_le_pow_left₀ (show (0:ℝ)≤roundedRadius (clusterCutoff κ n) by positivity) hg.2.2.2 (d-1)
  rw [Real.mul_rpow (by linarith : 0≤κ+1) hg.1.le] at hLpow
  rw [mul_pow] at hRpow
  have hprod := mul_le_mul hRpow hLpow
    (Real.rpow_nonneg (show (0:ℝ)≤clusterCutoff κ n by positivity) _)
    (mul_nonneg (pow_nonneg hB.le _) (pow_nonneg hg.2.1.le _))
  have hmul := mul_le_mul_of_nonneg_left hprod hD.le
  change D*((roundedRadius (clusterCutoff κ n):ℝ)^(d-1)*(clusterCutoff κ n:ℝ)^exponentA d) ≤ _
  convert hmul using 1 <;> dsimp [A, B] <;> ring

/-- Equation (3.11) at the actual integer cutoff from (3.10). -/
theorem actual_influence_ratio_tendsto (d : ℕ) (hd : 1 ≤ d) (C κ : ℝ)
    (hC : 0 ≤ C) (hκ : 0 < κ) :
    Tendsto (fun n : ℕ =>
      (C*(log (roundedRadius (clusterCutoff κ n)))^2+
        C*((clusterCutoff κ n:ℝ)*(roundedRadius (clusterCutoff κ n):ℝ)^d)*
          exp (-(roundedRadius (clusterCutoff κ n):ℝ)/8)) /
        (roundedRadius (clusterCutoff κ n):ℝ)) atTop (𝓝 0) :=
  (influence_ratio_tendsto d hd C hC).comp (clusterCutoff_tendsto hκ)

/-- The actual integer scale satisfies the range and divisibility hypotheses
of Lemma 3.2, for every fixed lower cutoff. -/
theorem scales_admissible (d : ℕ) (hd : 2 ≤ d) (κ : ℝ)
    (hκ : 1 ≤ κ) (hκd : 4*(d:ℝ) ≤ κ) (R₀ : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      R₀ ≤ roundedRadius (clusterCutoff κ n) ∧
      roundedRadius (clusterCutoff κ n) ≤ n ∧
      8 ∣ roundedRadius (clusterCutoff κ n) ∧
      κ*log n ≤ (clusterCutoff κ n:ℝ) := by
  have hκp : 0 < κ := by linarith
  have hA : 0 < κ+1 := by linarith
  have hRtop := roundedRadius_tendsto.comp (clusterCutoff_tendsto hκp)
  have hsmall := Real.isLittleO_log_id_atTop.bound (show 0 < 1/(κ+1) by positivity)
  filter_upwards [rounded_constraints d hd hκ hκd,
    hRtop.eventually (eventually_ge_atTop (R₀:ℝ)),
    tendsto_natCast_atTop_atTop.eventually hsmall,
    eventually_ge_atTop (3:ℕ)] with n hn hR hsmall hn3
  have hln : 0 ≤ log (n:ℝ) := by linarith [one_lt_log_of_three_le (show (3:ℝ)≤n by exact_mod_cast hn3)]
  change ‖log (n:ℝ)‖ ≤ 1/(κ+1)*‖(n:ℝ)‖ at hsmall
  rw [Real.norm_of_nonneg hln, Real.norm_of_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n)] at hsmall
  have hmul := mul_le_mul_of_nonneg_left hsmall hA.le
  have heq : (κ+1)*(1/(κ+1)*(n:ℝ)) = n := by field_simp
  rw [heq] at hmul
  have hLu := (clusterCutoff_bounds hκp.le hn3).2
  change (R₀:ℝ) ≤ (roundedRadius (clusterCutoff κ n):ℝ) at hR
  refine ⟨by exact_mod_cast hR, ?_, ?_, Nat.le_ceil _⟩
  · have hh : (roundedRadius (clusterCutoff κ n):ℝ) ≤ n := hn.2.2.1.trans (hLu.trans hmul)
    exact_mod_cast hh
  · exact dvd_mul_right 8 _

/-- The total physical time itself, in the exact exponential form needed
by Proposition 3.1. -/
theorem final_physical_time_bound (d : ℕ) (hd : 2 ≤ d) (κ C : ℝ)
    (hκ : 1 ≤ κ) (hκd : 4*(d:ℝ) ≤ κ) (hC : 1 ≤ C) :
    ∃ C' > 0, ∀ᶠ n : ℕ in atTop, ∀ M : ℝ,
      1 ≤ M → M ≤ (clusterCutoff κ n:ℝ)*(roundedRadius (clusterCutoff κ n):ℝ)^d →
      (stepCount C M (((2*n+1)^d:ℕ):ℝ):ℝ) *
        stepTime d C (roundedRadius (clusterCutoff κ n)) (clusterCutoff κ n) M (((2*n+1)^d:ℕ):ℝ) ≤
      exp (C'*(log (n:ℝ))^exponentA d*(log (log (n:ℝ)))^(d-1)) := by
  obtain ⟨C', hC', ht⟩ := final_time_bound d hd κ C hκ hκd hC
  refine ⟨C', hC', ?_⟩
  filter_upwards [ht] with n hn
  intro M hM hMb
  let t : ℝ := (stepCount C M (((2*n+1)^d:ℕ):ℝ):ℝ) *
    stepTime d C (roundedRadius (clusterCutoff κ n)) (clusterCutoff κ n) M (((2*n+1)^d:ℕ):ℝ)
  by_cases htpos : 0 < t
  · exact (Real.log_le_iff_le_exp htpos).mp (hn M hM hMb)
  · exact (le_of_not_gt htpos).trans (Real.exp_pos _).le

end Paper09.UpperScale
