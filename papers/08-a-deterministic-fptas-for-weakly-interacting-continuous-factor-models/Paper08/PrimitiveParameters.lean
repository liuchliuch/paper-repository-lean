import Paper08.Parameters

/-! # Generic effective parameter bounds for Lemma 3.3
The tolerance is arbitrary and positive; it need not be the special tolerance
used by the global FPTAS. All bounds apply to the actual executable choices.
-/
namespace Paper08.PrimitiveParameters
open Parameters

/-- A fixed constant depending only on the primitive Lipschitz budget base. -/
def baseLog (C : ℕ) : ℕ := binaryLog ((4 * C : ℕ) : ℚ)

def toleranceLog (τ : ℚ) : ℕ := binaryLog (1 / τ)

def levelEnvelope (C s : ℕ) (τ : ℚ) : ℕ :=
  2 * (1 + baseLog C * s + toleranceLog τ)

def sampleEnvelope (C s J : ℕ) (τ : ℚ) : ℕ :=
  (baseLog C + 3) * s + J + toleranceLog τ + 3

/-- Generic bound for the actual total-level choice, for arbitrary positive τ. -/
theorem level_le (s C : ℕ) (τ : ℚ) (hτ : 0 < τ) :
    Oracle.totalLevelChoice s C τ ≤ levelEnvelope C s τ := by
  let b := baseLog C
  let T := toleranceLog τ
  have hb : ((4 * C : ℕ) : ℚ) ^ s ≤ ((2 : ℚ) ^ b) ^ s :=
    pow_le_pow_left₀ (by positivity) (binaryLog_pow _) s
  have ht : 1 / τ ≤ (2 : ℚ) ^ T := binaryLog_pow _
  have hbase : 2 * ((4 * C : ℕ) : ℚ) ^ s / τ ≤ (2 : ℚ) ^ (1 + b * s + T) := by
    calc
      _ = 2 * ((4 * C : ℕ) : ℚ) ^ s * (1 / τ) := by ring
      _ ≤ 2 * ((2 : ℚ) ^ b) ^ s * (2 : ℚ) ^ T := by gcongr
      _ = _ := by simp only [pow_add, pow_mul, pow_one]
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℚ) ≤ 2 * ((4 * C : ℕ) : ℚ) ^ s / τ) hbase 2
  apply Oracle.totalLevelChoice_le
  convert hp using 1 <;> simp only [← pow_mul, levelEnvelope, T, b] <;> congr 1 <;> ring

/-- The explicit linear form J=O_C(s+log(1/τ)). -/
theorem level_linear {s : ℕ} (hs : 1 ≤ s) (C : ℕ) (τ : ℚ) (hτ : 0 < τ) :
    Oracle.totalLevelChoice s C τ ≤
      (2 * baseLog C + 4) * (s + toleranceLog τ) := by
  apply (level_le s C τ hτ).trans
  have ht : 1 ≤ toleranceLog τ := binaryLog_pos _
  unfold levelEnvelope
  nlinarith

/-- The reciprocal of the actual generic sample tolerance is exponentially bounded. -/
theorem sampleTolerance_inv_le {s C : ℕ} (hs : 1 ≤ s) (hC : 1 ≤ C)
    (J : ℕ) (τ : ℚ) (hτ : 0 < τ) :
    1 / Oracle.primitiveSampleTol s J C τ ≤ (2 : ℚ) ^ sampleEnvelope C s J τ := by
  let b := baseLog C
  let T := toleranceLog τ
  have hsp : (0 : ℚ) < s := by exact_mod_cast hs
  have hCp : (0 : ℚ) < C := by exact_mod_cast hC
  have hsn : (s : ℚ) ≤ (2 : ℚ) ^ s := by exact_mod_cast Nat.le_of_lt s.lt_two_pow_self
  have hJ : (J : ℚ) + 1 ≤ (2 : ℚ) ^ (J + 1) := by exact_mod_cast Nat.le_of_lt (J + 1).lt_two_pow_self
  have hb : (C : ℚ) ^ s ≤ ((2 : ℚ) ^ b) ^ s := by
    apply pow_le_pow_left₀ (by positivity)
    exact (show (C : ℚ) ≤ ((4 * C : ℕ) : ℚ) by push_cast; nlinarith).trans (binaryLog_pow _)
  have h3 : (3 : ℚ) ^ (s - 1) ≤ (2 : ℚ) ^ (2 * s) := by
    calc
      _ ≤ (4 : ℚ) ^ (s - 1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ ≤ (4 : ℚ) ^ s := pow_le_pow_right₀ (by norm_num) (Nat.sub_le s 1)
      _ = _ := by rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul]
  have ht : 1 / τ ≤ (2 : ℚ) ^ T := binaryLog_pow _
  unfold Oracle.primitiveSampleTol
  apply Parameters.inv_min_le (by positivity) (by positivity)
  · have h1 : 1 / (1 / (2 * ((J : ℚ) + 1))) ≤ (2 : ℚ) ^ (J + 2) := by
      have hp := mul_le_mul_of_nonneg_left hJ (by norm_num : (0 : ℚ) ≤ 2)
      convert hp using 1 <;> simp only [one_div, inv_inv, pow_add, pow_one] <;> ring
    apply h1.trans
    apply pow_le_pow_right₀ (by norm_num)
    unfold sampleEnvelope
    omega
  · have heq : 1 / (τ / (4 * (s : ℚ) * ((J : ℚ) + 1) * 3 ^ (s - 1) * (C : ℚ) ^ s)) =
        4 * (s : ℚ) * ((J : ℚ) + 1) * 3 ^ (s - 1) * (C : ℚ) ^ s * (1 / τ) := by field_simp
    rw [heq]
    have hp : 4 * (s : ℚ) * ((J : ℚ) + 1) * 3 ^ (s - 1) * (C : ℚ) ^ s * (1 / τ) ≤
        4 * (2 : ℚ) ^ s * (2 : ℚ) ^ (J + 1) * (2 : ℚ) ^ (2 * s) * ((2 : ℚ) ^ b) ^ s * (2 : ℚ) ^ T := by
      gcongr
    convert hp using 1
    rw [← pow_mul, show (4 : ℚ) = 2 ^ 2 by norm_num]
    simp only [← pow_add, sampleEnvelope, T, b]
    congr 1
    ring

/-- The actual oracle/sample precision is linear in s+J+log(1/τ), for arbitrary τ. -/
theorem precision_le {s C : ℕ} (hs : 1 ≤ s) (hC : 1 ≤ C)
    (J : ℕ) (τ : ℚ) (hτ : 0 < τ) :
    Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ) ≤
      (s + 2) + sampleEnvelope C s J τ := by
  let ζ := Oracle.primitiveSampleTol s J C τ
  let V := sampleEnvelope C s J τ
  have hζ : 0 < ζ := Oracle.primitiveSampleTol_pos hs hC hτ
  have h2s : ((2 * s + 1 : ℕ) : ℚ) ≤ (2 : ℚ) ^ (s + 2) := by
    have hsn : (s : ℚ) ≤ (2 : ℚ) ^ s := by exact_mod_cast Nat.le_of_lt s.lt_two_pow_self
    have hp : (1 : ℚ) ≤ 2 ^ s := one_le_pow₀ (by norm_num)
    rw [pow_add]
    norm_num
    push_cast
    nlinarith
  have hinv : 1 / ζ ≤ (2 : ℚ) ^ V := sampleTolerance_inv_le hs hC J τ hτ
  have hratio : ((2 * s + 1 : ℕ) : ℚ) / ζ ≤ (2 : ℚ) ^ ((s + 2) + V) := by
    have hp := mul_le_mul h2s hinv (by positivity : (0 : ℚ) ≤ 1 / ζ)
      (by positivity : (0 : ℚ) ≤ 2 ^ (s + 2))
    simpa only [pow_add, mul_one_div] using hp
  change binaryLog (((2 * s + 1 : ℕ) : ℚ) / ζ) ≤ _
  exact binaryLog_le (by omega) hratio

/-- A fixed-C coefficient for the generic precision bound. -/
theorem precision_linear {s C : ℕ} (hs : 1 ≤ s) (hC : 1 ≤ C)
    (J : ℕ) (τ : ℚ) (hτ : 0 < τ) :
    Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ) ≤
      (baseLog C + 9) * (s + J + toleranceLog τ) := by
  apply (precision_le hs hC J τ hτ).trans
  have ht : 1 ≤ toleranceLog τ := binaryLog_pos _
  unfold sampleEnvelope
  nlinarith

/-- Both actual growing parameters are O_C(s+log(1/τ)), as required in Lemma 3.3. -/
theorem level_precision_linear {s C : ℕ} (hs : 1 ≤ s) (hC : 1 ≤ C)
    (τ : ℚ) (hτ : 0 < τ) :
    let J := Oracle.totalLevelChoice s C τ
    J ≤ (2 * baseLog C + 4) * (s + toleranceLog τ) ∧
      Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ) ≤
        (3 * baseLog C + 14) * (s + toleranceLog τ) := by
  dsimp only
  have hJ := level_linear hs C τ hτ
  refine ⟨hJ, ?_⟩
  apply (precision_le hs hC (Oracle.totalLevelChoice s C τ) τ hτ).trans
  have ht : 1 ≤ toleranceLog τ := binaryLog_pos _
  unfold sampleEnvelope
  nlinarith

end Paper08.PrimitiveParameters
