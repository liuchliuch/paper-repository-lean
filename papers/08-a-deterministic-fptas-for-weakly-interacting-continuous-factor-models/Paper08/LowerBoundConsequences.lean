import Paper08.LowerBoundAdaptive
import Paper08.Oracle

/-! # Explicit sampling consequences of Proposition B.1

For fixed `r`, `K`, and `U`, the specialization `m = n / r`, `ε = 1 / n`
yields a positive explicit constant times `n^(2*r+1)` after an explicit
threshold. The algorithm theorem invokes the actual adaptive lower bound.
-/
noncomputable section
open scoped Real BigOperators
open MeasureTheory
namespace Paper08.LowerBound

/-- Half the leading coefficient obtained by bounding `floor(n/r)` below by `n/(2r)`. -/
def samplingOmegaConstant (r : ℕ) (K U : ℝ) : ℝ :=
  (c0 r K U / (2 * U)) ^ r / (2 * (2 * (r : ℝ)) ^ (r + 1))

lemma samplingOmegaConstant_pos {r : ℕ} {K U : ℝ}
    (hr : 1 ≤ r) (hK : 0 < K) (hU : 1 < U) :
    0 < samplingOmegaConstant r K U := by
  unfold samplingOmegaConstant
  have hc := c0_pos hr hK hU
  positivity

/-- An explicit threshold that also absorbs the subtracted linear term in (B.1). -/
def samplingOmegaThreshold (r : ℕ) (K U : ℝ) : ℕ :=
  max (2 * r) ⌈1 / samplingOmegaConstant r K U⌉₊

lemma floor_div_ge_half {n r : ℕ} (hr : 1 ≤ r) (hn : 2 * r ≤ n) :
    (n : ℝ) / (2 * r) ≤ (n / r : ℕ) := by
  have hr0 : 0 < r := by omega
  have hm : 1 ≤ n / r := (Nat.le_div_iff_mul_le hr0).mpr (by omega)
  have hmod : n % r < r := Nat.mod_lt n hr0
  have hsum : n / r * r + n % r = n := by simpa only [Nat.mul_comm] using Nat.div_add_mod n r
  have hmul : r ≤ n / r * r := by nlinarith
  have hnat : n ≤ (n / r) * (2 * r) := by nlinarith
  have hrR : 0 < (r : ℝ) := by positivity
  apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) * r)).mpr
  exact_mod_cast hnat

/-- The literal right-hand side of (B.1) has the stated eventual polynomial lower bound. -/
lemma sampling_rhs_ge_power {n r : ℕ} {K U : ℝ}
    (hr : 1 ≤ r) (hK : 0 < K) (hU : 1 < U)
    (hn : samplingOmegaThreshold r K U ≤ n) :
    samplingOmegaConstant r K U * (n : ℝ) ^ (2 * r + 1) ≤
      (c0 r K U / (2 * U * (1 / (n : ℝ)))) ^ r *
        (n / r : ℕ) ^ (r + 1) - (n / r : ℕ) := by
  let δ := samplingOmegaConstant r K U
  have hδ : 0 < δ := samplingOmegaConstant_pos hr hK hU
  have hn2 : 2 * r ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by positivity
  have hrR : (r : ℝ) ≠ 0 := by positivity
  have hU0 : U ≠ 0 := by linarith
  have hc := c0_pos hr hK hU
  have hm0 : 0 ≤ ((n / r : ℕ) : ℝ) := by positivity
  have hfloor := floor_div_ge_half hr hn2
  have hceil : 1 / δ ≤ (n : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right (2 * r) ⌈1 / δ⌉₊).trans hn)
  have hδn : 1 ≤ δ * (n : ℝ) := by
    have hh := (div_le_iff₀ hδ).mp hceil
    nlinarith
  have hpow : (n : ℝ) ≤ (n : ℝ) ^ (2 * r) := le_self_pow₀ hnR (by omega)
  have habsorb : (n : ℝ) ≤ δ * (n : ℝ) ^ (2 * r + 1) := by
    have hh : 1 ≤ δ * (n : ℝ) ^ (2 * r) :=
      hδn.trans (mul_le_mul_of_nonneg_left hpow hδ.le)
    have hh' := mul_le_mul_of_nonneg_right hh hn0.le
    simpa only [one_mul, pow_succ, mul_assoc] using hh'
  have hlinear : ((n / r : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.div_le_self n r
  have hroot : c0 r K U / (2 * U * (1 / (n : ℝ))) =
      (c0 r K U / (2 * U)) * n := by field_simp
  have hleading : 2 * δ * (n : ℝ) ^ (2 * r + 1) ≤
      (c0 r K U / (2 * U * (1 / (n : ℝ)))) ^ r * (n / r : ℕ) ^ (r + 1) := by
    rw [hroot, mul_pow]
    have hc0 : 0 ≤ (c0 r K U / (2 * U)) ^ r := by positivity
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (n : ℝ) / (2 * r)) hfloor (r + 1)
    have hh := mul_le_mul_of_nonneg_left hp
      (mul_nonneg hc0 (pow_nonneg hn0.le r))
    apply le_trans (le_of_eq ?_) hh
    dsimp [δ, samplingOmegaConstant]
    rw [show 2 * r + 1 = r + (r + 1) by omega, pow_add (n : ℝ) r (r + 1),
      div_pow (n : ℝ) (2 * (r : ℝ)) (r + 1)]
    have hd : (2 * (r : ℝ)) ^ (r + 1) ≠ 0 := by positivity
    generalize (c0 r K U / (2 * U)) ^ r = A
    generalize (2 * (r : ℝ)) ^ (r + 1) = d at hd ⊢
    field_simp
  linarith

/-- The actual algorithmic `Ω(n^(2r+1))` consequence, with explicit constant and threshold.
The scopes are the `n/r` disjoint blocks already represented by `blockPartition`. -/
theorem prop_B1_sampling_omega {n r : ℕ} {K U : ℝ}
    (hr : 1 ≤ r) (hK : 0 < K) (hU : 1 < U)
    (hn : samplingOmegaThreshold r K U ≤ n)
    (A : ValuePolicy (BlockQuery (n / r) r))
    (hcorrect : BlockAccurate A K U (1 / (n : ℝ)))
    (steps : ℕ) (z : ℝ)
    (hhalt : A (valueTranscript A (fun _ => 1) steps) = .inr z) :
    samplingOmegaConstant r K U * (n : ℝ) ^ (2 * r + 1) ≤
      ((valueTranscript A (fun _ => 1) steps).length : ℝ) := by
  have hn2 : 2 * r ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by positivity
  have hm : 1 ≤ n / r := (Nat.le_div_iff_mul_le (by omega : 0 < r)).mpr (by omega)
  have hε1 : 1 / (n : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hn0).mpr
    simpa only [one_mul] using (show (1 : ℝ) ≤ n by exact_mod_cast hn1)
  have hh := prop_B1_adaptive hr hm hK hU (by positivity) hε1 A hcorrect steps z hhalt
  exact (sampling_rhs_ge_power hr hK hU hn).trans hh

/-- The exponent in the Corollary 1.3 notation `r = η + 1` is `2η + 3`. -/
theorem prop_B1_sampling_eta {n η : ℕ} {K U : ℝ}
    (hK : 0 < K) (hU : 1 < U)
    (hn : samplingOmegaThreshold (η + 1) K U ≤ n)
    (A : ValuePolicy (BlockQuery (n / (η + 1)) (η + 1)))
    (hcorrect : BlockAccurate A K U (1 / (n : ℝ)))
    (steps : ℕ) (z : ℝ)
    (hhalt : A (valueTranscript A (fun _ => 1) steps) = .inr z) :
    samplingOmegaConstant (η + 1) K U * (n : ℝ) ^ (2 * η + 3) ≤
      ((valueTranscript A (fun _ => 1) steps).length : ℝ) := by
  have hh := prop_B1_sampling_omega (by omega : 1 ≤ η + 1) hK hU hn A hcorrect steps z hhalt
  convert hh using 1 <;> congr 2 <;> omega

/-- A rational amplitude loses at most a factor two in the fooling mass. -/
lemma rational_amplitude_exists {r : ℕ} {K U : ℝ}
    (hr : 1 ≤ r) (hK : 0 < K) (hU : 1 < U) :
    ∃ a : ℚ, a0 r K U / 2 < (a : ℝ) ∧ (a : ℝ) < a0 r K U := by
  exact exists_rat_btwn (by linarith [a0_pos hr hK hU])

/-- The zero-extended bump evaluated using rational arithmetic and rational comparisons. -/
def compactBumpQ (t : ℚ) : ℚ :=
  if 0 ≤ t ∧ t ≤ 1 then 16 * t ^ 2 * (1 - t) ^ 2 else 0

lemma compactBumpQ_cast (t : ℚ) : (compactBumpQ t : ℝ) = compactBump (t : ℝ) := by
  unfold compactBumpQ compactBump
  by_cases ht : 0 ≤ t ∧ t ≤ 1
  · have htR : (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      change 0 ≤ (t : ℝ) ∧ (t : ℝ) ≤ 1
      exact_mod_cast ht
    rw [if_pos ht, if_pos htR]
    push_cast
    rfl
  · have htR : (t : ℝ) ∉ Set.Icc (0 : ℝ) 1 := by
      change ¬ (0 ≤ (t : ℝ) ∧ (t : ℝ) ≤ 1)
      exact_mod_cast ht
    rw [if_neg ht, if_neg htR]
    norm_cast

/-- A cell bump has a finite rational evaluation program. -/
def gridBumpQ {r L : ℕ} (a : ℚ) (z : GridCell r L) (x : Fin r → ℚ) : ℚ :=
  (a / L) * ∏ j, compactBumpQ ((L : ℚ) * x j - (z j : ℚ))

lemma gridBumpQ_cast {r L : ℕ} (a : ℚ) (z : GridCell r L) (x : Fin r → ℚ) :
    (gridBumpQ a z x : ℝ) = gridBump (a : ℝ) z (fun j => (x j : ℝ)) := by
  unfold gridBumpQ gridBump
  push_cast
  simp_rw [compactBumpQ_cast]
  push_cast
  rfl

/-- Finite concrete data for the completed rational piecewise-polynomial factor.
Its data consists only of a rational amplitude, a natural grid size, and finitely
many active cell indices. Evaluation reads precisely those finite data. -/
structure RationalGridDescription (r : ℕ) where
  amplitude : ℚ
  gridSize : ℕ
  cells : Finset (GridCell r gridSize)

namespace RationalGridDescription

def evalQ {r : ℕ} (d : RationalGridDescription r) (x : Fin r → ℚ) : ℚ :=
  1 + ∑ z ∈ d.cells, gridBumpQ d.amplitude z x

def realize {r : ℕ} (d : RationalGridDescription r) (x : Fin r → ℝ) : ℝ :=
  1 + ∑ z ∈ d.cells, gridBump (d.amplitude : ℝ) z x

/-- The rational program computes the actual real function exactly at every rational point. -/
theorem evalQ_cast {r : ℕ} (d : RationalGridDescription r) (x : Fin r → ℚ) :
    (d.evalQ x : ℝ) = d.realize (fun j => (x j : ℝ)) := by
  unfold evalQ realize
  push_cast
  simp_rw [gridBumpQ_cast]

/-- The finite-precision oracle is an explicit dyadic rounding program. -/
def reply {r : ℕ} (d : RationalGridDescription r) (b : ℕ) (x : Fin r → ℚ) : ℚ :=
  Oracle.dyadQ b (d.evalQ x)

theorem reply_binary {r : ℕ} (d : RationalGridDescription r) (b : ℕ) (x : Fin r → ℚ) :
    Oracle.IsBinary (d.reply b x) := Oracle.dyadQ_isBinary _ _

theorem reply_error {r : ℕ} (d : RationalGridDescription r) (b : ℕ) (x : Fin r → ℚ) :
    |(d.reply b x : ℝ) - d.realize (fun j => (x j : ℝ))| ≤ (2 : ℝ) ^ (-(b : ℝ)) := by
  rw [← d.evalQ_cast x]
  exact Oracle.abs_dyadQ_sub_le _ _

/-- Encode the exact active-cell set of the previously proved grid adversary. -/
def ofQueries {r : ℕ} (a : ℚ) (queries : Finset (Fin r → ℝ)) : RationalGridDescription r :=
  ⟨a, foolingGridSize r queries.card,
    activeGridCells (L := foolingGridSize r queries.card) queries⟩

lemma ofQueries_realize {r : ℕ} (a : ℚ) (queries : Finset (Fin r → ℝ)) :
    (ofQueries a queries).realize = fun x => 1 +
      foolingBump (L := foolingGridSize r queries.card) (a : ℝ) queries x := rfl

lemma ofQueries_at_query {r : ℕ} (a : ℚ) (queries : Finset (Fin r → ℝ))
    {x : Fin r → ℝ} (hx : x ∈ queries) : (ofQueries a queries).realize x = 1 := by
  rw [ofQueries_realize]
  change 1 + foolingBump (L := foolingGridSize r queries.card) (a : ℝ) queries x = 1
  rw [foolingBump_at_query _ _ hx, add_zero]

lemma dyadQ_one (b : ℕ) : Oracle.dyadQ b 1 = 1 := by
  unfold Oracle.dyadQ
  have hp : (2 : ℚ) ^ b = ((2 : ℤ) ^ b : ℚ) := by norm_cast
  rw [one_mul, hp, ← Int.cast_pow, Int.floor_intCast]
  exact div_self (by positivity)

/-- Actual finite-precision replies on all rational queried points are exactly one. -/
theorem ofQueries_reply_at_query {r : ℕ} (a : ℚ) (queries : Finset (Fin r → ℝ))
    (b : ℕ) {x : Fin r → ℚ} (hx : (fun j => (x j : ℝ)) ∈ queries) :
    (ofQueries a queries).reply b x = 1 := by
  have heq := (ofQueries a queries).evalQ_cast x
  rw [ofQueries_at_query a queries hx] at heq
  have hQ : (ofQueries a queries).evalQ x = 1 := by exact_mod_cast heq
  unfold reply
  rw [hQ, dyadQ_one]

lemma ofQueries_contDiff {r : ℕ} (a : ℚ) (queries : Finset (Fin r → ℝ)) :
    ContDiff ℝ 1 (ofQueries a queries).realize :=
  contDiff_const.add (contDiff_foolingBump _ _)

/-- The rational description satisfies the actual paper range and Euclidean Lipschitz promises. -/
theorem ofQueries_promises {r : ℕ} {K U : ℝ} (hr : 1 ≤ r) (hK : 0 < K) (hU : 1 < U)
    {a : ℚ} (ha : 0 ≤ (a : ℝ)) (haA : (a : ℝ) ≤ a0 r K U)
    (queries : Finset (Fin r → ℝ)) :
    (∀ x ∈ Integral.cube r, 1 ≤ (ofQueries a queries).realize x ∧
      (ofQueries a queries).realize x ≤ U) ∧
      (LocalFunc.mk (ofQueries a queries).realize).LipLe K := by
  have hs : 0 < 8 * Real.sqrt (r : ℝ) := by positivity
  have hLip : 8 * (a : ℝ) * Real.sqrt r ≤ K := by
    have hh := (le_div_iff₀ hs).mp (haA.trans (a0_le_K_div r K U))
    nlinarith
  constructor
  · intro x _
    exact foolingFactor_range ha (haA.trans (a0_le_U_sub_one r K U))
      (foolingGridSize_pos r queries.card) queries x
  · intro x y _ _
    change |(1 + _) - (1 + _)| ≤ _
    rw [add_sub_add_left_eq_sub]
    exact (foolingBump_euclidean_lipschitz ha (foolingGridSize_pos r queries.card) queries x y).trans
      (mul_le_mul_of_nonneg_right hLip (norm_nonneg _))

/-- Choosing the amplitude above `a0/2` retains half the original actual integral mass. -/
theorem ofQueries_mass {r : ℕ} {K U : ℝ} (hr : 1 ≤ r) (hK : 0 < K) (hU : 1 < U)
    {a : ℚ} (ha : a0 r K U / 2 < (a : ℝ)) (queries : Finset (Fin r → ℝ)) :
    (c0 r K U / 2) * ((queries.card : ℝ) + 1) ^ negInvR r ≤
      Integral.cubeIntegral (fun x => (ofQueries a queries).realize x - 1) := by
  have ha0 : 0 < (a : ℝ) := by linarith [a0_pos hr hK hU]
  have hm := cubeIntegral_foolingBump_ge (foolingGridSize_pos r queries.card) ha0.le queries
    (foolingGridSize_count hr)
  have hc := mu_bound_core hr (show 1 ≤ queries.card + 1 by omega) ha0 (J_pos r)
    (Nat.le_ceil _) (ceil_two_rpow_le (queries.card + 1) r (by omega) hr)
  have hμ := hc.trans hm
  have haJ : c0 r K U / 2 ≤ (a : ℝ) * J r / 6 := by
    unfold c0
    nlinarith [J_pos r]
  have hh := (mul_le_mul_of_nonneg_right haJ
    (Real.rpow_nonneg (by positivity : 0 ≤ ((queries.card + 1 : ℕ) : ℝ)) (negInvR r))).trans hμ
  simpa only [ofQueries_realize, add_sub_cancel_left, Nat.cast_add, Nat.cast_one] using hh

end RationalGridDescription

/-- A finite-precision query names a factor, a rational point, and the requested number of bits. -/
structure FiniteValueQuery (m r : ℕ) where
  factor : Fin m
  point : Fin r → ℚ
  bits : ℕ

def FiniteValueQuery.realQuery {m r : ℕ} (q : FiniteValueQuery m r) : BlockQuery m r :=
  (q.factor, fun j => (q.point j : ℝ))

/-- Ordinary universal accuracy for binary finite-precision value access. The reply
routine is quantified explicitly, including its actual binary and error promises. -/
def FiniteBlockAccurate {m r : ℕ} (A : ValuePolicy (FiniteValueQuery m r)) (K U ε : ℝ) : Prop :=
  ∀ ψ : BlockFactors m r, BlockPromises K U ψ →
    ∀ answer : FiniteValueQuery m r → ℚ,
      (∀ q, Oracle.IsBinary (answer q) ∧
        |(answer q : ℝ) - ψ q.factor (fun j => (q.point j : ℝ))| ≤
          (2 : ℝ) ^ (-(q.bits : ℝ))) →
      ∀ n z, A (valueTranscript A (fun q => (answer q : ℝ)) n) = .inr z →
        0 < z ∧ |Real.log (z / blockPartition ψ)| ≤ ε

lemma a0_for_amplitude {r : ℕ} (hr : 1 ≤ r) {a : ℝ} (ha : a ≤ 1) :
    a0 r (8 * Real.sqrt r * a) (1 + a) = a := by
  have hs : (8 * Real.sqrt (r : ℝ)) ≠ 0 := by positivity
  have hdiv : (8 * Real.sqrt (r : ℝ) * a) / (8 * Real.sqrt r) = a := by field_simp
  unfold a0
  rw [show 1 + a - 1 = a by ring, hdiv, min_eq_left ha, min_self]

/-- A genuine finite-precision adaptive lower bound. The adversary's responses
are the concrete dyadic program on finite rational polynomial data, and its
response at every actual baseline query is proved to equal one at every precision. -/
theorem prop_B1_finite_precision {m r : ℕ} {K U ε : ℝ}
    (hr : 1 ≤ r) (hm : 1 ≤ m) (hK : 0 < K) (hU : 1 < U)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (a : ℚ)
    (ha0 : 0 < (a : ℝ)) (haA : (a : ℝ) ≤ a0 r K U)
    (A : ValuePolicy (FiniteValueQuery m r)) (hcorrect : FiniteBlockAccurate A K U ε)
    (n : ℕ) (z : ℝ) (hhalt : A (valueTranscript A (fun _ => 1) n) = .inr z) :
    ((valueTranscript A (fun _ => 1) n).length : ℝ) ≥
      (((a : ℝ) * J r / 6) / (2 * (1 + (a : ℝ)) * ε)) ^ r *
        (m : ℝ) ^ (r + 1) - m := by
  classical
  let qs : Finset (BlockQuery m r) := (allOneQueries A n).image FiniteValueQuery.realQuery
  let N : Fin m → ℕ := fun e => (factorQuerySet qs e).card
  let d : Fin m → RationalGridDescription r := fun e =>
    RationalGridDescription.ofQueries a (factorQuerySet qs e)
  let ψ : BlockFactors m r := fun e => (d e).realize
  let answer : FiniteValueQuery m r → ℚ := fun q => (d q.factor).reply q.bits q.point
  let μ : Fin m → ℝ := fun e => Integral.cubeIntegral
    (foolingBump (L := foolingGridSize r (N e)) (a : ℝ) (factorQuerySet qs e))
  let Kq : ℝ := 8 * Real.sqrt r * (a : ℝ)
  let Uq : ℝ := 1 + (a : ℝ)
  have hKq : 0 < Kq := by dsimp [Kq]; positivity
  have hUq : 1 < Uq := by dsimp [Uq]; linarith
  have ha1 : (a : ℝ) ≤ 1 := haA.trans (a0_le_one r K U)
  have hcq : c0 r Kq Uq = (a : ℝ) * J r / 6 := by
    unfold c0
    rw [show a0 r Kq Uq = (a : ℝ) from a0_for_amplitude hr ha1]
  have hψ : BlockPromises K U ψ := by
    intro e
    exact ⟨RationalGridDescription.ofQueries_contDiff a _,
      RationalGridDescription.ofQueries_promises hr hK hU ha0.le haA _⟩
  have hInt (e : Fin m) : IntegrableOn
      (foolingBump (L := foolingGridSize r (N e)) (a : ℝ) (factorQuerySet qs e))
      (Integral.cube r) := by
    apply Integral.integrableOn_cube_of_bound (contDiff_foolingBump _ _).continuous.measurable
    intro x _
    rw [abs_of_nonneg (foolingBump_nonneg ha0.le _ _)]
    exact foolingBump_le ha0.le _ _
  have hμ0 (e : Fin m) : 0 ≤ μ e :=
    Integral.le_cubeIntegral (hInt e) (fun x _ => foolingBump_nonneg ha0.le _ x)
  have hμU (e : Fin m) : μ e ≤ Uq - 1 := by
    apply Integral.cubeIntegral_le (hInt e)
    intro x _
    have hh := foolingBump_le (L := foolingGridSize r (N e)) ha0.le (factorQuerySet qs e) x
    have hdiv : (a : ℝ) / foolingGridSize r (N e) ≤ a :=
      div_le_self ha0.le (by exact_mod_cast foolingGridSize_pos r (N e))
    exact hh.trans (by dsimp [Uq]; linarith)
  have hμmass (e : Fin m) : c0 r Kq Uq * ((N e : ℝ) + 1) ^ negInvR r ≤ μ e := by
    have hh := (mu_bound_core hr (show 1 ≤ N e + 1 by omega) ha0 (J_pos r)
      (Nat.le_ceil _) (ceil_two_rpow_le (N e + 1) r (by omega) hr)).trans
        (cubeIntegral_foolingBump_ge (foolingGridSize_pos r (N e)) ha0.le
          (factorQuerySet qs e) (foolingGridSize_count hr))
    simpa only [hcq, Nat.cast_add, Nat.cast_one] using hh
  have hZ : blockPartition ψ = ∏ e, (1 + μ e) := by
    rw [blockPartition_eq_prod]
    apply Finset.prod_congr rfl
    intro e _
    change Integral.cubeIntegral (fun x => 1 + foolingBump
      (L := foolingGridSize r (N e)) (a : ℝ) (factorQuerySet qs e) x) = 1 + μ e
    rw [Integral.cubeIntegral_add (integrableOn_const (Integral.volume_cube_lt_top r).ne) (hInt e),
      Integral.cubeIntegral_const]
  have hZpos : 0 < blockPartition ψ := by
    rw [hZ]
    exact Finset.prod_pos fun e _ => by linarith [hμ0 e]
  have hbaseline : BlockPromises (m := m) (r := r) K U (fun _ _ => 1) := by
    intro e
    refine ⟨contDiff_const, fun _ _ => ⟨le_refl _, hU.le⟩, ?_⟩
    intro x y _ _
    simp only [sub_self, abs_zero]
    positivity
  have h₀ := hcorrect (fun _ _ => 1) hbaseline (fun _ => 1)
    (fun q => ⟨Oracle.isBinary_one, by simp⟩) n z (by simpa using hhalt)
  have hAnswers (q : FiniteValueQuery m r) : Oracle.IsBinary (answer q) ∧
      |(answer q : ℝ) - ψ q.factor (fun j => (q.point j : ℝ))| ≤
        (2 : ℝ) ^ (-(q.bits : ℝ)) :=
    ⟨(d q.factor).reply_binary q.bits q.point, (d q.factor).reply_error q.bits q.point⟩
  have hOne (q : FiniteValueQuery m r) (hq : q ∈ allOneQueries A n) : (answer q : ℝ) = 1 := by
    have hreal : q.realQuery ∈ qs := Finset.mem_image.mpr ⟨q, hq, rfl⟩
    have hx := factorQuerySet_mem.mpr hreal
    have hh := RationalGridDescription.ofQueries_reply_at_query a
      (factorQuerySet qs q.factor) q.bits hx
    change ((d q.factor).reply q.bits q.point : ℝ) = 1
    exact_mod_cast hh
  have haltψ : A (valueTranscript A (fun q => (answer q : ℝ)) n) = .inr z :=
    same_output_of_allOneQueries A n _ hOne hhalt
  have h₁ := hcorrect ψ hψ answer hAnswers n z haltψ
  have hgap := common_output_forces_log_gap h₀.1 (show 0 < blockPartition
    (fun _ : Fin m => fun _ : Fin r → ℝ => 1) by rw [blockPartition_one]; norm_num) hZpos h₀.2 h₁.2
  rw [blockPartition_one, Real.log_one, sub_zero] at hgap
  have hlog : Real.log (blockPartition ψ) ≤ 2 * ε := (le_abs_self _).trans hgap
  have hterms (e : Fin m) : (c0 r Kq Uq / Uq) * ((N e : ℝ) + 1) ^ negInvR r ≤
      Real.log (1 + μ e) := by
    calc
      _ = (c0 r Kq Uq * ((N e : ℝ) + 1) ^ negInvR r) / Uq := by ring
      _ ≤ μ e / Uq := div_le_div_of_nonneg_right (hμmass e) (by dsimp [Uq]; linarith)
      _ ≤ Real.log (1 + μ e) := log_one_add_ge_div_U (hμ0 e) hUq.le (hμU e)
  have hsumlog := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hterms e)
  rw [← Finset.mul_sum, ← Real.log_prod Finset.univ (fun e => 1 + μ e)
    (fun e _ => (show 0 < 1 + μ e by linarith [hμ0 e]).ne'), ← hZ] at hsumlog
  have hcount := prop_B1 hr hm hKq hUq hε0 hε1 N
    (show (∑ e, (N e : ℝ)) = (qs.card : ℝ) by
      rw [← Nat.cast_sum]; exact_mod_cast sum_factorQuerySet_card qs)
    (hsumlog.trans hlog)
  rw [hcq] at hcount
  have hcard : qs.card ≤ (valueTranscript A (fun _ => 1) n).length := by
    apply Finset.card_image_le.trans
    letI : DecidableEq (FiniteValueQuery m r) := Classical.decEq _
    have hh := List.toFinset_card_le ((valueTranscript A (fun _ => 1) n).map Prod.fst)
    simpa only [allOneQueries, List.length_map] using hh
  exact hcount.trans (by exact_mod_cast hcard)

/-- The finite-precision model therefore has a positive lower-bound constant
fixed solely by `r`, `K`, and `U`; the rational amplitude is chosen before the algorithm. -/
theorem finite_precision_lower_constant_exists {r : ℕ} {K U : ℝ}
    (hr : 1 ≤ r) (hK : 0 < K) (hU : 1 < U) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ) (ε : ℝ), 1 ≤ m → 0 < ε → ε ≤ 1 →
      ∀ (A : ValuePolicy (FiniteValueQuery m r)), FiniteBlockAccurate A K U ε →
      ∀ (n : ℕ) (z : ℝ), A (valueTranscript A (fun _ => 1) n) = .inr z →
        ((valueTranscript A (fun _ => 1) n).length : ℝ) ≥
          (c / (2 * U * ε)) ^ r * (m : ℝ) ^ (r + 1) - m := by
  obtain ⟨a, haHalf, haA⟩ := rational_amplitude_exists hr hK hU
  have ha0 : 0 < (a : ℝ) := by linarith [a0_pos hr hK hU]
  have hJ := J_pos r
  have hU0 : 0 < U := by linarith
  let c : ℝ := (a : ℝ) * J r / 6
  refine ⟨c, by dsimp [c]; positivity, ?_⟩
  intro m ε hm hε0 hε1 A hcorrect n z hhalt
  have hh := prop_B1_finite_precision hr hm hK hU hε0 hε1 a ha0 haA.le A hcorrect n z hhalt
  have hUa : 1 + (a : ℝ) ≤ U := by linarith [haA.trans_le (a0_le_U_sub_one r K U)]
  have hdiv : c / (2 * U * ε) ≤ c / (2 * (1 + (a : ℝ)) * ε) := by
    apply div_le_div_of_nonneg_left (by dsimp [c]; positivity) (by positivity)
    nlinarith
  have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by dsimp [c]; positivity) hdiv r)
    (pow_nonneg (Nat.cast_nonneg m) (r + 1))
  exact (sub_le_sub_right hp m).trans hh

end Paper08.LowerBound
