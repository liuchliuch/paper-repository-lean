import Paper08.FPTASAlgorithm
import Paper08.BitComplexity

/-!
# Oracle queries of the executable FPTAS program

The instrumentation below traverses the same finite sums and the same uncached
recurrence as the rational program. Its value component is proved equal to
`FPTASAlgorithm.run`; no bound on the output or its cost is assumed.
-/

open scoped BigOperators

namespace Paper08.FPTASCost
open PrimitiveMomentsQ FPTASAlgorithm

/-- Queries in the actual sparse primitive grid loops. -/
def primitiveQueries {n m : ℕ} (scopes : Fin m → Finset (Fin n))
    (d : Fin m →₀ ℕ) (s C : ℕ) (τ : ℚ) : ℕ :=
  RationalQuadrature.queryCalls
    (fun i : Fin d.support.card => scopes (d.support.orderEmbOfFin rfl i))
    (Oracle.totalLevelChoice s C τ)

/-- Queries in the actual multinomial moment sum. -/
def momentQueries {n m : ℕ} (scopes : Fin m → Finset (Fin n))
    (B : Finset (Fin m)) (j s C : ℕ) (τ : ℚ) : ℕ :=
  if j = 0 then 0 else
    ∑ d ∈ Finset.finsuppAntidiag B j, primitiveQueries scopes d s C τ

/-- The local recurrence instrumented with every executed moment query. -/
def localCoeffWithCost {n m : ℕ} (scopes : Fin m → Finset (Fin n)) (query : Queries scopes)
    (B : Finset (Fin m)) (j s C : ℕ) (τ : ℚ) : ℚ × ℕ :=
  BitComplexity.rationalLogCoeffQueryCost
    (fun i => (momentQ scopes query B i s C τ, momentQueries scopes B i s C τ)) j

/-- Instrumented support-extraction loops. -/
def logApproxWithCost {n m : ℕ} (scopes : Fin m → Finset (Fin n)) (query : Queries scopes)
    (r c s C : ℕ) (τ : ℚ) : ℚ × ℕ :=
  (∑ p ∈ Finset.Icc 1 s, ∑ AB ∈ pairs scopes r c s p,
      (-1 : ℚ) ^ (AB.1.card - AB.2.card) * (localCoeffWithCost scopes query AB.2 p s C τ).1,
    ∑ p ∈ Finset.Icc 1 s, ∑ AB ∈ pairs scopes r c s p,
      (localCoeffWithCost scopes query AB.2 p s C τ).2)

/-- The complete instrumented program. Final exponentiation invokes no
factor value queries. -/
def runWithCost {n m : ℕ} (fixed : Parameters.Fixed) (scopes : Fin m → Finset (Fin n))
    (query : Queries scopes) (r c : ℕ) (ε : ℚ) : ℚ × ℕ :=
  if m = 0 then (1, 0) else
    let L := logApproxWithCost scopes query r c (Parameters.truncationOrder fixed m ε)
      fixed.C (Parameters.primitiveTolerance fixed m ε)
    (Algorithm.rationalExp L.1 ε, L.2)

@[simp] theorem localCoeffWithCost_value {n m : ℕ} (scopes : Fin m → Finset (Fin n))
    (query : Queries scopes) (B : Finset (Fin m)) (j s C : ℕ) (τ : ℚ) :
    (localCoeffWithCost scopes query B j s C τ).1 = localCoeff scopes query B j s C τ :=
  BitComplexity.rationalLogCoeffQueryCost_value _ j

@[simp] theorem logApproxWithCost_value {n m : ℕ} (scopes : Fin m → Finset (Fin n))
    (query : Queries scopes) (r c s C : ℕ) (τ : ℚ) :
    (logApproxWithCost scopes query r c s C τ).1 = logApprox scopes query r c s C τ := by
  simp only [logApproxWithCost, logApprox, localCoeffWithCost_value]

/-- The instrumented program computes exactly the original program's answer. -/
@[simp] theorem runWithCost_value {n m : ℕ} (fixed : Parameters.Fixed)
    (scopes : Fin m → Finset (Fin n)) (query : Queries scopes) (r c : ℕ) (ε : ℚ) :
    (runWithCost fixed scopes query r c ε).1 = run fixed scopes query r c ε := by
  simp only [runWithCost, run]
  split_ifs <;> simp only [logApproxWithCost_value]

/-- Common upper bound for a primitive grid query loop. -/
def primitiveQueryBound (r s J : ℕ) : ℕ := 2 * s * 2 ^ ((r + 1) * J + s)

lemma primitiveQueries_le {n m r s C : ℕ} (scopes : Fin m → Finset (Fin n))
    (hscopes : ∀ e, (scopes e).card ≤ r) (d : Fin m →₀ ℕ) (hd : d.degree ≤ s) (τ : ℚ) :
    primitiveQueries scopes d s C τ ≤ primitiveQueryBound r s (Oracle.totalLevelChoice s C τ) := by
  have ht : d.support.card ≤ s := (Support.finsupp_support_card_le_degree d).trans hd
  have h := RationalQuadrature.queryCalls_bound_pow (J := Oracle.totalLevelChoice s C τ)
    (fun i : Fin d.support.card => scopes (d.support.orderEmbOfFin rfl i)) (fun i => hscopes _)
  apply h.trans
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 ht)
    (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.add_le_add_left ht _))

/-- Query bound for the actual degree-`j` moment enumeration. -/
theorem momentQueries_le {n m r s C j : ℕ} (scopes : Fin m → Finset (Fin n))
    (hscopes : ∀ e, (scopes e).card ≤ r) (B : Finset (Fin m))
    (hB : B.card ≤ s) (hj : j ≤ s) (τ : ℚ) :
    momentQueries scopes B j s C τ ≤
      4 ^ s * primitiveQueryBound r s (Oracle.totalLevelChoice s C τ) := by
  unfold momentQueries
  split_ifs with hj0
  · omega
  · have hterm : ∀ d ∈ Finset.finsuppAntidiag B j,
        primitiveQueries scopes d s C τ ≤ primitiveQueryBound r s (Oracle.totalLevelChoice s C τ) := by
      intro d hd
      have hh := (Finset.mem_finsuppAntidiag'.mp hd).1
      have hdeg : d.degree ≤ s := by
        change (∑ e ∈ d.support, d e) = j at hh
        change (∑ e ∈ d.support, d e) ≤ s
        omega
      exact primitiveQueries_le scopes hscopes d hdeg τ
    calc
      _ ≤ ∑ _d ∈ Finset.finsuppAntidiag B j,
          primitiveQueryBound r s (Oracle.totalLevelChoice s C τ) := Finset.sum_le_sum hterm
      _ = (Finset.finsuppAntidiag B j).card *
          primitiveQueryBound r s (Oracle.totalLevelChoice s C τ) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (TupleCount.card_finsuppAntidiag_le B hB hj)

/-- The actual uncached local-coefficient program, including repeated moment
calls, has the expected exponential-in-order query cost. -/
theorem localCoeffWithCost_queries_le {n m r s C j : ℕ} (scopes : Fin m → Finset (Fin n))
    (hscopes : ∀ e, (scopes e).card ≤ r) (query : Queries scopes)
    (B : Finset (Fin m)) (hB : B.card ≤ s) (hj : j ≤ s) (τ : ℚ) :
    (localCoeffWithCost scopes query B j s C τ).2 ≤
      (4 ^ s * primitiveQueryBound r s (Oracle.totalLevelChoice s C τ)) * 2 ^ (s + 1) := by
  have h := BitComplexity.rationalLogCoeffQueryCost_queries_le
    (fun i => (momentQ scopes query B i s C τ, momentQueries scopes B i s C τ)) s j
    (4 ^ s * primitiveQueryBound r s (Oracle.totalLevelChoice s C τ)) hj
    (fun i _ hi => momentQueries_le scopes hscopes B hB hi τ)
  exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 0 < 2)
    (Nat.add_le_add_right hj 1)))

/-- The actual support/degree loops have a proved total query count. -/
theorem logApproxWithCost_queries_le {n m r c s C : ℕ} (scopes : Fin m → Finset (Fin n))
    (hscopes : ∀ e, (scopes e).card ≤ r) (query : Queries scopes) (τ : ℚ) :
    (logApproxWithCost scopes query r c s C τ).2 ≤
      s * (m * (8 * degreeBound r c) ^ s) *
        ((4 ^ s * primitiveQueryBound r s (Oracle.totalLevelChoice s C τ)) * 2 ^ (s + 1)) := by
  let U := (4 ^ s * primitiveQueryBound r s (Oracle.totalLevelChoice s C τ)) * 2 ^ (s + 1)
  unfold logApproxWithCost
  dsimp only
  calc
    _ ≤ ∑ _p ∈ Finset.Icc 1 s, (m * (8 * degreeBound r c) ^ s) * U := by
      apply Finset.sum_le_sum
      intro p hp
      calc
        _ ≤ ∑ _AB ∈ pairs scopes r c s p, U := by
          apply Finset.sum_le_sum
          intro AB hAB
          have hb := pair_subset scopes hAB
          exact localCoeffWithCost_queries_le scopes hscopes query AB.2
            ((Finset.card_le_card hb.1).trans hb.2) (Finset.mem_Icc.mp hp).2 τ
        _ = (pairs scopes r c s p).card * U := by simp
        _ ≤ _ := Nat.mul_le_mul_right U (pairs_card scopes)
    _ = _ := by simp [U]; ring

/-- An elementary power-of-two envelope for the complete support/degree loops. -/
theorem logApproxWithCost_queries_two_pow {n m r c s C : ℕ} (scopes : Fin m → Finset (Fin n))
    (hscopes : ∀ e, (scopes e).card ≤ r) (query : Queries scopes) (τ : ℚ) :
    (logApproxWithCost scopes query r c s C τ).2 ≤
      m * 2 ^ ((r + 1) * Oracle.totalLevelChoice s C τ +
        ((8 * degreeBound r c).size + 6) * s + 2) := by
  have h := logApproxWithCost_queries_le (s := s) (C := C) scopes hscopes query (c := c) τ
  have hs : s ≤ 2 ^ s := s.lt_two_pow_self.le
  have hb : 8 * degreeBound r c ≤ 2 ^ (8 * degreeBound r c).size :=
    (Nat.lt_size_self _).le
  apply h.trans
  unfold primitiveQueryBound
  have hfac : s * (m * (8 * degreeBound r c) ^ s) *
      ((4 ^ s * (2 * s * 2 ^ ((r + 1) * Oracle.totalLevelChoice s C τ + s))) * 2 ^ (s + 1)) ≤
      (2 ^ s) * (m * (2 ^ (8 * degreeBound r c).size) ^ s) *
      ((4 ^ s * (2 * (2 ^ s) * 2 ^ ((r + 1) * Oracle.totalLevelChoice s C τ + s))) * 2 ^ (s + 1)) := by
    gcongr
  apply hfac.trans_eq
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
  ring_nf


/-- Fixed coefficient in the linear total-level bound. -/
def levelSlope (p : Parameters.Fixed) : ℕ :=
  2 * (Parameters.budgetBaseLog p + Parameters.momentBaseLog p + 2) + 6

/-- Fixed exponent converting all local loop costs to an exponential in `s`. -/
def querySlope (p : Parameters.Fixed) (r c : ℕ) : ℕ :=
  (r + 1) * levelSlope p + (8 * degreeBound r c).size + 6

/-- Fixed polynomial degree for the complete actual oracle-query procedure. -/
def queryDegree (p : Parameters.Fixed) (r c : ℕ) : ℕ :=
  Parameters.truncationBlock p * (Parameters.truncationOffset p + 1) * querySlope p r c + 1

lemma level_le_slope (p : Parameters.Fixed) {m : ℕ} {ε : ℚ} (hm : 1 ≤ m) (hε : 0 < ε) :
    Parameters.level p m ε ≤ levelSlope p * Parameters.truncationOrder p m ε := by
  apply (Parameters.level_le p hm hε).trans
  have hs := Parameters.truncationOrder_pos p m ε
  unfold Parameters.levelBound Parameters.toleranceExponent levelSlope
  nlinarith

/-- A polynomial query bound for the exact costed program, obtained by
substituting the computed parameters into its counted loops. -/
theorem runWithCost_queries_polynomial {n m r c : ℕ} (p : Parameters.Fixed)
    (scopes : Fin m → Finset (Fin n)) (hscopes : ∀ e, (scopes e).card ≤ r)
    (query : Queries scopes) (ε : ℚ) (hε : 0 < ε) (hεu : ε ≤ 1) :
    ((runWithCost p scopes query r c ε).2 : ℚ) ≤
      (4 * (((m + 1 : ℕ) : ℚ) / ε)) ^ queryDegree p r c := by
  by_cases hm : m = 0
  · simp only [runWithCost, if_pos hm]
    positivity
  have hmp : 1 ≤ m := by omega
  let s := Parameters.truncationOrder p m ε
  let D := Parameters.truncationBlock p * (Parameters.truncationOffset p + 1)
  let H := querySlope p r c
  let X : ℚ := ((m + 1 : ℕ) : ℚ) / ε
  have hX : 1 ≤ X := by
    apply (le_div_iff₀ hε).mpr
    have hm1 : (1 : ℚ) ≤ ((m + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    linarith
  have hmx : (m : ℚ) ≤ X := by
    apply (le_div_iff₀ hε).mpr
    have hh := mul_le_mul_of_nonneg_left hεu (Nat.cast_nonneg m : (0 : ℚ) ≤ m)
    have hm1 : (m : ℚ) ≤ ((m + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.le_succ m
    simp only [mul_one] at hh
    exact hh.trans hm1
  have hJ := level_le_slope p hmp hε
  have he : (r + 1) * Parameters.level p m ε + ((8 * degreeBound r c).size + 6) * s + 2 ≤
      H * s + 2 := by
    have hh := Nat.mul_le_mul_left (r + 1) hJ
    dsimp only [H, querySlope, s]
    nlinarith
  have hcost := logApproxWithCost_queries_two_pow (s := s) (C := p.C) (c := c)
    scopes hscopes query (Parameters.primitiveTolerance p m ε)
  have hcost' : (runWithCost p scopes query r c ε).2 ≤ m * 2 ^ (H * s + 2) := by
    rw [runWithCost, if_neg hm]
    exact hcost.trans (Nat.mul_le_mul_left m (Nat.pow_le_pow_right (by decide : 0 < 2) he))
  have hpower : (2 : ℚ) ^ s ≤ (4 * X) ^ D := Parameters.two_pow_order_le p hε hεu
  have hpoly : ((m * 2 ^ (H * s + 2) : ℕ) : ℚ) ≤ (4 * X) ^ (D * H + 1) := by
    calc
      _ = (4 * (m : ℚ)) * ((2 : ℚ) ^ s) ^ H := by
        push_cast
        simp only [pow_add, pow_mul]
        ring
      _ ≤ (4 * X) * ((4 * X) ^ D) ^ H := by gcongr
      _ = _ := by rw [← pow_mul, pow_succ]; ring
  have hcQ : ((runWithCost p scopes query r c ε).2 : ℚ) ≤
      ((m * 2 ^ (H * s + 2) : ℕ) : ℚ) := by exact_mod_cast hcost'
  apply hcQ.trans
  simpa only [queryDegree, D, H] using hpoly

/-- Bounded occurrence gives the variable-count polynomial bound without an
additional dynamic parameter in the polynomial degree. -/
theorem runWithCost_queries_variables {n m r c : ℕ} (p : Parameters.Fixed)
    (scopes : Fin m → Finset (Fin n)) (hscopes : ∀ e, (scopes e).card ≤ r)
    (hoccurrence : m ≤ c * n) (query : Queries scopes) (ε : ℚ)
    (hε : 0 < ε) (hεu : ε ≤ 1) :
    ((runWithCost p scopes query r c ε).2 : ℚ) ≤
      (4 * ((c + 1 : ℕ) : ℚ) * (((n + 1 : ℕ) : ℚ) / ε)) ^ queryDegree p r c := by
  apply (runWithCost_queries_polynomial p scopes hscopes query ε hε hεu).trans
  apply pow_le_pow_left₀ (by positivity)
  have hmn : m + 1 ≤ (c + 1) * (n + 1) := by nlinarith
  have hdiv := div_le_div_of_nonneg_right (by exact_mod_cast hmn :
    ((m + 1 : ℕ) : ℚ) ≤ (((c + 1) * (n + 1) : ℕ) : ℚ)) hε.le
  push_cast at hdiv
  have hh := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℚ) ≤ 4)
  convert hh using 1 <;> push_cast <;> ring

end Paper08.FPTASCost
