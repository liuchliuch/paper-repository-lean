import Paper08.ArithmeticBounds

/-!
# Bounds for exact rational arithmetic

`rationalBits` measures the actual reduced numerator and denominator. The
costed recurrence below counts rational field operations; it does not assert
a machine-level implementation or charge a unit bit cost for those operations.
-/

open scoped BigOperators

namespace Paper08.BitComplexity

/-- Encoding length of a reduced rational, including one sign bit. -/
def rationalBits (q : ℚ) : ℕ := q.num.natAbs.size + q.den.size + 1

/-- Every partial sum of a finite rational sum inherits its common denominator
and a numerator bound. Thus accumulation order does not grow the reduced
representations beyond these bounds. -/
theorem finite_sum_size_le {α : Type*} (S : Finset α) (f : α → ℚ)
    (D U V W : ℕ) (hD : 0 < D) (hDb : D ≤ 2 ^ V)
    (hden : ∀ i ∈ S, (f i).den ∣ D)
    (habs : ∀ i ∈ S, |f i| ≤ (2 : ℚ) ^ U)
    (hcard : S.card ≤ 2 ^ W) :
    (∑ i ∈ S, f i).num.natAbs.size ≤ U + W + V + 1 ∧
      (∑ i ∈ S, f i).den.size ≤ V + 1 := by
  have hd := Moments.rational_sum_den_dvd S f D hden
  have hdenb := (Nat.le_of_dvd hD hd).trans hDb
  have hb : |∑ i ∈ S, f i| ≤ (2 : ℚ) ^ (U + W) := by
    calc
      _ ≤ ∑ i ∈ S, |f i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ S, (2 : ℚ) ^ U := Finset.sum_le_sum habs
      _ = (S.card : ℚ) * (2 : ℚ) ^ U := by simp [nsmul_eq_mul]
      _ ≤ (2 : ℚ) ^ W * (2 : ℚ) ^ U := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; omega
  refine ⟨Moments.rational_num_size_le_of_abs_den_le _ (U + W) V hb hdenb, ?_⟩
  apply Nat.size_le.mpr
  rw [pow_succ]
  have hp : (0 : ℕ) < 2 ^ V := by positivity
  omega

/-- A uniform bit bound for any subset of a finite family, useful both for
recurrence prefix sums and for support-extraction prefix sums. -/
theorem partial_sum_bits_le {α : Type*} (T S : Finset α) (hST : S ⊆ T)
    (f : α → ℚ) (D U V W : ℕ) (hD : 0 < D) (hDb : D ≤ 2 ^ V)
    (hden : ∀ i ∈ T, (f i).den ∣ D)
    (habs : ∀ i ∈ T, |f i| ≤ (2 : ℚ) ^ U)
    (hcard : T.card ≤ 2 ^ W) :
    rationalBits (∑ i ∈ S, f i) ≤ U + W + 2 * V + 3 := by
  have h := finite_sum_size_le S f D U V W hD hDb
    (fun i hi => hden i (hST hi)) (fun i hi => habs i (hST hi))
    ((Finset.card_le_card hST).trans hcard)
  unfold rationalBits
  omega

/-- A costed version of the actual recurrence. The second component counts
the field operations: four per summand, and three for the final division,
multiplication and subtraction. The recurrence may recompute earlier values. -/
def rationalLogCoeffWithCost (M : ℕ → ℚ) (j : ℕ) : ℚ × ℕ :=
  if h : j = 0 then (0, 0) else
    let earlier : Fin j → ℚ × ℕ := fun i => rationalLogCoeffWithCost M i.val
    (M j - (1 / (j : ℚ)) *
        ∑ i : Fin j, (i.val : ℚ) * (earlier i).1 * M (j - i.val),
      3 + ∑ i : Fin j, ((earlier i).2 + 4))
termination_by j
decreasing_by exact i.isLt

/-- The arithmetic operation count associated with that concrete evaluator. -/
def recurrenceOperationCount (j : ℕ) : ℕ :=
  if h : j = 0 then 0 else
    3 + ∑ i : Fin j, (recurrenceOperationCount i.val + 4)
termination_by j
decreasing_by exact i.isLt

/-- The costed program returns exactly the established recurrence output and
its recursively computed operation count. -/
theorem rationalLogCoeffWithCost_spec (M : ℕ → ℚ) (j : ℕ) :
    rationalLogCoeffWithCost M j =
      (Moments.rationalLogCoeff M j, recurrenceOperationCount j) := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    rw [rationalLogCoeffWithCost, Moments.rationalLogCoeff, recurrenceOperationCount]
    split_ifs with hj
    · rfl
    · simp only [ih _ (Fin.isLt _)]

@[simp] theorem recurrenceOperationCount_zero : recurrenceOperationCount 0 = 0 := by
  rw [recurrenceOperationCount]
  simp

lemma recurrenceOperationCount_eq {j : ℕ} (hj : 1 ≤ j) :
    recurrenceOperationCount j =
      3 + ∑ i ∈ Finset.range j, (recurrenceOperationCount i + 4) := by
  rw [recurrenceOperationCount, dif_neg (by omega)]
  rw [Fin.sum_univ_eq_sum_range (fun i => recurrenceOperationCount i + 4)]

lemma recurrenceOperationCount_succ {j : ℕ} (hj : 1 ≤ j) :
    recurrenceOperationCount (j + 1) = 2 * recurrenceOperationCount j + 4 := by
  have heq := recurrenceOperationCount_eq hj
  rw [recurrenceOperationCount_eq (by omega : 1 ≤ j + 1), Finset.sum_range_succ]
  omega

/-- Even without memoization the actual recurrence uses exponentially many
field operations in the truncation order, as permitted by the FPTAS. -/
theorem recurrenceOperationCount_le (j : ℕ) :
    recurrenceOperationCount j + 4 ≤ 2 ^ (j + 4) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    by_cases hj : j = 0
    · subst j
      rw [recurrenceOperationCount_eq (by decide : 1 ≤ 1)]
      norm_num
    · rw [recurrenceOperationCount_succ (by omega : 1 ≤ j),
        show j + 1 + 4 = (j + 4) + 1 by omega, pow_succ]
      omega


/-- The actual number of moment evaluations in the uncached recurrence,
including repeated calls to the same degree. -/
def momentEvaluationCount (j : ℕ) : ℕ :=
  if h : j = 0 then 0 else
    1 + ∑ i : Fin j, (momentEvaluationCount i.val + 1)
termination_by j
decreasing_by exact i.isLt

@[simp] lemma momentEvaluationCount_zero : momentEvaluationCount 0 = 0 := by
  rw [momentEvaluationCount]
  simp

lemma momentEvaluationCount_eq {j : ℕ} (hj : 1 ≤ j) :
    momentEvaluationCount j = 1 + ∑ i ∈ Finset.range j, (momentEvaluationCount i + 1) := by
  rw [momentEvaluationCount, dif_neg (by omega),
    Fin.sum_univ_eq_sum_range (fun i => momentEvaluationCount i + 1)]

lemma momentEvaluationCount_succ {j : ℕ} (hj : 1 ≤ j) :
    momentEvaluationCount (j + 1) = 2 * momentEvaluationCount j + 1 := by
  have he := momentEvaluationCount_eq hj
  rw [momentEvaluationCount_eq (by omega : 1 ≤ j + 1), Finset.sum_range_succ]
  omega

/-- Recomputing moments incurs only an exponential-in-order factor. -/
theorem momentEvaluationCount_le (j : ℕ) : momentEvaluationCount j + 1 ≤ 2 ^ (j + 1) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    by_cases hj : j = 0
    · subst j
      rw [momentEvaluationCount_eq (by decide : 1 ≤ 1)]
      norm_num
    · rw [momentEvaluationCount_succ (by omega : 1 ≤ j),
        show j + 1 + 1 = (j + 1) + 1 by omega, pow_succ]
      omega

/-- A costed lift of the actual recurrence for moments supplied by a query
routine. Its second component sums every executed moment call's query count. -/
def rationalLogCoeffQueryCost (M : ℕ → ℚ × ℕ) (j : ℕ) : ℚ × ℕ :=
  if h : j = 0 then (0, 0) else
    let earlier : Fin j → ℚ × ℕ := fun i => rationalLogCoeffQueryCost M i.val
    ((M j).1 - (1 / (j : ℚ)) *
        ∑ i : Fin j, (i.val : ℚ) * (earlier i).1 * (M (j - i.val)).1,
      (M j).2 + ∑ i : Fin j, ((earlier i).2 + (M (j - i.val)).2))
termination_by j
decreasing_by exact i.isLt

/-- The costed lift returns the same rational value as the original program. -/
theorem rationalLogCoeffQueryCost_value (M : ℕ → ℚ × ℕ) (j : ℕ) :
    (rationalLogCoeffQueryCost M j).1 = Moments.rationalLogCoeff (fun i => (M i).1) j := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    rw [rationalLogCoeffQueryCost, Moments.rationalLogCoeff]
    split_ifs with hj
    · rfl
    · simp only [ih _ (Fin.isLt _)]

/-- Every executed moment query is accounted for, without a caching premise.
The uniform input bound can be instantiated by the finite quadrature loops. -/
theorem rationalLogCoeffQueryCost_queries (M : ℕ → ℚ × ℕ) (s j C : ℕ) (hj : j ≤ s)
    (hM : ∀ k, 1 ≤ k → k ≤ s → (M k).2 ≤ C) :
    (rationalLogCoeffQueryCost M j).2 ≤ C * momentEvaluationCount j := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    by_cases hj0 : j = 0
    · subst j
      rw [rationalLogCoeffQueryCost, momentEvaluationCount]
      simp
    have hjp : 1 ≤ j := by omega
    rw [rationalLogCoeffQueryCost, dif_neg hj0, momentEvaluationCount, dif_neg hj0]
    dsimp only
    have hsum :
        (∑ i : Fin j, ((rationalLogCoeffQueryCost M i.val).2 + (M (j - i.val)).2)) ≤
          ∑ i : Fin j, (C * momentEvaluationCount i.val + C) := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.add_le_add (ih i.val i.isLt (by omega))
        (hM (j - i.val) (by have := i.isLt; omega) (by omega))
    have hm := hM j hjp hj
    calc
      _ ≤ C + ∑ i : Fin j, (C * momentEvaluationCount i.val + C) := Nat.add_le_add hm hsum
      _ = C * (1 + ∑ i : Fin j, (momentEvaluationCount i.val + 1)) := by
        rw [Nat.mul_add, Nat.mul_one, Finset.mul_sum]
        simp only [Nat.mul_add, Nat.mul_one]

/-- Explicit oracle-query envelope for the uncached actual recurrence. -/
theorem rationalLogCoeffQueryCost_queries_le (M : ℕ → ℚ × ℕ) (s j C : ℕ) (hj : j ≤ s)
    (hM : ∀ k, 1 ≤ k → k ≤ s → (M k).2 ≤ C) :
    (rationalLogCoeffQueryCost M j).2 ≤ C * 2 ^ (j + 1) := by
  apply (rationalLogCoeffQueryCost_queries M s j C hj hM).trans
  exact Nat.mul_le_mul_left C (by have := momentEvaluationCount_le j; omega)

/-- The complete reduced numerator/denominator bound for each actual
recurrence output. -/
theorem rationalLogCoeff_bits_le (M : ℕ → ℚ) (P s r J a : ℕ)
    (hden : ∀ i, 1 ≤ i → i ≤ s → (M i).den ∣ Moments.denomBound P s r J)
    (habs : ∀ i, 1 ≤ i → i ≤ s → |M i| ≤ (2 : ℚ) ^ (a * s))
    {j : ℕ} (hj : j ≤ s) :
    rationalBits (Moments.rationalLogCoeff M j) ≤
      ((a + 1) * s * s + s) + 2 * ((P * s + r * J) * s + s ^ 3 + s ^ 2) + 3 := by
  have hn := Moments.rationalLogCoeff_num_size_le M P s r J a hden habs hj
  have hd := Moments.rationalLogCoeff_den_size_le M P s r J hden hj
  unfold rationalBits
  omega


/-- A finite Taylor sum on the scaled interval has magnitude at most two,
uniformly in the chosen degree. -/
theorem expPolynomial_abs_le_two (t : ℚ) (N : ℕ) (ht : |t| ≤ 1 / 2) :
    |Algorithm.expPolynomial t N| ≤ 2 := by
  have hs : (∑ j ∈ Finset.range (N + 1), (1 / 2 : ℚ) ^ j) ≤ 2 := by
    rw [geom_sum_eq (by norm_num : (1 / 2 : ℚ) ≠ 1)]
    apply (div_le_iff_of_neg (by norm_num : (1 / 2 : ℚ) - 1 < 0)).mpr
    linarith [pow_nonneg (by norm_num : (0 : ℚ) ≤ 1 / 2) (N + 1)]
  unfold Algorithm.expPolynomial
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply le_trans _ hs
  apply Finset.sum_le_sum
  intro j _
  rw [abs_div, abs_pow, abs_of_pos (by positivity : (0 : ℚ) < Nat.factorial j)]
  have hf : (1 : ℚ) ≤ Nat.factorial j := by exact_mod_cast Nat.factorial_pos j
  exact (div_le_self (pow_nonneg (abs_nonneg t) _) hf).trans
    (pow_le_pow_left₀ (abs_nonneg t) ht j)

/-- Canonical denominator of the actual finite Taylor program. -/
theorem expPolynomial_den_dvd (t : ℚ) (N : ℕ) :
    (Algorithm.expPolynomial t N).den ∣ t.den ^ N * Nat.factorial N := by
  unfold Algorithm.expPolynomial
  apply Moments.rational_sum_den_dvd
  intro j hj
  have hjN : j ≤ N := by have := Finset.mem_range.mp hj; omega
  have h := Rat.mul_den_dvd (t ^ j) ((Nat.factorial j : ℚ)⁻¹)
  have hd : (t ^ j / (Nat.factorial j : ℚ)).den ∣ t.den ^ j * Nat.factorial j := by
    simpa only [div_eq_mul_inv, Rat.den_pow, Rat.inv_natCast_den_of_pos (Nat.factorial_pos j)] using h
  exact hd.trans (Nat.mul_dvd_mul (pow_dvd_pow t.den hjN) (Nat.factorial_dvd_factorial hjN))

/-- Binary denominator envelope of the finite Taylor sum. -/
theorem expPolynomial_den_le (t : ℚ) (N : ℕ) :
    (Algorithm.expPolynomial t N).den ≤ 2 ^ (t.den.size * N + N ^ 2) := by
  have hD : 0 < t.den ^ N * Nat.factorial N := by positivity
  have hd := Nat.le_of_dvd hD (expPolynomial_den_dvd t N)
  have hden : t.den ≤ 2 ^ t.den.size := (Nat.lt_size_self t.den).le
  have h := Nat.mul_le_mul (Nat.pow_le_pow_left hden N) (Moments.factorial_le_two_pow_square N)
  apply hd.trans
  simpa only [← pow_mul, ← pow_add, pow_two] using h

/-- Actual bit length after the final exact integer power. This bound covers
every intermediate squaring as well, by substituting its smaller exponent. -/
theorem expPolynomial_pow_bits_le (t : ℚ) (N R : ℕ) (ht : |t| ≤ 1 / 2) :
    rationalBits (Algorithm.expPolynomial t N ^ R) ≤
      (2 * (t.den.size * N + N ^ 2) + 1) * R + 3 := by
  let E := t.den.size * N + N ^ 2
  have hden : (Algorithm.expPolynomial t N ^ R).den ≤ 2 ^ (E * R) := by
    rw [Rat.den_pow]
    have hp := Nat.pow_le_pow_left (expPolynomial_den_le t N) R
    simpa only [E, ← pow_mul] using hp
  have habs : |Algorithm.expPolynomial t N ^ R| ≤ (2 : ℚ) ^ R := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (expPolynomial_abs_le_two t N ht) R
  have hn := Moments.rational_num_size_le_of_abs_den_le
    (Algorithm.expPolynomial t N ^ R) R (E * R) habs hden
  have hd : (Algorithm.expPolynomial t N ^ R).den.size ≤ E * R + 1 := by
    apply Nat.size_le.mpr
    rw [pow_succ]
    have hp : 0 < (2 : ℕ) ^ (E * R) := by positivity
    omega
  unfold rationalBits
  change _ ≤ (2 * E + 1) * R + 3
  nlinarith

/-- The degree actually selected for final exponentiation is polynomial in
the accuracy encoding length and the scaling exponent. -/
theorem rationalExp_degree_le (L ε : ℚ) (hε : 0 < ε) :
    Algorithm.exponentialDegree (ε / (12 * (2 : ℚ) ^ Algorithm.exponentialScale L)) ≤
      ε.den.size + Algorithm.exponentialScale L + 4 := by
  let h := Algorithm.exponentialScale L
  have hnum : (1 : ℚ) ≤ (ε.num : ℚ) := by
    exact_mod_cast (show (1 : ℤ) ≤ ε.num by have := Rat.num_pos.mpr hε; omega)
  have hd : (ε.den : ℚ) ≠ 0 := by exact_mod_cast ε.den_ne_zero
  have he := (div_eq_iff hd).mp ε.num_div_den
  have hinv : 1 / ε ≤ (ε.den : ℚ) := by
    apply (div_le_iff₀ hε).mpr
    rw [mul_comm]
    linarith
  have hden : (ε.den : ℚ) ≤ (2 : ℚ) ^ ε.den.size := by
    exact_mod_cast (Nat.lt_size_self ε.den).le
  have htarget : 1 / (ε / (12 * (2 : ℚ) ^ h)) ≤
      (2 : ℚ) ^ (ε.den.size + h + 4) := by
    calc
      _ = 12 * (2 : ℚ) ^ h * (1 / ε) := by field_simp
      _ ≤ 16 * (2 : ℚ) ^ h * (1 / ε) := by gcongr; norm_num
      _ ≤ 16 * (2 : ℚ) ^ h * (2 : ℚ) ^ ε.den.size :=
        mul_le_mul_of_nonneg_left (hinv.trans hden) (by positivity)
      _ = _ := by rw [show (16 : ℚ) = 2 ^ 4 by norm_num, ← pow_add, ← pow_add]; congr 1; omega
  rw [Algorithm.exponentialDegree, Nat.clog_le_iff_le_pow (by decide : 1 < 2), Nat.ceil_le]
  exact_mod_cast htarget

/-- Scaling the rational argument enlarges its denominator encoding by at
most the scaling exponent. -/
theorem rationalExp_scaled_den_size_le (L : ℚ) :
    (L / (2 : ℚ) ^ Algorithm.exponentialScale L).den.size ≤
      L.den.size + Algorithm.exponentialScale L + 1 := by
  let h := Algorithm.exponentialScale L
  have hd := Rat.mul_den_dvd L (((2 : ℚ) ^ h)⁻¹)
  have hinv : (((2 : ℚ) ^ h)⁻¹).den = 2 ^ h := by
    rw [← inv_pow, Rat.den_pow]
    norm_num
  rw [hinv] at hd
  have hden := Nat.le_of_dvd (by positivity : 0 < L.den * 2 ^ h) hd
  have hb : L.den * 2 ^ h ≤ 2 ^ (L.den.size + h) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ (Nat.lt_size_self L.den).le
  have hh : (L / (2 : ℚ) ^ h).den ≤ 2 ^ (L.den.size + h) := by
    simpa only [div_eq_mul_inv] using hden.trans hb
  change (L / (2 : ℚ) ^ h).den.size ≤ L.den.size + h + 1
  apply Nat.size_le.mpr
  rw [pow_succ]
  have hp : 0 < (2 : ℕ) ^ (L.den.size + h) := by positivity
  omega

/-- A direct representation-size bound for the actual final rational output.
All quantities on the right are program inputs or its computed integer
parameters, whose preceding bounds are polynomial. -/
theorem rationalExp_bits_le (L ε : ℚ) :
    let h := Algorithm.exponentialScale L
    let t := L / (2 : ℚ) ^ h
    let N := Algorithm.exponentialDegree (ε / (12 * (2 : ℚ) ^ h))
    rationalBits (Algorithm.rationalExp L ε) ≤
      (2 * (t.den.size * N + N ^ 2) + 1) * (2 ^ h) + 3 := by
  dsimp only [Algorithm.rationalExp]
  exact expPolynomial_pow_bits_le _ _ _ (Algorithm.exponentialScale_bound L)


/-- A polynomial bound on the actual final rational output encoding, in the
encoded argument, accuracy, and an ordinary magnitude bound for the argument. -/
theorem rationalExp_bits_polynomial (L ε : ℚ) (M : ℕ) (hε : 0 < ε)
    (hL : |L| ≤ (M : ℚ)) :
    rationalBits (Algorithm.rationalExp L ε) ≤
      (2 * ((L.den.size + 4 * M + 3) * (ε.den.size + 4 * M + 6) +
        (ε.den.size + 4 * M + 6) ^ 2) + 1) * (4 * M + 2) + 3 := by
  let h := Algorithm.exponentialScale L
  let N := Algorithm.exponentialDegree (ε / (12 * (2 : ℚ) ^ h))
  let t := L / (2 : ℚ) ^ h
  have hpq : ((2 ^ h : ℕ) : ℚ) ≤ (4 * M + 2 : ℕ) := by
    have hh : ((2 ^ h : ℕ) : ℚ) ≤ 4 * |L| + 2 := Algorithm.exponentialScale_power_bound L
    apply hh.trans
    push_cast
    nlinarith
  have hpow : 2 ^ h ≤ 4 * M + 2 := by exact_mod_cast hpq
  have hh : h ≤ 4 * M + 2 := h.lt_two_pow_self.le.trans hpow
  have hN : N ≤ ε.den.size + 4 * M + 6 := by
    have hn := rationalExp_degree_le L ε hε
    dsimp only [N, h]
    omega
  have ht : t.den.size ≤ L.den.size + 4 * M + 3 := by
    have hd := rationalExp_scaled_den_size_le L
    dsimp only [t, h]
    omega
  have hE : t.den.size * N + N ^ 2 ≤
      (L.den.size + 4 * M + 3) * (ε.den.size + 4 * M + 6) +
        (ε.den.size + 4 * M + 6) ^ 2 :=
    Nat.add_le_add (Nat.mul_le_mul ht hN) (Nat.pow_le_pow_left hN 2)
  have hmul := Nat.mul_le_mul
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hE) 1) hpow
  exact (rationalExp_bits_le L ε).trans (Nat.add_le_add_right hmul 3)

end Paper08.BitComplexity
