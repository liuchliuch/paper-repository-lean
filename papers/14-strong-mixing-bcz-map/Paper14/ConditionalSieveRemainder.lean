import Paper14.PrimeSieveRemainder

open MeasureTheory Function Set Filter Finset
namespace Paper14
noncomputable section

lemma integrable_single_unit (M : ℕ) (q : ℤ) (c ε : ℝ) :
    IntegrableOn (fun θ : ℝ => (sieveSingle M q ε ((q : ℝ)*θ-c) : ℝ)) (Ioc (0 : ℝ) 1) := by
  letI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  have hn : Measurable (fun θ : ℝ => sieveSingle M q ε ((q : ℝ)*θ-c)) :=
    (measurable_sieveSingle M q ε).comp (by fun_prop)
  apply integrable_of_measurable_bound ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hn) 1
  intro θ
  dsimp only [Function.comp_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast sieveSingle_le_one M q ε ((q : ℝ)*θ-c)

lemma integrable_divisible_single_unit (ℓ q : ℕ) (c ε : ℝ) :
    IntegrableOn (fun θ : ℝ => (divisibleBandSingle ℓ ε ((q : ℝ)*θ-c) : ℝ)) (Ioc (0 : ℝ) 1) := by
  letI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  have hn : Measurable (fun θ : ℝ => divisibleBandSingle ℓ ε ((q : ℝ)*θ-c)) :=
    (measurable_divisibleBandSingle ℓ ε).comp (by fun_prop)
  apply integrable_of_measurable_bound ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hn) 1
  intro θ
  dsimp only [Function.comp_apply]
  unfold divisibleBandSingle
  split_ifs <;> norm_num

/-- For a fixed common prime divisor, exactly floor(Q/ell) vertical
indices contribute, each with conditional mean epsilon/ell. -/
theorem integral_divisible_index_sum {ℓ : ℕ} (hℓ : 0 < ℓ) (Q : ℕ) (c : ℝ)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ θ in Ioc (0 : ℝ) 1, ∑ q ∈ Finset.range Q,
      if ℓ ∣ q+1 then (divisibleBandSingle ℓ ε (((q+1 : ℕ) : ℝ)*θ-c) : ℝ) else 0) =
      ((Q/ℓ : ℕ) : ℝ)*(ε/(ℓ : ℝ)) := by
  have hqi (q : ℕ) : IntegrableOn (fun θ : ℝ =>
      if ℓ ∣ q+1 then (divisibleBandSingle ℓ ε (((q+1 : ℕ) : ℝ)*θ-c) : ℝ) else 0) (Ioc (0 : ℝ) 1) := by
    split_ifs
    · exact integrable_divisible_single_unit ℓ (q+1) c ε
    · exact integrable_zero _ _ _
  rw [integral_finset_sum _ (fun q _ => hqi q)]
  have hsingle (q : ℕ) : (∫ θ in Ioc (0 : ℝ) 1,
      if ℓ ∣ q+1 then (divisibleBandSingle ℓ ε (((q+1 : ℕ) : ℝ)*θ-c) : ℝ) else 0) =
      if ℓ ∣ q+1 then ε/(ℓ : ℝ) else 0 := by
    by_cases hd : ℓ ∣ q+1
    · simp only [if_pos hd]
      have hk : 0 < (q+1)/ℓ := Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos q) hd) hℓ
      have heq : ℓ*((q+1)/ℓ) = q+1 := Nat.mul_div_cancel' hd
      simpa only [heq] using integral_divisible_band hℓ hk c hε0 hε1
    · simp only [if_neg hd,integral_zero]
  simp_rw [hsingle]
  rw [← Finset.sum_filter,Finset.sum_const,Nat.card_multiples,nsmul_eq_mul]

/-- The actual sieve remainder has a conditional first-moment bound
uniform in c, before summing the prime tail. -/
theorem integral_GM_remainder_prime_bound (P Q : ℕ) (c : ℝ)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ θ in Ioc (0 : ℝ) 1,
      ((GM (primorial P) Q c θ ε : ℝ)-(GPrim Q c θ ε : ℝ))) ≤
      ∑ ℓ ∈ Finset.range (Q+1), if P < ℓ ∧ Nat.Prime ℓ then
        ((Q/ℓ : ℕ) : ℝ)*(ε/(ℓ : ℝ)) else 0 := by
  let R : ℕ → ℝ → ℝ := fun ℓ θ =>
    if P < ℓ ∧ Nat.Prime ℓ then
      ∑ q ∈ Finset.range Q, if ℓ ∣ q+1 then
        (divisibleBandSingle ℓ ε (((q+1 : ℕ) : ℝ)*θ-c) : ℝ) else 0
    else 0
  have hR (ℓ : ℕ) : IntegrableOn (R ℓ) (Ioc (0 : ℝ) 1) := by
    dsimp only [R]
    split_ifs
    · apply integrable_finset_sum
      intro q hq
      split_ifs
      · exact integrable_divisible_single_unit ℓ (q+1) c ε
      · exact integrable_zero _ _ _
    · exact integrable_zero _ _ _
  have hleft : IntegrableOn (fun θ => (GM (primorial P) Q c θ ε : ℝ)-(GPrim Q c θ ε : ℝ)) (Ioc (0 : ℝ) 1) := by
    have heq : (fun θ : ℝ => (GM (primorial P) Q c θ ε : ℝ)-(GPrim Q c θ ε : ℝ)) =
        (fun θ => ∑ q ∈ Finset.range Q,
          ((sieveSingle (primorial P) ((q+1 : ℕ) : ℤ) ε (((q+1 : ℕ) : ℝ)*θ-c) : ℝ)-
           (sieveSingle 0 ((q+1 : ℕ) : ℤ) ε (((q+1 : ℕ) : ℝ)*θ-c) : ℝ))) := by
      funext θ
      rw [GM_cast_sum_nat _ Q c θ ε hε1,GPrim_cast_sum_nat Q c θ ε hε1,Finset.sum_sub_distrib]
    rw [heq]
    apply integrable_finset_sum
    intro q hq
    have h1 := integrable_single_unit (primorial P) ((q+1 : ℕ) : ℤ) c ε
    have h0 := integrable_single_unit 0 ((q+1 : ℕ) : ℤ) c ε
    simp only [Int.cast_natCast] at h1 h0
    exact h1.sub h0
  calc
    _ ≤ ∫ θ in Ioc (0 : ℝ) 1, ∑ ℓ ∈ Finset.range (Q+1), R ℓ θ :=
      integral_mono hleft (integrable_finset_sum _ (fun ℓ _ => hR ℓ))
        (fun θ => GM_remainder_le_prime_sum P Q c θ ε hε1)
    _ = _ := by
      rw [integral_finset_sum _ (fun ℓ _ => hR ℓ)]
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      dsimp only [R]
      by_cases hp : P < ℓ ∧ Nat.Prime ℓ
      · simp only [if_pos hp]
        exact integral_divisible_index_sum hp.2.pos Q c hε0 hε1
      · simp only [if_neg hp,integral_zero]

end
end Paper14
