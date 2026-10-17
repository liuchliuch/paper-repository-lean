import Paper14.ConditionalSieveRemainder
import Paper14.SievePrimeTailBound
import Paper14.CoordinateBounds

open MeasureTheory Set Function Filter Finset
namespace Paper14
noncomputable section

/-- The actual common-prime majorant from the pointwise union bound. -/
def sieveRemainderMajorant (P Q : ℕ) (ε : ℝ) : ℝ × ℝ → ℝ := fun z =>
  ∑ ℓ ∈ Finset.range (Q+1), if P < ℓ ∧ Nat.Prime ℓ then
    ∑ q ∈ Finset.range Q, if ℓ ∣ q+1 then
      (divisibleBandSingle ℓ ε (((q+1 : ℕ) : ℝ)*z.2-z.1) : ℝ) else 0
  else 0

lemma divisibleBandSingle_le_one (ℓ : ℕ) (ε u : ℝ) : divisibleBandSingle ℓ ε u ≤ 1 := by
  unfold divisibleBandSingle
  split_ifs <;> omega

lemma measurable_sieveRemainderMajorant (P Q : ℕ) (ε : ℝ) :
    Measurable (sieveRemainderMajorant P Q ε) := by
  unfold sieveRemainderMajorant
  apply Finset.measurable_sum
  intro ℓ hℓ
  by_cases hp : P < ℓ ∧ Nat.Prime ℓ
  · simp only [if_pos hp]
    apply Finset.measurable_sum
    intro q hq
    by_cases hd : ℓ ∣ q+1
    · simp only [if_pos hd]
      have hn : Measurable (fun z : ℝ × ℝ => divisibleBandSingle ℓ ε (((q+1 : ℕ) : ℝ)*z.2-z.1)) :=
        (measurable_divisibleBandSingle ℓ ε).comp (by fun_prop)
      exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hn
    · simp only [if_neg hd]
      exact measurable_const
  · simp only [if_neg hp]
    exact measurable_const

lemma sieveRemainderMajorant_mem_Icc (P Q : ℕ) (ε : ℝ) (z : ℝ × ℝ) :
    sieveRemainderMajorant P Q ε z ∈ Icc (0 : ℝ) ((Q+1 : ℕ)*Q : ℕ) := by
  have hterm (ℓ q : ℕ) :
      (if ℓ ∣ q+1 then (divisibleBandSingle ℓ ε (((q+1 : ℕ) : ℝ)*z.2-z.1) : ℝ) else 0) ∈ Icc (0 : ℝ) 1 := by
    split_ifs
    · exact ⟨Nat.cast_nonneg _,by exact_mod_cast divisibleBandSingle_le_one ℓ ε _⟩
    · exact ⟨le_rfl,zero_le_one⟩
  have hinner (ℓ : ℕ) :
      (if P < ℓ ∧ Nat.Prime ℓ then ∑ q ∈ Finset.range Q,
        if ℓ ∣ q+1 then (divisibleBandSingle ℓ ε (((q+1 : ℕ) : ℝ)*z.2-z.1) : ℝ) else 0
       else 0) ∈ Icc (0 : ℝ) Q := by
    split_ifs
    · refine ⟨Finset.sum_nonneg (fun q _ => (hterm ℓ q).1),?_⟩
      calc _ ≤ ∑ _q ∈ Finset.range Q, (1 : ℝ) := Finset.sum_le_sum (fun q _ => (hterm ℓ q).2)
           _ = _ := by simp
    · exact ⟨le_rfl,Nat.cast_nonneg _⟩
  refine ⟨Finset.sum_nonneg (fun ℓ _ => (hinner ℓ).1),?_⟩
  calc _ ≤ ∑ _ℓ ∈ Finset.range (Q+1), (Q : ℝ) := Finset.sum_le_sum (fun ℓ _ => (hinner ℓ).2)
       _ = _ := by simp

lemma integral_sieveRemainderMajorant_unit (P Q : ℕ) (c : ℝ)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ θ in Ioc (0 : ℝ) 1, sieveRemainderMajorant P Q ε (c,θ)) ≤ ε*(Q : ℝ)*SP P := by
  let R : ℕ → ℝ → ℝ := fun ℓ θ =>
    if P < ℓ ∧ Nat.Prime ℓ then
      ∑ q ∈ Finset.range Q, if ℓ ∣ q+1 then
        (divisibleBandSingle ℓ ε (((q+1 : ℕ) : ℝ)*θ-c) : ℝ) else 0 else 0
  have hRi (ℓ : ℕ) : IntegrableOn (R ℓ) (Ioc (0 : ℝ) 1) := by
    dsimp only [R]
    split_ifs
    · apply integrable_finset_sum
      intro q hq
      split_ifs
      · exact integrable_divisible_single_unit ℓ (q+1) c ε
      · exact integrable_zero _ _ _
    · exact integrable_zero _ _ _
  have heq : (∫ θ in Ioc (0 : ℝ) 1, sieveRemainderMajorant P Q ε (c,θ)) =
      ∑ ℓ ∈ Finset.range (Q+1), if P < ℓ ∧ Nat.Prime ℓ then
        ((Q/ℓ : ℕ) : ℝ)*(ε/(ℓ : ℝ)) else 0 := by
    change (∫ θ in Ioc (0 : ℝ) 1, ∑ ℓ ∈ Finset.range (Q+1), R ℓ θ) = _
    rw [integral_finset_sum _ (fun ℓ _ => hRi ℓ)]
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    dsimp only [R]
    by_cases hp : P < ℓ ∧ Nat.Prime ℓ
    · simp only [if_pos hp]
      exact integral_divisible_index_sum hp.2.pos Q c hε0 hε1
    · simp only [if_neg hp,integral_zero]
  rw [heq]
  exact prime_mean_sum_le P Q hε0

lemma GM_cast_le_Q (M Q : ℕ) (c θ ε : ℝ) (hε : ε ≤ 1) : (GM M Q c θ ε : ℝ) ≤ Q := by
  rw [GM_cast_sum_nat M Q c θ ε hε]
  calc _ ≤ ∑ _q ∈ Finset.range Q, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        exact_mod_cast sieveSingle_le_one M ((q+1 : ℕ) : ℤ) ε (((q+1 : ℕ) : ℝ)*θ-c)
       _ = _ := by simp

/-- Full original unsieved residual expectation (19), under the actual
normalized area measure m, with no additional factor from c integration. -/
theorem integral_sieve_residual (P Q : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ x, ((GM (primorial P) Q (cOf x) (thetaOf x) ε : ℝ)-
      (GPrim Q (cOf x) (thetaOf x) ε : ℝ)) ∂m) ≤ ε*(Q : ℝ)*SP P := by
  let f : ℝ × ℝ → ℝ := sieveRemainderMajorant P Q ε
  have hfn : ∀ z, 0 ≤ f z := fun z => (sieveRemainderMajorant_mem_Icc P Q ε z).1
  have hfb : ∀ z, ‖f z‖ ≤ ((Q+1 : ℕ)*Q : ℕ) := by
    intro z
    rw [Real.norm_eq_abs,abs_of_nonneg (hfn z)]
    exact (sieveRemainderMajorant_mem_Icc P Q ε z).2
  have hbound := integral_farey_of_uniform_conditional_bound f (measurable_sieveRemainderMajorant P Q ε)
    hfn _ hfb (mul_nonneg (mul_nonneg hε0 (Nat.cast_nonneg _)) (SP_nonneg P))
    (fun c hc => integral_sieveRemainderMajorant_unit P Q c hε0 hε1)
  have hcoord : Measurable (fun x : ℝ × ℝ => (cOf x,thetaOf x)) := by
    unfold cOf thetaOf
    fun_prop
  have hfm : Integrable (fun x => f (cOf x,thetaOf x)) m :=
    integrable_of_measurable_bound ((measurable_sieveRemainderMajorant P Q ε).comp hcoord) _ (fun x => hfb _)
  have hG (M : ℕ) : Measurable (fun z : ℝ × ℝ => (GM M Q z.1 z.2 ε : ℝ)) := by
    have hn := measurable_GM M Q hε1
    exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hn
  have hGc (M : ℕ) : Measurable (fun x : ℝ × ℝ => (GM M Q (cOf x) (thetaOf x) ε : ℝ)) := by
    change Measurable ((fun z : ℝ × ℝ => (GM M Q z.1 z.2 ε : ℝ)) ∘
      (fun x : ℝ × ℝ => (cOf x,thetaOf x)))
    exact (hG M).comp hcoord
  have hdiffMeas : Measurable (fun x => (GM (primorial P) Q (cOf x) (thetaOf x) ε : ℝ)-
      (GPrim Q (cOf x) (thetaOf x) ε : ℝ)) := by
    have heq : (fun x : ℝ × ℝ => (GM (primorial P) Q (cOf x) (thetaOf x) ε : ℝ)-
        (GPrim Q (cOf x) (thetaOf x) ε : ℝ)) =
        (fun x => (GM (primorial P) Q (cOf x) (thetaOf x) ε : ℝ)-
        (GM 0 Q (cOf x) (thetaOf x) ε : ℝ)) := by
      funext x
      rw [GPrim_eq_GM_zero]
    rw [heq]
    exact (hGc (primorial P)).sub (hGc 0)
  have hdiffI : Integrable (fun x => (GM (primorial P) Q (cOf x) (thetaOf x) ε : ℝ)-
      (GPrim Q (cOf x) (thetaOf x) ε : ℝ)) m := by
    apply integrable_of_measurable_bound hdiffMeas (Q : ℝ)
    intro x
    rw [Real.norm_eq_abs]
    have hM := GM_cast_le_Q (primorial P) Q (cOf x) (thetaOf x) ε hε1
    have hP : (GPrim Q (cOf x) (thetaOf x) ε : ℝ) ≤ Q := by
      rw [GPrim_eq_GM_zero]
      exact GM_cast_le_Q 0 Q (cOf x) (thetaOf x) ε hε1
    have hM0 : (0 : ℝ) ≤ (GM (primorial P) Q (cOf x) (thetaOf x) ε : ℝ) := Nat.cast_nonneg _
    have hP0 : (0 : ℝ) ≤ (GPrim Q (cOf x) (thetaOf x) ε : ℝ) := Nat.cast_nonneg _
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  apply le_trans (integral_mono hdiffI hfm (fun x => GM_remainder_le_prime_sum P Q (cOf x) (thetaOf x) ε hε1)) hbound

end
end Paper14
