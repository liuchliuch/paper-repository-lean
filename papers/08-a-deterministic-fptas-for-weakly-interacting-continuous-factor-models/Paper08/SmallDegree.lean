import Paper08.Appendix

/-!
Actual product perturbation and component-accuracy estimates used in Appendix A.
The functions and component integrals occur in the conclusions; these are not
nonnegativity assertions about the numerical error majorants.
-/

noncomputable section
open scoped BigOperators

namespace Paper08.SmallDegree

theorem abs_product_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) {U : ℝ}
    (hU : 0 ≤ U) (hf : ∀ i ∈ s, |f i| ≤ U) :
    |∏ i ∈ s, f i| ≤ U ^ s.card := by
  rw [Finset.abs_prod]
  calc
    ∏ i ∈ s, |f i| ≤ ∏ _i ∈ s, U :=
      Finset.prod_le_prod (fun _ _ => abs_nonneg _) hf
    _ = U ^ s.card := by simp

/-- Telescoping a bounded product gives the error used for both Lipschitz
functions and finite-precision oracle samples in Appendix A. -/
theorem product_perturbation {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f g : ι → ℝ) {U δ : ℝ}
    (hU : 0 ≤ U) (hδ : 0 ≤ δ)
    (hf : ∀ i ∈ s, |f i| ≤ U) (hg : ∀ i ∈ s, |g i| ≤ U)
    (he : ∀ i ∈ s, |f i - g i| ≤ δ) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ s.card * U ^ (s.card - 1) * δ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfs : ∀ i ∈ s, |f i| ≤ U := fun i hi => hf i (by simp [hi])
    have hgs : ∀ i ∈ s, |g i| ≤ U := fun i hi => hg i (by simp [hi])
    have hes : ∀ i ∈ s, |f i - g i| ≤ δ := fun i hi => he i (by simp [hi])
    have hfa := hf a (by simp)
    have hea := he a (by simp)
    have hp := abs_product_le s g hU hgs
    have hi := ih hfs hgs hes
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have heq : f a * (∏ i ∈ s, f i) - g a * ∏ i ∈ s, g i =
        f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) +
          (f a - g a) * ∏ i ∈ s, g i := by ring
    rw [heq]
    have htri := abs_add_le (f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i))
      ((f a - g a) * ∏ i ∈ s, g i)
    simp only [abs_mul] at htri
    have hfirst : |f a| * |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤
        U * (s.card * U ^ (s.card - 1) * δ) :=
      mul_le_mul hfa hi (abs_nonneg _) hU
    have hsecond : |f a - g a| * |∏ i ∈ s, g i| ≤ δ * U ^ s.card :=
      mul_le_mul hea hp (abs_nonneg _) hδ
    have halg : U * (s.card * U ^ (s.card - 1) * δ) + δ * U ^ s.card =
        (s.card + 1 : ℕ) * U ^ ((s.card + 1) - 1) * δ := by
      by_cases hs : s.card = 0
      · simp [hs]
      · have hc : s.card = (s.card - 1) + 1 := by omega
        have hpow : U ^ s.card = U ^ (s.card - 1) * U := by
          conv_lhs => rw [hc, pow_succ]
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
        rw [hpow]
        ring
    linarith

/-- Product Lipschitz estimate, with a common metric distance represented by d. -/
theorem product_lipschitz {ι : Type*} [DecidableEq ι] {X : Type*}
    (s : Finset ι) (f : ι → X → ℝ) (x y : X) {U K d : ℝ}
    (hU : 0 ≤ U) (hK : 0 ≤ K) (hd : 0 ≤ d)
    (hx : ∀ i ∈ s, |f i x| ≤ U) (hy : ∀ i ∈ s, |f i y| ≤ U)
    (hlip : ∀ i ∈ s, |f i x - f i y| ≤ K * d) :
    |(∏ i ∈ s, f i x) - ∏ i ∈ s, f i y| ≤
      (s.card * K * U ^ (s.card - 1)) * d := by
  have h := product_perturbation s (fun i => f i x) (fun i => f i y)
    hU (mul_nonneg hK hd) hx hy hlip
  convert h using 1 <;> ring

/-- Passing from approximations of component integrals to the final product
costs at most the sum of their absolute errors because every integral is ≥1. -/
theorem component_log_error {ι : Type*} (s : Finset ι) (I Ihat : ι → ℝ)
    (hI : ∀ i ∈ s, 1 ≤ I i) (hIhat : ∀ i ∈ s, 1 ≤ Ihat i) :
    |Real.log (∏ i ∈ s, Ihat i) - Real.log (∏ i ∈ s, I i)| ≤
      ∑ i ∈ s, |Ihat i - I i| := by
  rw [Real.log_prod s Ihat (fun i hi => ne_of_gt (lt_of_lt_of_le zero_lt_one (hIhat i hi))),
    Real.log_prod s I (fun i hi => ne_of_gt (lt_of_lt_of_le zero_lt_one (hI i hi))),
    ← Finset.sum_sub_distrib]
  calc
    |∑ i ∈ s, (Real.log (Ihat i) - Real.log (I i))| ≤
        ∑ i ∈ s, |Real.log (Ihat i) - Real.log (I i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, |Ihat i - I i| := Finset.sum_le_sum fun i hi =>
      Paper08.log_abs_sub_le_abs_sub (hIhat i hi) (hI i hi)

theorem component_accuracy {ι : Type*} (s : Finset ι) (I Ihat : ι → ℝ)
    {n : ℕ} {ε : ℝ} (hn : 0 < n) (hcard : s.card ≤ n) (hε : 0 ≤ ε)
    (hI : ∀ i ∈ s, 1 ≤ I i) (hIhat : ∀ i ∈ s, 1 ≤ Ihat i)
    (herr : ∀ i ∈ s, |Ihat i - I i| ≤ ε / n) :
    |Real.log (∏ i ∈ s, Ihat i) - Real.log (∏ i ∈ s, I i)| ≤ ε := by
  apply (component_log_error s I Ihat hI hIhat).trans
  calc
    ∑ i ∈ s, |Ihat i - I i| ≤ ∑ _i ∈ s, ε / n := Finset.sum_le_sum herr
    _ = s.card * (ε / n) := by simp
    _ ≤ n * (ε / n) := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      (div_nonneg hε (by positivity))
    _ = ε := by field_simp

end Paper08.SmallDegree
