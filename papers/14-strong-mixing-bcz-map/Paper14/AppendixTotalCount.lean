import Paper14.AppendixSecondGeometry
import Mathlib.Data.Finset.Sigma

open MeasureTheory Set Finset
open Classical
namespace Paper14
noncomputable section

def appendixQCount (r : ℝ) (q : ℕ) (x : ℝ × ℝ) : ℕ :=
  ((Finset.range (2*q)).filter (fun p => x ∈ appendixStrip r p q)).card

def appendixTotalCount (n : ℕ) (r : ℝ) (x : ℝ × ℝ) : ℕ :=
  ∑ q ∈ Finset.Icc 1 (4*n),appendixQCount r q x

lemma appendixQCount_real_eq_sum (r : ℝ) (q : ℕ) (x : ℝ × ℝ) :
    (appendixQCount r q x : ℝ) =
      ∑ p ∈ Finset.range (2*q),(appendixStrip r p q).indicator (fun _ => (1 : ℝ)) x := by
  simp only [appendixQCount,Finset.card_eq_sum_ones,Finset.sum_filter,Nat.cast_sum,Nat.cast_ite,
    Nat.cast_one,Nat.cast_zero,Set.indicator_apply]

lemma appendixQCount_le_one {r : ℝ} (hr : (1 : ℝ)/2 < r) (q : ℕ) (x : ℝ × ℝ) :
    appendixQCount r q x ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp p' hp'
  by_contra hpp
  exact Set.disjoint_left.mp (appendix_same_q_disjoint hr hpp)
    (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hp').2

lemma appendixTotalCount_le (n : ℕ) {r : ℝ} (hr : (1 : ℝ)/2 < r) (x : ℝ × ℝ) :
    appendixTotalCount n r x ≤ 4*n := by
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 (4*n),1 := Finset.sum_le_sum (fun q _ => appendixQCount_le_one hr q x)
    _ ≤ 4*n := by simp

lemma measurable_appendixQCount_real (r : ℝ) (q : ℕ) :
    Measurable (fun x : ℝ × ℝ => (appendixQCount r q x : ℝ)) := by
  simp_rw [appendixQCount_real_eq_sum]
  exact Finset.measurable_sum _ (fun p _ => measurable_const.indicator (measurableSet_appendixStrip r p q))

lemma measurable_appendixTotalCount_real (n : ℕ) (r : ℝ) :
    Measurable (fun x : ℝ × ℝ => (appendixTotalCount n r x : ℝ)) := by
  simp only [appendixTotalCount,Nat.cast_sum]
  exact Finset.measurable_sum _ (fun q _ => measurable_appendixQCount_real r q)

/-- The upper strip count genuinely dominates F_2; no height condition was retained. -/
theorem appendix_F2_le_totalCount {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hε : α/(n : ℝ) < 1)
    {x : ℝ × ℝ} (hx : x ∈ appendixAr (1-α/(n : ℝ))) :
    ZCount (2*n) (2*α) x ≤ appendixTotalCount n (1-α/(n : ℝ)) x := by
  let r := 1-α/(n : ℝ)
  let S := (Finset.Icc 1 (4*n)).sigma (fun q => (Finset.range (2*q)).filter (fun p => x ∈ appendixStrip r p q))
  have hcardS : S.card = appendixTotalCount n r x := by rw [Finset.card_sigma]; rfl
  rw [← hcardS]
  let f : ℤ × ℤ → Σ q : ℕ, ℕ := fun pr => ⟨pr.2.toNat,pr.1.toNat⟩
  change ((Finset.Icc (-(4*(2*n) : ℤ)) (4*(2*n)) ×ˢ Finset.Icc (1 : ℤ) (2*(2*n))).filter
    (fun pr => inZRect (2*n) ((2*α)/(2*n : ℕ)) x pr.1 pr.2)).card ≤ S.card
  have heq : (2*α)/(2*n : ℕ) = α/(n : ℝ) := by push_cast; field_simp
  apply Finset.card_le_card_of_injOn f
  · intro pr hpr
    have hrect := (Finset.mem_filter.mp hpr).2
    obtain ⟨hq0,hqu,hp0,hpu⟩ := appendix_F2_coefficients hα hε hx hrect
    have hpNat : (pr.1.toNat : ℤ) = pr.1 := Int.toNat_of_nonneg hp0
    have hqNat : (pr.2.toNat : ℤ) = pr.2 := Int.toNat_of_nonneg (by omega)
    have hqN0 : 1 ≤ pr.2.toNat := by rw [← hqNat] at hq0; exact_mod_cast hq0
    have hqNU : pr.2.toNat ≤ 4*n := by rw [← hqNat] at hqu; exact_mod_cast hqu
    have hpNU : pr.1.toNat < 2*pr.2.toNat := by rw [← hpNat,← hqNat] at hpu; exact_mod_cast hpu
    have hpR : (pr.1.toNat : ℝ) = (pr.1 : ℝ) := by exact_mod_cast hpNat
    have hqR : (pr.2.toNat : ℝ) = (pr.2 : ℝ) := by exact_mod_cast hqNat
    have hstrip : x ∈ appendixStrip r pr.1.toNat pr.2.toNat := by
      refine ⟨hx,?_,?_⟩ <;> rw [hpR,hqR]
      · simpa only [heq] using hrect.2.2.1
      · exact hrect.2.2.2.1
    change (⟨pr.2.toNat,pr.1.toNat⟩ : Σ q : ℕ,ℕ) ∈ S
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hqN0,hqNU⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpNU,hstrip⟩⟩
  · intro pr₁ hpr₁ pr₂ hpr₂ heqf
    obtain ⟨hq₁,hqu₁,hp₁,hpu₁⟩ := appendix_F2_coefficients hα hε hx (Finset.mem_filter.mp hpr₁).2
    obtain ⟨hq₂,hqu₂,hp₂,hpu₂⟩ := appendix_F2_coefficients hα hε hx (Finset.mem_filter.mp hpr₂).2
    have hpNat : pr₁.1.toNat = pr₂.1.toNat := congrArg (fun z : Σ q : ℕ,ℕ => z.2) heqf
    have hqNat : pr₁.2.toNat = pr₂.2.toNat := congrArg (fun z : Σ q : ℕ,ℕ => z.1) heqf
    apply Prod.ext
    · rw [← Int.toNat_of_nonneg hp₁,← Int.toNat_of_nonneg hp₂,hpNat]
    · rw [← Int.toNat_of_nonneg (by omega : 0 ≤ pr₁.2),← Int.toNat_of_nonneg (by omega : 0 ≤ pr₂.2),hqNat]

end
end Paper14
