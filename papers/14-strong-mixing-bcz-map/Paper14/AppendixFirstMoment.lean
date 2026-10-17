import Paper14.AppendixFirstGeometry
import Paper14.AppendixCountBasic

open MeasureTheory Set Finset Filter
open scoped ENNReal
open Classical
namespace Paper14
noncomputable section

lemma appendix_strip_sum_le_count {n : ℕ} (hn : 6 ≤ n) {α : ℝ} (hα : 0 < α) (hαs : α < 1/32)
    (x : ℝ × ℝ) :
    ∑ pq ∈ appendixPairs n, (appendixLowerStrip (1-α/(n : ℝ)) pq.1 pq.2).indicator (fun _ => (1 : ℝ)) x
      ≤ (ZCount n α x : ℝ) := by
  let S := (appendixPairs n).filter (fun pq => x ∈ appendixLowerStrip (1-α/(n : ℝ)) pq.1 pq.2)
  let f : ℕ × ℕ → ℤ × ℤ := fun pq => (pq.1,pq.2)
  have hinj : Function.Injective f := by
    intro a b h
    apply Prod.ext
    · exact_mod_cast (show (a.1 : ℤ) = (b.1 : ℤ) from congrArg Prod.fst h)
    · exact_mod_cast (show (a.2 : ℤ) = (b.2 : ℤ) from congrArg Prod.snd h)
  have hcard : S.card ≤ ZCount n α x := by
    apply Finset.card_le_card_of_injOn f
    · intro pq hpq
      obtain ⟨hpair,hx⟩ := Finset.mem_filter.mp hpq
      have hgeom := (appendix_lowerStrip_subset hn hα hαs hpair hx).2
      obtain ⟨hmem,hcop⟩ := Finset.mem_filter.mp hpair
      obtain ⟨hp,hq⟩ := Finset.mem_product.mp hmem
      simp only [Finset.mem_Ioc] at hp hq
      change f pq ∈ (Finset.Icc (-(4*n : ℤ)) (4*n) ×ˢ Finset.Icc (1 : ℤ) (2*n)).filter _
      apply Finset.mem_filter.mpr
      refine ⟨?_,hgeom⟩
      simp only [f,Finset.mem_product,Finset.mem_Icc]
      have hpn : pq.1 ≤ n := hp.2.trans (Nat.div_le_self n 3)
      have hq0 : 0 < pq.2 := by omega
      constructor <;> constructor <;> omega
    · exact hinj.injOn
  have heq : ∑ pq ∈ appendixPairs n,
      (appendixLowerStrip (1-α/(n : ℝ)) pq.1 pq.2).indicator (fun _ => (1 : ℝ)) x = (S.card : ℝ) := by
    simp only [S,Finset.card_eq_sum_ones,Finset.sum_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
      Set.indicator_apply]
  rw [heq]
  exact_mod_cast hcard

lemma appendix_firstMoment_lower {n : ℕ} (hn : 6 ≤ n) {α : ℝ} (hα : 0 < α) (hαs : α < 1/32) :
    (coprimePairCount n : ℝ)*((α/(n : ℝ))/(4*(n : ℝ))) ≤
      ∫ x in appendixAr (1-α/(n : ℝ)), (ZCount n α x : ℝ) ∂m := by
  let r := 1-α/(n : ℝ)
  have hstrip (pq : ℕ × ℕ) :
      Integrable ((appendixLowerStrip r pq.1 pq.2).indicator (fun _ => (1 : ℝ)))
        (m.restrict (appendixAr r)) :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_appendixLowerStrip _ _ _)
  have hsum := integral_mono (integrable_finset_sum _ (fun pq _ => hstrip pq))
    (integrable_ZCount n α (m.restrict (appendixAr r))) (appendix_strip_sum_le_count hn hα hαs)
  rw [integral_finset_sum _ (fun pq _ => hstrip pq)] at hsum
  have heq (pq : ℕ × ℕ) (hpq : pq ∈ appendixPairs n) :
      (∫ x in appendixAr r, (appendixLowerStrip r pq.1 pq.2).indicator (fun _ => (1 : ℝ)) x ∂m) =
        (m (appendixLowerStrip r pq.1 pq.2)).toReal := by
    have hsub : appendixLowerStrip r pq.1 pq.2 ⊆ appendixAr r :=
      fun x hx => (appendix_lowerStrip_subset hn hα hαs hpq hx).1
    rw [setIntegral_indicator (measurableSet_appendixLowerStrip _ _ _),inter_eq_right.mpr hsub,
      setIntegral_const]
    simp [Measure.real]
  rw [Finset.sum_congr rfl (fun pq hpq => heq pq hpq)] at hsum
  calc
    _ = ∑ pq ∈ appendixPairs n, (α/(n : ℝ))/(4*(n : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul,appendixPairs_card]
    _ ≤ ∑ pq ∈ appendixPairs n, (m (appendixLowerStrip r pq.1 pq.2)).toReal :=
      Finset.sum_le_sum (fun pq hpq => appendix_lowerStrip_measure hn hα hαs hpq)
    _ ≤ _ := hsum

/-- The genuine first moment (24), for the original Z count and original normalized Farey measure. -/
theorem appendix_firstMoment (α : ℝ) (hα : 0 < α) (hαs : α < 1/32) :
    ∀ᶠ n : ℕ in atTop, α/80 ≤
      ∫ x in appendixAr (1-α/(n : ℝ)), (ZCount n α x : ℝ) ∂m := by
  obtain ⟨N,hN⟩ := coprimeCountLower
  filter_upwards [eventually_ge_atTop (max N 6)] with n hn
  have hn6 : 6 ≤ n := (le_max_right N 6).trans hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlow := appendix_firstMoment_lower hn6 hα hαs
  have hcount := hN n ((le_max_left N 6).trans hn)
  calc
    α/80 = ((n : ℝ)^2/20)*((α/(n : ℝ))/(4*(n : ℝ))) := by field_simp [hnR.ne']; ring
    _ ≤ (coprimePairCount n : ℝ)*((α/(n : ℝ))/(4*(n : ℝ))) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ ≤ _ := hlow

end
end Paper14
