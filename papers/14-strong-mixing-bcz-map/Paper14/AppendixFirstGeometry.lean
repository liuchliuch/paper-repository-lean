import Paper14.AppendixStripArea
import Paper14.CoprimeAsymptotic

open MeasureTheory Set Function Filter Finset
namespace Paper14
noncomputable section

def appendixPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc (n/6) (n/3) ×ˢ Finset.Ioc ((n-1)/2) n).filter (fun pq => Nat.Coprime pq.1 pq.2)

def appendixAr (r : ℝ) : Set (ℝ × ℝ) := {x ∈ Omega | (1 : ℝ)/2 ≤ x.1 ∧ x.1 ≤ r}

lemma appendixPairs_card (n : ℕ) : (appendixPairs n).card = coprimePairCount n :=
  (coprimePairCount_eq_Ioc n).symm

lemma appendix_scale_bounds {n : ℕ} (hn : 6 ≤ n) {α : ℝ} (hα : 0 < α) (hαs : α < 1/32) :
    0 < 1-α/(n : ℝ) ∧ 1-α/(n : ℝ) < 1 ∧ (1 : ℝ)/8 ≤ (1-α/(n : ℝ))-6/7 := by
  have hn6 : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have he0 := div_pos hα hn0
  have hes : α/(n : ℝ) < 1/56 := by
    apply (div_lt_iff₀ hn0).mpr
    nlinarith
  exact ⟨by linarith,by linarith,by linarith⟩

lemma appendix_pair_constraints {n p q : ℕ} (hn : 6 ≤ n) (hpq : (p,q) ∈ appendixPairs n) :
    0 < p ∧ 0 < q ∧ p+1 ≤ q ∧ q ≤ n ∧ q < 6*p ∧ Nat.Coprime p q := by
  obtain ⟨hmem,hcop⟩ := Finset.mem_filter.mp hpq
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp hmem
  simp only [Finset.mem_Ioc] at hp hq
  exact ⟨by omega,by omega,by omega,hq.2,by omega,hcop⟩

/-- Every point of each actual Appendix A lower strip is in A_r and
contributes its selected primitive vector to the original F_1 count. -/
theorem appendix_lowerStrip_subset {n p q : ℕ} (hn : 6 ≤ n) {α : ℝ} (hα : 0 < α) (hαs : α < 1/32)
    (hpq : (p,q) ∈ appendixPairs n) :
    appendixLowerStrip (1-α/(n : ℝ)) p q ⊆
      {x ∈ appendixAr (1-α/(n : ℝ)) | inZRect n (α/(n : ℝ)) x (p : ℤ) (q : ℤ)} := by
  obtain ⟨hp0,hq0,hpqle,hqn,hq6p,hcop⟩ := appendix_pair_constraints hn hpq
  obtain ⟨hr0,hr1,hrlen⟩ := appendix_scale_bounds hn hα hαs
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
  have hpr : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hpqr : (p : ℝ)+1 ≤ q := by exact_mod_cast hpqle
  have hqnr : (q : ℝ) ≤ n := by exact_mod_cast hqn
  have hq6pr : (q : ℝ) < 6*(p : ℝ) := by exact_mod_cast hq6p
  intro x hx
  obtain ⟨hs,hl,hu⟩ := hx
  have hs0 : 0 < x.1 := by linarith [hs.1]
  have hs1 : x.1 ≤ 1 := hs.2.trans hr1.le
  have hlow : (p : ℝ)*x.1+(1-α/(n : ℝ)) < x.2*(q : ℝ) := (div_lt_iff₀ hqr).mp hl
  have hupp : x.2*(q : ℝ) ≤ (p : ℝ)*x.1+1 := (le_div_iff₀ hqr).mp hu
  have hps : (p : ℝ)*x.1 ≤ p := mul_le_of_le_one_right hpr hs1
  have ht1 : x.2 ≤ 1 := (mul_le_mul_iff_right₀ hqr).mp (by nlinarith)
  have hqps := mul_lt_mul_of_pos_right hq6pr hs0
  have hqs : 6*(q : ℝ) < 7*(q : ℝ)*x.1 := by
    have hh := mul_lt_mul_of_pos_left hs.1 hqr
    nlinarith
  have ht0 : 1-x.1 < x.2 := (mul_lt_mul_iff_right₀ hqr).mp (by nlinarith)
  have hΩ : x ∈ Omega := mem_Omega_iff.mpr ⟨hs0,hs1,ht0,ht1⟩
  refine ⟨⟨hΩ,by linarith [hs.1],hs.2⟩,?_⟩
  change 0 < (q : ℤ) ∧ ((q : ℤ) : ℝ) ≤ 2*n ∧
    1-α/(n : ℝ) < ((q : ℤ) : ℝ)*x.2-((p : ℤ) : ℝ)*x.1 ∧
    ((q : ℤ) : ℝ)*x.2-((p : ℤ) : ℝ)*x.1 ≤ 1 ∧
    0 < ((q : ℤ) : ℝ)/x.1 ∧ ((q : ℤ) : ℝ)/x.1 ≤ 2*n ∧ IsCoprime (p : ℤ) (q : ℤ)
  simp only [Int.cast_natCast]
  have hnss : (n : ℝ) ≤ 2*(n : ℝ)*x.1 := by
    have hh := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (by linarith [hs.1] : (0 : ℝ) ≤ x.1-1/2)
    nlinarith
  exact ⟨by exact_mod_cast hq0,by nlinarith,by nlinarith,by nlinarith,div_pos hqr hs0,
    (div_le_iff₀ hs0).mpr (hqnr.trans hnss),hcop.isCoprime⟩

/-- Each selected strip has the original lower normalized area epsilon/(4n). -/
theorem appendix_lowerStrip_measure {n p q : ℕ} (hn : 6 ≤ n) {α : ℝ} (hα : 0 < α) (hαs : α < 1/32)
    (hpq : (p,q) ∈ appendixPairs n) :
    (α/(n : ℝ))/(4*(n : ℝ)) ≤ (m (appendixLowerStrip (1-α/(n : ℝ)) p q)).toReal := by
  obtain ⟨hp0,hq0,hpqle,hqn,hq6p,hcop⟩ := appendix_pair_constraints hn hpq
  obtain ⟨hr0,hr1,hrlen⟩ := appendix_scale_bounds hn hα hαs
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hqnR : (q : ℝ) ≤ n := by exact_mod_cast hqn
  have hε0 : 0 ≤ α/(n : ℝ) := (div_pos hα hn0).le
  have hsub : appendixLowerStrip (1-α/(n : ℝ)) p q ⊆ Omega := fun x hx => (appendix_lowerStrip_subset hn hα hαs hpq hx).1.1
  rw [m,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply (measurableSet_appendixLowerStrip _ p q),
    inter_eq_self_of_subset_left hsub,volume_appendixLowerStrip hr1.le,
    ENNReal.toReal_mul,ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (mul_nonneg (by linarith [hrlen]) (div_nonneg (sub_nonneg.mpr hr1.le) hqR.le))]
  have heq : 1-(1-α/(n : ℝ)) = α/(n : ℝ) := by ring
  rw [heq]
  calc
    _ = (1/4 : ℝ)*((α/(n : ℝ))/(n : ℝ)) := by ring
    _ ≤ (1/4 : ℝ)*((α/(n : ℝ))/(q : ℝ)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hε0 hqR hqnR) (by norm_num)
    _ ≤ 2*((1-α/(n : ℝ))-6/7)*((α/(n : ℝ))/(q : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith [hrlen]) (div_nonneg hε0 hqR.le)
    _ = _ := by ring

end
end Paper14
