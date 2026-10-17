import Paper14.AppendixArithmetic

open Finset
open Classical
namespace Paper14
noncomputable section

def pairDet (q q' : ℕ) (pp : ℕ × ℕ) : ℤ := (pp.2 : ℤ)*q-(pp.1 : ℤ)*q'

def determinantPairs (q q' : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (2*q) ×ˢ Finset.range (2*q')).filter
    (fun pp => 0 < pairDet q q' pp ∧ pairDet q q' pp ≤ 4*(q'-q : ℕ))

lemma gcd_dvd_pairDet (q q' : ℕ) (pp : ℕ × ℕ) :
    (Nat.gcd q q' : ℤ) ∣ pairDet q q' pp := by
  have hq : (Nat.gcd q q' : ℤ) ∣ (q : ℤ) := by exact_mod_cast Nat.gcd_dvd_left q q'
  have hq' : (Nat.gcd q q' : ℤ) ∣ (q' : ℤ) := by exact_mod_cast Nat.gcd_dvd_right q q'
  exact dvd_sub (dvd_mul_of_dvd_right hq _) (dvd_mul_of_dvd_right hq' _)

/-- The actual lattice-index bound used between (25) and (26): at most 8Δ pairs. -/
theorem determinantPairs_card_le {q q' : ℕ} (hq : 0 < q) :
    (determinantPairs q q').card ≤ 8*(q'-q) := by
  let d := Nat.gcd q q'
  let a := q/d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left q' hq
  have ha : 0 < a := Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_left q q')) hd
  have hqd : d*a = q := Nat.mul_div_cancel' (Nat.gcd_dvd_left q q')
  let f : ℕ × ℕ → ℕ × ℕ := fun pp => ((pairDet q q' pp).toNat/d,pp.1/a)
  have hcard : (determinantPairs q q').card ≤
      ((Finset.Ioc 0 (4*(q'-q)/d)) ×ˢ Finset.range (2*d)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro pp hpp
      obtain ⟨hmem,hD,hDu⟩ := Finset.mem_filter.mp hpp
      have hDnat : ((pairDet q q' pp).toNat : ℤ) = pairDet q q' pp := Int.toNat_of_nonneg hD.le
      have hDn0 : 0 < (pairDet q q' pp).toNat := by
        rw [← hDnat] at hD
        exact_mod_cast hD
      have hdvd : d ∣ (pairDet q q' pp).toNat := by
        apply Int.natCast_dvd_natCast.mp
        rw [hDnat]
        exact gcd_dvd_pairDet q q' pp
      have hDnU : (pairDet q q' pp).toNat ≤ 4*(q'-q) := by
        rw [← hDnat] at hDu
        exact_mod_cast hDu
      have hp : pp.1 < 2*q := Finset.mem_range.mp (Finset.mem_product.mp hmem).1
      change ((pairDet q q' pp).toNat/d,pp.1/a) ∈
        ((Finset.Ioc 0 (4*(q'-q)/d)) ×ˢ Finset.range (2*d))
      simp only [Finset.mem_product,Finset.mem_Ioc,Finset.mem_range]
      refine ⟨⟨Nat.div_pos (Nat.le_of_dvd hDn0 hdvd) hd,Nat.div_le_div_right hDnU⟩,?_⟩
      apply (Nat.div_lt_iff_lt_mul ha).mpr
      calc
        pp.1 < 2*q := hp
        _ = (2*d)*a := by rw [mul_assoc,hqd]
    · intro pp₁ hpp₁ pp₂ hpp₂ heq
      obtain ⟨hmem₁,hD₁,hDu₁⟩ := Finset.mem_filter.mp hpp₁
      obtain ⟨hmem₂,hD₂,hDu₂⟩ := Finset.mem_filter.mp hpp₂
      have hnat₁ : ((pairDet q q' pp₁).toNat : ℤ) = pairDet q q' pp₁ := Int.toNat_of_nonneg hD₁.le
      have hnat₂ : ((pairDet q q' pp₂).toNat : ℤ) = pairDet q q' pp₂ := Int.toNat_of_nonneg hD₂.le
      have hdvd₁ : d ∣ (pairDet q q' pp₁).toNat := by
        apply Int.natCast_dvd_natCast.mp
        rw [hnat₁]
        exact gcd_dvd_pairDet q q' pp₁
      have hdvd₂ : d ∣ (pairDet q q' pp₂).toNat := by
        apply Int.natCast_dvd_natCast.mp
        rw [hnat₂]
        exact gcd_dvd_pairDet q q' pp₂
      have he₁ : (pairDet q q' pp₁).toNat/d = (pairDet q q' pp₂).toNat/d := congrArg Prod.fst heq
      have he₂ : pp₁.1/a = pp₂.1/a := congrArg Prod.snd heq
      have hnat : (pairDet q q' pp₁).toNat = (pairDet q q' pp₂).toNat := by
        rw [← Nat.div_mul_cancel hdvd₁,← Nat.div_mul_cancel hdvd₂,he₁]
      have hdet : pairDet q q' pp₁ = pairDet q q' pp₂ := by
        rw [← hnat₁,← hnat₂,hnat]
      obtain ⟨hp,hp'⟩ := determinant_block_injective hq hdet he₂
      exact Prod.ext hp hp'
  calc
    _ ≤ ((Finset.Ioc 0 (4*(q'-q)/d)) ×ˢ Finset.range (2*d)).card := hcard
    _ = (4*(q'-q)/d)*(2*d) := by simp
    _ = 2*((4*(q'-q)/d)*d) := by ring
    _ ≤ 2*(4*(q'-q)) := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
    _ = _ := by ring

end
end Paper14
