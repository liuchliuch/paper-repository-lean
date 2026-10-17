import Paper14.SieveResidualGeometry
import Paper14.RectangleCount

open MeasureTheory Set Function Filter
namespace Paper14
noncomputable section

/-- A primitive vector in the narrower c-band gives a primitive vector
in the original rectangle, after restoring the integer part of b/a. -/
lemma sieve_band_vector_in_rectangle {n Q : ℕ} {ε K : ℝ} {x : ℝ × ℝ}
    (hx : x ∈ Omega) (hε : 0 ≤ ε) (hK : 0 < K) (hcK : cOf x ≤ K)
    (hQ : (Q : ℝ)*K ≤ 2*(n : ℝ)) {p q : ℤ}
    (hband : inSieveBand Q (cOf x) (thetaOf x) ε (p,q)) (hcop : IsCoprime p q) :
    ∃ p' q' : ℤ,
      1-ε < (q' : ℝ)*x.2-(p' : ℝ)*x.1 ∧
      (q' : ℝ)*x.2-(p' : ℝ)*x.1 ≤ 1 ∧
      0 < (q' : ℝ)/x.1 ∧ (q' : ℝ)/x.1 ≤ 2*n ∧ IsCoprime p' q' := by
  let k : ℤ := Int.floor (x.2/x.1)
  have ha0 : 0 < x.1 := hx.1
  have ha1 : x.1 ≤ 1 := hx.2.1
  have hc0 : 0 < cOf x := inv_pos.mpr ha0
  have hac : x.1*cOf x = 1 := mul_inv_cancel₀ ha0.ne'
  have hu : (q : ℝ)*x.2-((p+q*k : ℤ) : ℝ)*x.1 = x.1*((q : ℝ)*thetaOf x-(p : ℝ)) := by
    simp only [thetaOf,Int.fract,k,Int.cast_add,Int.cast_mul]
    field_simp [ha0.ne']
    <;> ring
  have hq0 : (0 : ℝ) < q := by have hh := hband.1; exact_mod_cast (by omega : 0 < q)
  have hqQ : (q : ℝ) ≤ Q := by exact_mod_cast hband.2.1
  refine ⟨p+q*k,q,?_,?_,?_,?_,?_⟩
  · rw [hu]
    have hl := mul_lt_mul_of_pos_left hband.2.2.1 ha0
    have hεa : x.1*ε ≤ ε := mul_le_of_le_one_left hε ha1
    nlinarith
  · rw [hu]
    have hh := mul_le_mul_of_nonneg_left hband.2.2.2 ha0.le
    nlinarith
  · exact div_pos hq0 ha0
  · change (q : ℝ)*cOf x ≤ 2*n
    exact (mul_le_mul hqQ hcK hc0.le (Nat.cast_nonneg Q)).trans hQ
  · obtain ⟨s,t,hst⟩ := hcop
    refine ⟨s,t-s*k,?_⟩
    calc s*(p+q*k)+(t-s*k)*q = s*p+t*q := by ring
         _ = 1 := hst

/-- On the bounded c-region, original primitive-rectangle void forces
void of the narrower primitive-band count used in the sieve. -/
theorem ZCount_zero_GPrim_zero {n : ℕ} {α K : ℝ} {x : ℝ × ℝ}
    (hx : x ∈ Omega) (hα0 : 0 ≤ α/(n : ℝ)) (hα1 : α/(n : ℝ) < 1)
    (hK : 0 < K) (hcK : cOf x ≤ K) (hZ : ZCount n α x = 0) :
    GPrim ⌊2*(n : ℝ)/K⌋₊ (cOf x) (thetaOf x) (α/(n : ℝ)) = 0 := by
  by_contra hn
  obtain ⟨⟨p,q⟩,hpq⟩ := Set.nonempty_of_ncard_ne_zero hn
  have hQ : (⌊2*(n : ℝ)/K⌋₊ : ℝ)*K ≤ 2*n := by
    have hf := Nat.floor_le (div_nonneg (by positivity : (0 : ℝ) ≤ 2*(n : ℝ)) hK.le)
    exact (mul_le_mul_of_nonneg_right hf hK.le).trans_eq (div_mul_cancel₀ _ hK.ne')
  have hv := sieve_band_vector_in_rectangle hx hα0 hK hcK hQ hpq.1 hpq.2
  exact (ZCount_eq_zero_iff hx hα1).mp hZ hv

end
end Paper14
