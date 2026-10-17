import Paper14.SieveVariance
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Algebra.Ring.Periodic

open Set Function
namespace Paper14
noncomputable section

/-- One actual band contribution, indexed by its integer vertical
coefficient. There is at most one horizontal coefficient when epsilon < 1. -/
def sieveSingle (M : ℕ) (q : ℤ) (ε u : ℝ) : ℕ :=
  if (Int.ceil u : ℝ) < u+ε ∧ IsCoprime (Int.ceil u) ((Int.gcd q (Int.ofNat M) : ℕ) : ℤ) then 1 else 0

lemma narrow_band_integer_unique {u ε : ℝ} (hε : ε ≤ 1) {p : ℤ}
    (hup : u ≤ (p : ℝ)) (hpu : (p : ℝ) < u+ε) : p = Int.ceil u := by
  have hlo : Int.ceil u ≤ p := Int.ceil_le.mpr hup
  have hhi : (p : ℝ) < (Int.ceil u : ℝ)+1 := by
    linarith [Int.le_ceil u]
  have hhiZ : p < Int.ceil u+1 := by exact_mod_cast hhi
  omega

/-- The finite-sieve definition counts exactly the finite sum of its
actual single-q contributions; no finite p cutoff is introduced. -/
theorem GM_eq_sum_sieveSingle (M Q : ℕ) (c θ ε : ℝ) (hε : ε ≤ 1) :
    GM M Q c θ ε = ∑ q ∈ Finset.Icc (1 : ℤ) (Q : ℤ), sieveSingle M q ε ((q : ℝ)*θ-c) := by
  classical
  let F : Finset ℤ := (Finset.Icc (1 : ℤ) (Q : ℤ)).filter (fun q : ℤ =>
    (Int.ceil ((q : ℝ)*θ-c) : ℝ) < ((q : ℝ)*θ-c)+ε ∧
      IsCoprime (Int.ceil ((q : ℝ)*θ-c)) ((Int.gcd q (Int.ofNat M) : ℕ) : ℤ))
  let f : ℤ → ℤ × ℤ := fun q => (Int.ceil ((q : ℝ)*θ-c),q)
  have hf : Injective f := by intro q q' h; exact congrArg Prod.snd h
  have hset : {pq : ℤ × ℤ | inSieveBand Q c θ ε pq ∧
      IsCoprime pq.1 ((Int.gcd pq.2 (Int.ofNat M) : ℕ) : ℤ)} = f '' (F : Set ℤ) := by
    ext pq
    constructor
    · rintro ⟨⟨hql,hqu,hbandl,hbandu⟩,hcop⟩
      have hp : pq.1 = Int.ceil ((pq.2 : ℝ)*θ-c) := narrow_band_integer_unique hε (by linarith) (by linarith)
      refine ⟨pq.2,?_,?_⟩
      · simp only [F,Finset.mem_coe,Finset.mem_filter,Finset.mem_Icc]
        refine ⟨⟨hql,hqu⟩,?_,?_⟩
        · rw [← hp]; linarith
        · rw [← hp]; exact hcop
      · exact Prod.ext hp.symm rfl
    · rintro ⟨q,hq,rfl⟩
      have hq' := (Finset.mem_filter.mp hq)
      obtain ⟨hql,hqu⟩ := Finset.mem_Icc.mp hq'.1
      dsimp [f]
      refine ⟨⟨hql,hqu,?_,?_⟩,hq'.2.2⟩
      · linarith [hq'.2.1]
      · linarith [Int.le_ceil ((q : ℝ)*θ-c)]
  rw [GM,hset,Set.ncard_image_of_injective _ hf,Set.ncard_coe_finset]
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro q hq
  rfl

lemma sieveSingle_le_one (M : ℕ) (q : ℤ) (ε u : ℝ) : sieveSingle M q ε u ≤ 1 := by
  unfold sieveSingle
  split_ifs <;> omega

lemma measurable_sieveSingle (M : ℕ) (q : ℤ) (ε : ℝ) : Measurable (sieveSingle M q ε) := by
  unfold sieveSingle
  apply Measurable.ite _ measurable_const measurable_const
  apply MeasurableSet.inter
  · change MeasurableSet {u : ℝ | (Int.ceil u : ℝ) < u+ε}
    apply measurableSet_lt
    · fun_prop
    · exact measurable_id.add_const ε
  · change MeasurableSet ((Int.ceil : ℝ → ℤ) ⁻¹' {p : ℤ | IsCoprime p ((Int.gcd q (Int.ofNat M) : ℕ) : ℤ)})
    exact Int.measurable_ceil (Set.to_countable _ |>.measurableSet)

lemma sieveSingle_add_int (M : ℕ) (q k : ℤ) (ε u : ℝ)
    (hk : ((Int.gcd q (Int.ofNat M) : ℕ) : ℤ) ∣ k) :
    sieveSingle M q ε (u+(k : ℝ)) = sieveSingle M q ε u := by
  have hcop : IsCoprime (Int.ceil u+k) ((Int.gcd q (Int.ofNat M) : ℕ) : ℤ) ↔
      IsCoprime (Int.ceil u) ((Int.gcd q (Int.ofNat M) : ℕ) : ℤ) := by
    obtain ⟨z,hz⟩ := hk
    rw [hz,IsCoprime.add_mul_left_left_iff]
  have hlt : (Int.ceil u : ℝ)+(k : ℝ) < (u+(k : ℝ))+ε ↔ (Int.ceil u : ℝ) < u+ε := by
    constructor <;> intro h <;> linarith
  simp only [sieveSingle,Int.ceil_add_intCast,Int.cast_add,hlt,hcop]

/-- The two periods of the sieve indicator used in the torus argument. -/
lemma sieveSingle_periods (M : ℕ) (q : ℤ) (ε : ℝ) :
    Function.Periodic (sieveSingle M q ε) (M : ℝ) ∧
    Function.Periodic (sieveSingle M q ε) (q : ℝ) := by
  constructor
  · intro u
    exact sieveSingle_add_int M q (Int.ofNat M) ε u (Int.gcd_dvd_right _ _)
  · intro u
    exact sieveSingle_add_int M q q ε u (Int.gcd_dvd_left _ _)

lemma measurable_GM (M Q : ℕ) {ε : ℝ} (hε : ε ≤ 1) :
    Measurable (fun z : ℝ × ℝ => GM M Q z.1 z.2 ε) := by
  have heq : (fun z : ℝ × ℝ => GM M Q z.1 z.2 ε) =
      (fun z => ∑ q ∈ Finset.Icc (1 : ℤ) (Q : ℤ), sieveSingle M q ε ((q : ℝ)*z.2-z.1)) := by
    funext z
    exact GM_eq_sum_sieveSingle M Q z.1 z.2 ε hε
  rw [heq]
  apply Finset.measurable_sum
  intro q hq
  exact (measurable_sieveSingle M q ε).comp (by fun_prop)

end
end Paper14
