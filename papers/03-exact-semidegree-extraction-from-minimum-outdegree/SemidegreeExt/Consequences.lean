import SemidegreeExt.Main
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Finset Real Filter Topology Asymptotics
namespace SemidegreeExt

@[simp] theorem C_zero (n : ℕ) : C n 0 = 0 := by
  by_cases hn : 0 < n
  · exact Nat.le_zero.mp (C_le_d n 0 hn)
  · simp [C, hn]

/-- The complete symmetric digraph endpoint, also for n = 1. -/
theorem C_top (n : ℕ) (hn : 0 < n) : C n (n-1) = n-1 := by
  have hd : n-1 < n := by omega
  apply Nat.le_antisymm (C_le_d n _ hd)
  have h := C_spec n (n-1) hd
  have hle := C_le_d n (n-1) hd
  have hns : n-1+1=n := by omega
  nlinarith [sq_nonneg (n-1-C n (n-1) : ℤ)]

/-- The sharp profile strictly improves both earlier lower bounds, and lies below α. -/
theorem dense_strict_comparisons (α : ℝ) (hα : 0 < α) (hα' : α < 1) :
    α^2/2 < 1-sqrt (1-α^2) ∧
    1-sqrt (3-4*α+α^2) < 1-sqrt (1-α^2) ∧
    1-sqrt (1-α^2) < α := by
  have ha2 : 0 < α^2 := sq_pos_of_pos hα
  have har : 0 < 1-α^2 := by nlinarith
  have hs0 := Real.sqrt_nonneg (1-α^2)
  have hs2 := Real.sq_sqrt har.le
  have hs1 : sqrt (1-α^2) < 1 := (Real.sqrt_lt' (by norm_num)).mpr (by nlinarith)
  have hmid : sqrt (1-α^2) < sqrt (3-4*α+α^2) := by
    apply Real.sqrt_lt_sqrt har.le
    nlinarith [sq_pos_of_pos (show 0 < 1-α by linarith)]
  have hlower : 1-α < sqrt (1-α^2) := by
    apply (Real.lt_sqrt (by linarith)).mpr
    nlinarith
  refine ⟨?_, by linarith, by linarith⟩
  nlinarith [sq_pos_of_pos (sub_pos.mpr hs1)]

/-- Uniform error estimate underlying the small-density expansion. -/
lemma small_density_error (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) :
    |(1-sqrt (1-α^2)) - α^2/2 - α^4/8| ≤ α^6 := by
  let s := sqrt (1-α^2)
  have harg : 0 ≤ 1-α^2 := by nlinarith
  have hs0 : 0 ≤ s := sqrt_nonneg _
  have hs1 : s ≤ 1 := (sqrt_le_left (by norm_num)).mpr (by nlinarith)
  have hs2 : s^2 = 1-α^2 := sq_sqrt harg
  have ht : α^2 = 1-s^2 := by linarith
  have hrem : (1-s)-α^2/2-α^4/8 = (1-s)^3*(s+3)/8 := by
    rw [show α^4 = (α^2)^2 by ring, ht]
    ring
  have ha0 : 0 ≤ 1-s := by linarith
  have hat : 1-s ≤ α^2 := by nlinarith
  have hcub : (1-s)^3 ≤ α^6 := by
    convert pow_le_pow_left₀ ha0 hat 3 using 1 <;> ring
  have ha3 : 0 ≤ (1-s)^3 := pow_nonneg ha0 _
  have hpos : 0 ≤ (1-s)^3*(s+3)/8 := by positivity
  change |(1-s)-α^2/2-α^4/8| ≤ _
  rw [hrem, abs_of_nonneg hpos]
  nlinarith [mul_nonneg ha3 (by linarith : 0 ≤ 1-s)]

/-- Section 4, first endpoint expansion, with the stated O(α^6) error. -/
theorem small_density_expansion :
    (fun α : ℝ => (1-sqrt (1-α^2)) - α^2/2 - α^4/8)
      =O[𝓝[>] (0 : ℝ)] (fun α => α^6) := by
  apply Asymptotics.IsBigO.of_bound 1
  have hlt : ∀ᶠ α : ℝ in 𝓝[>] 0, α < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with α hα hlt
  have hα0 : 0 ≤ α := le_of_lt hα
  simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg (pow_nonneg hα0 6)] using
    small_density_error α hα0 hlt.le

/-- Uniform error estimate underlying the density-one expansion. -/
lemma high_density_error (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1) :
    |(1-sqrt (1-α^2)) - (1-sqrt (2*(1-α)))| ≤ (1-α)*sqrt (1-α) := by
  let t := 1-α
  have ht : 0 < t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  let a := sqrt (2-t)
  let b := sqrt (2 : ℝ)
  have ha0 : 0 ≤ a := sqrt_nonneg _
  have hb0 : 0 ≤ b := sqrt_nonneg _
  have ha2 : a^2 = 2-t := sq_sqrt (by linarith)
  have hb2 : b^2 = 2 := sq_sqrt (by norm_num)
  have ha1 : 1 ≤ a := (le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
  have hab : a ≤ b := sqrt_le_sqrt (by linarith)
  have hd0 : 0 ≤ b-a := by linarith
  have hdt : b-a ≤ t := by
    nlinarith [mul_nonneg hd0 (by linarith : 0 ≤ a+b-1)]
  have heq : (1-sqrt (1-α^2)) - (1-sqrt (2*(1-α))) = sqrt t*(b-a) := by
    have harg : 1-α^2 = t*(2-t) := by dsimp [t]; ring
    rw [harg, sqrt_mul ht.le]
    change (1-sqrt t*a)-(1-sqrt (2*t)) = _
    rw [mul_comm (2 : ℝ) t, sqrt_mul ht.le]
    dsimp [b]
    ring
  rw [heq, abs_of_nonneg (mul_nonneg (sqrt_nonneg _) hd0)]
  change sqrt t*(b-a) ≤ t*sqrt t
  nlinarith [mul_nonneg (sqrt_nonneg t) (sub_nonneg.mpr hdt)]

/-- Section 4, second endpoint expansion, with the stated O((1-α)^(3/2)) error. -/
theorem high_density_expansion :
    (fun α : ℝ => (1-sqrt (1-α^2)) - (1-sqrt (2*(1-α))))
      =O[𝓝[<] (1 : ℝ)] (fun α => (1-α)^((3 : ℝ)/2)) := by
  apply Asymptotics.IsBigO.of_bound 1
  have hgt : ∀ᶠ α : ℝ in 𝓝[<] 1, 0 < α :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hgt] with α hα hgt
  change α < 1 at hα
  have ht : 0 < 1-α := by linarith [hα]
  have hp : (1-α)^((3 : ℝ)/2) = (1-α)*sqrt (1-α) := by
    rw [show (3 : ℝ)/2 = 1+1/2 by norm_num, Real.rpow_add ht,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, hp,
    abs_of_nonneg (mul_nonneg ht.le (sqrt_nonneg _))]
  exact high_density_error α hgt.le hα

/-- Arc inclusion preserves the extraction parameter, justifying passage to induced graphs. -/
theorem q_mono {V : Type*} [Fintype V] {G H : Digraph V}
    (hGH : ∀ v w, G.Adj v w → H.Adj v w) : q G ≤ q H := by
  classical
  unfold q
  apply Finset.sup_le
  intro S hS
  have hs : S.Nonempty := (mem_filter.mp hS).2
  apply le_trans (b := minSemiDegOn H S) ?_ (le_q H hs)
  rw [minSemiDegOn, dif_pos hs, minSemiDegOn, dif_pos hs]
  apply Finset.le_inf'
  intro v hv
  apply le_trans (Finset.inf'_le (semiDegOn G S) hv)
  unfold semiDegOn outDegOn inDegOn
  apply min_le_min <;> apply card_le_card <;> intro u hu
  · exact mem_filter.mpr ⟨(mem_filter.mp hu).1, hGH _ _ (mem_filter.mp hu).2⟩
  · exact mem_filter.mpr ⟨(mem_filter.mp hu).1, hGH _ _ (mem_filter.mp hu).2⟩

/-- A transitive tournament may have quadratically many arcs and extraction parameter zero. -/
theorem transitive_tournament_q_zero (n : ℕ) :
    q (⟨fun i j : Fin n => i < j⟩ : Digraph (Fin n)) = 0 := by
  let G : Digraph (Fin n) := ⟨fun i j => i < j⟩
  apply Nat.le_zero.mp
  apply (q_le_iff_weaklyDegenerate G 0).mpr
  intro S hS
  let v := S.max' hS
  refine ⟨v, max'_mem S hS, Or.inl ?_⟩
  have hz : outDegOn G S v = 0 := by
    unfold outDegOn
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hw' : w ∈ S ∧ v < w := by simpa only [mem_filter, G] using hw
    exact not_lt_of_ge (le_max' S w hw'.1) hw'.2
  omega
/-- The Section 4 comparisons for the paper's original liminf function. -/
theorem hAlpha_strict_comparisons (α : ℝ) (hα : 0 < α) (hα' : α < 1) :
    α^2/2 < hAlpha α ∧
    1-sqrt (3-4*α+α^2) < hAlpha α ∧ hAlpha α < α := by
  rw [(corollary_1_2 α hα hα').2.2]
  exact dense_strict_comparisons α hα hα'

/-- The small-density expansion also holds for the original extraction function. -/
theorem hAlpha_small_expansion :
    (fun α : ℝ => hAlpha α - α^2/2 - α^4/8)
      =O[𝓝[>] (0 : ℝ)] (fun α => α^6) := by
  apply small_density_expansion.congr' ?_ Filter.EventuallyEq.rfl
  have hlt : ∀ᶠ α : ℝ in 𝓝[>] 0, α < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with α hα hlt
  rw [(corollary_1_2 α hα hlt).2.2]

/-- The density-one expansion also holds for the original extraction function. -/
theorem hAlpha_high_expansion :
    (fun α : ℝ => hAlpha α - (1-sqrt (2*(1-α))))
      =O[𝓝[<] (1 : ℝ)] (fun α => (1-α)^((3 : ℝ)/2)) := by
  apply high_density_expansion.congr' ?_ Filter.EventuallyEq.rfl
  have hgt : ∀ᶠ α : ℝ in 𝓝[<] 1, 0 < α :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hgt] with α hα hgt
  rw [(corollary_1_2 α hgt hα).2.2]

/-- The numerical example from the introduction. -/
theorem dense_four_fifths : 1-sqrt (1-(4/5 : ℝ)^2) = (2/5 : ℝ) := by
  have hs : sqrt (1-(4/5 : ℝ)^2) = (3/5 : ℝ) := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
    norm_num
  rw [hs]
  norm_num

/-- The earlier bound (1.2) follows by dropping the quadratic correction. -/
theorem earlier_extraction_bound (n d : ℕ) (hn : 0 < n) (hdn : d < n)
    (G : Digraph (Fin n)) (hG : Loopless G) (hd : ∀ v, d ≤ outDeg G v) :
    (d : ℝ)*(d+1)/(2*n) ≤ q G := by
  have h := prop_2_1 hG hd rfl hn hdn
  have h' : d*(d+1) ≤ 2*q G*n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*n)).mpr
  have hr : (d : ℝ)*(d+1) ≤ 2*(q G)*n := by exact_mod_cast h'
  nlinarith
end SemidegreeExt
