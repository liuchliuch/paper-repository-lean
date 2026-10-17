import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Module.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import GeometricMedianCoresets.VarianceIdentity

/-!
# Boundary cases of Lemma 2.3 (7)

* `m = n`: unique sample `univ`, variance 0.
* `m = 1`: samples are singletons, expectation `(1/n) ∑ ‖h i - h̄‖²`.
* `n = 1` (so `m = 1`): variance 0.
-/

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace GeometricMedianCoresets
namespace FinitePopulation

/-- When `m = n` the only sample is the full set and the mean error vanishes. -/
theorem variance_zero_of_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (hn : 0 < n) (h : Fin n → H) :
    uniformAvg (m := n) (fun I => ‖sampleMean h I - popMean h‖ ^ 2) = 0 := by
  have hcard : (Finset.univ : Finset (Fin n)).card = n := Fintype.card_fin n
  have hsm : sampleMean h Finset.univ = popMean h := by
    rw [sampleMean_eq h Finset.univ (by rw [hcard]; exact hn), popMean_eq hn h]
    have hsum : ∑ i ∈ (Finset.univ : Finset (Fin n)), h i = ∑ i, h i := rfl
    rw [hsum]
    have hcard' : ((Finset.univ : Finset (Fin n)).card : ℝ) = (n : ℝ) := by
      exact_mod_cast hcard
    rw [hcard']
  have hpow : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    have h := Finset.powersetCard_self (Finset.univ : Finset (Fin n))
    rwa [hcard] at h
  unfold uniformAvg
  rw [hpow, Finset.sum_singleton, hsm, sub_self, norm_zero, zero_pow (by norm_num)]
  rw [Nat.choose_self]
  ring

/-- Singleton sample mean is the point itself. -/
theorem sampleMean_singleton {H : Type*} [NormedAddCommGroup H] [Module ℝ H]
    {n : ℕ} (h : Fin n → H) (i : Fin n) :
    sampleMean h ({i} : Finset (Fin n)) = h i := by
  have hcard : ({i} : Finset (Fin n)).card = 1 := Finset.card_singleton i
  rw [sampleMean_eq h {i} (by rw [hcard]; exact Nat.one_pos), hcard]
  have hsum : ∑ j ∈ ({i} : Finset (Fin n)), h j = h i := by simp
  rw [hsum]
  norm_num

/-- When `m = 1`, `uniformAvg ‖h̄_I - h̄‖² = (1/n) ∑ ‖h i - h̄‖²`. -/
theorem variance_one_sample {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (hn : 0 < n) (h : Fin n → H) :
    uniformAvg (m := 1) (fun I => ‖sampleMean h I - popMean h‖ ^ 2)
      = (1:ℝ) / n * ∑ i, ‖h i - popMean h‖ ^ 2 := by
  let emb : Fin n ↪ Finset (Fin n) :=
    ⟨fun i => ({i} : Finset (Fin n)), Finset.singleton_injective⟩
  have hmap : (Finset.univ : Finset (Fin n)).powersetCard 1
      = (Finset.univ : Finset (Fin n)).map emb :=
    Finset.powersetCard_one _
  have hsm : ∀ i : Fin n, sampleMean h ({i} : Finset (Fin n)) = h i :=
    fun i => sampleMean_singleton h i
  have hemp : ∀ i : Fin n, emb i = ({i} : Finset (Fin n)) := fun i => rfl
  unfold uniformAvg
  rw [hmap, Finset.sum_map]
  have h3 : (∑ i : Fin n, ‖sampleMean h (emb i) - popMean h‖ ^ 2)
      = ∑ i : Fin n, ‖h i - popMean h‖ ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [hemp i, hsm i]
  rw [h3]
  have h1 : (n.choose 1 : ℝ) = n := by rw [Nat.choose_one_right]
  rw [h1]
  ring

/-- When `n = 1` (hence `m = 1`) the variance is 0. -/
theorem variance_one_point {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (h : Fin 1 → H) :
    uniformAvg (m := 1) (fun I => ‖sampleMean h I - popMean h‖ ^ 2) = 0 := by
  have hn : 0 < (1:ℕ) := by norm_num
  rw [variance_one_sample hn h]
  have hpop : popMean h = h 0 := by
    rw [popMean_eq hn h]
    have hsum : ∑ i : Fin 1, h i = h 0 := by simp
    rw [hsum]
    norm_num
  have hsum : ∑ i : Fin 1, ‖h i - popMean h‖ ^ 2 = 0 := by
    rw [Finset.sum_eq_single 0]
    · rw [hpop, sub_self, norm_zero, zero_pow (by norm_num)]
    · intro i _hi hne
      exact absurd (Fin.eq_zero i) hne
    · intro habs
      exact absurd (Finset.mem_univ (0 : Fin 1)) (by simp at habs)
  rw [hsum, mul_zero]

end FinitePopulation
end GeometricMedianCoresets
