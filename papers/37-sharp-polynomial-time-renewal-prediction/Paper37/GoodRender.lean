import Paper37.BackwardRender
import Paper37.BayesLowerBound
import Mathlib.Data.Fin.Tuple.Take

/-! Deterministic transfer from the backward-cycle construction to the
observable source good event. No event-probability estimate is assumed. -/
namespace Paper37.GoodRender
open Paper37.Renewal Paper37.BackwardRender

lemma gapsFrom_length_eq_count (a : ℕ) (x : List Bool) :
    (gapsFrom a x).length = x.count true := by
  induction x generalizing a with
  | nil => simp [gapsFrom]
  | cons v x ih => cases v <;> simp [gapsFrom, ih]

lemma count_true_zeros (j : ℕ) : (List.replicate j false).count true = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => simpa [List.replicate_succ] using ih

/-- Every parsed completed gap belongs to the corresponding prefix of the
supplied backward iid sample. -/
lemma mem_prefix_sample {b n : ℕ} (hbn : b ≤ n) (ds : Fin n → ℕ)
    {r age : ℕ} (hr : r ≤ b) (hmem : age ∈ (List.ofFn ds).take r) :
    ∃ i : Fin b, ds (Fin.castLE hbn i) = age := by
  have hb : age ∈ (List.ofFn ds).take b := by
    have he : (List.ofFn ds).take r = ((List.ofFn ds).take b).take r := by
      rw [List.take_take, Nat.min_eq_left hr]
    rw [he] at hmem
    exact List.mem_of_mem_take hmem
  rw [← Fin.ofFn_take_eq_take_ofFn hbn ds] at hb
  simpa only [List.mem_ofFn, Fin.take_apply] using hb

/-- The three elementary sampling events imply precisely the actual
observable `GoodBlock`: a visible renewal, small terminal age, and an unseen
age among at most `b` completed gaps. -/
theorem render_goodBlock {b n age : ℕ} (hbn : b ≤ n) (ds : Fin n → ℕ)
    (ha : age < 24 * b) (hn : 24 * b ≤ n)
    (hcount : (render n age (List.ofFn ds)).count true ≤ b)
    (hcollision : ¬ ∃ i : Fin b, ds (Fin.castLE hbn i) = age) :
    Paper37.BayesLowerBound.GoodBlock b (render n age (List.ofFn ds)) := by
  obtain ⟨j, x, hx, hage, hparse⟩ := render_parse (ds := List.ofFn ds) (by omega : age < n)
  have hr : (gapsFrom 0 x).length ≤ b := by
    rw [gapsFrom_length_eq_count]
    rw [hx] at hcount
    have hz := count_true_zeros j
    have hcx : 1 + x.count true ≤ b := by simpa [hz, Nat.add_comm] using hcount
    omega
  refine ⟨j, x, hx, by simpa [hage] using ha, ?_, hr⟩
  intro hmem
  apply hcollision
  apply mem_prefix_sample hbn ds hr
  rw [← hparse]
  simpa [hage] using hmem

end Paper37.GoodRender
