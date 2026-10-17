import Paper09.Asymptotics
import Mathlib.Data.Nat.Find
import Mathlib.Order.Filter.AtTopBot.Tendsto

open Real Filter Classical
open scoped Topology
noncomputable section
namespace Paper09

/-- The consecutive-ratio hypothesis in Assumption 1.1 supplies an admissible
box at every sufficiently large target scale. The lower factor `1/2` is enough
for the lower bound and keeps all constants independent of the outer volume. -/
theorem dense_sequence_scale (m : ℕ → ℕ) (hm : StrictMono m)
    (hratio : Tendsto (fun k => (m (k + 1) : ℝ) / (m k : ℝ)) atTop (𝓝 1))
    (K : ℕ) :
    ∃ R : ℝ, ∀ r : ℝ, R ≤ r → ∃ k : ℕ,
      K ≤ k ∧ 1 ≤ m k ∧ (m k : ℝ) ≤ r ∧ r < 2 * (m k : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hratio.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)))
  let J := max (max K N) 1
  refine ⟨m (J + 1), ?_⟩
  intro r hr
  have hex : ∃ k : ℕ, r < (m k : ℝ) := by
    obtain ⟨k, hk⟩ := exists_nat_gt r
    refine ⟨k, hk.trans_le ?_⟩
    exact_mod_cast hm.id_le k
  let p := Nat.find hex
  have hp : r < (m p : ℝ) := Nat.find_spec hex
  have hJ : J + 1 < p := by
    by_contra h
    have hle : p ≤ J + 1 := by omega
    have hmp : (m p : ℝ) ≤ m (J + 1) := by exact_mod_cast hm.monotone hle
    linarith
  have hp0 : 0 < p := by omega
  have hprev : p - 1 + 1 = p := by omega
  have hprevJ : J ≤ p - 1 := by omega
  have hprevN : N ≤ p - 1 :=
    (le_max_right K N).trans ((le_max_left (max K N) 1).trans hprevJ)
  have hprevK : K ≤ p - 1 :=
    (le_max_left K N).trans ((le_max_left (max K N) 1).trans hprevJ)
  have hprev1 : 1 ≤ p - 1 := (le_max_right (max K N) 1).trans hprevJ
  have hmpos : 1 ≤ m (p - 1) := hprev1.trans (hm.id_le _)
  have hmreal : (0 : ℝ) < m (p - 1) := by exact_mod_cast (show 0 < m (p-1) by omega)
  have hle : (m (p - 1) : ℝ) ≤ r :=
    le_of_not_gt (Nat.find_min hex (show p - 1 < Nat.find hex by change p - 1 < p; omega))
  have hnext : (m p : ℝ) < 2 * m (p - 1) := by
    have hh := hN (p - 1) hprevN
    rw [hprev, div_lt_iff₀ hmreal] at hh
    exact hh
  exact ⟨p - 1, hprevK, hmpos, hle, hp.trans hnext⟩

end Paper09
