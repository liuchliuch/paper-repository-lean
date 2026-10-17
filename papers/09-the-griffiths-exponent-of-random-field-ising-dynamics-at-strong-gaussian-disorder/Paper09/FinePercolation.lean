import Paper09.BadClusters
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.Complex.Exponential

open Finset BigOperators Classical Real
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

namespace Paper09.Percolation.Fine

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

structure State (V : Type*) where
  found : Finset V
  asked : Finset V

def candidates (z : V) (F : Finset V) : Finset V :=
  insert z (F.biUnion (fun v => G.neighborFinset v))

def frontier (z : V) (s : State V) : Finset V := candidates G z s.found \ s.asked

def step (z : V) (b : Bool) (s : State V) : State V :=
  if hs : (frontier G z s).Nonempty then
    let v := hs.choose
    ⟨if b then insert v s.found else s.found, insert v s.asked⟩
  else s

def answer (z : V) (S : Finset V) (s : State V) : Bool :=
  if hs : (frontier G z s).Nonempty then decide (hs.choose ∈ S) else false

def run (z : V) (S : Finset V) : ℕ → State V
  | 0 => ⟨∅, ∅⟩
  | n+1 => step G z (answer G z S (run z S n)) (run z S n)

def code (z : V) (S : Finset V) (n : ℕ) : Finset ℕ :=
  (range n).filter fun k => answer G z S (run G z S k) = true

def decode (z : V) (T : Finset ℕ) : ℕ → State V
  | 0 => ⟨∅, ∅⟩
  | n+1 => step G z (decide (n ∈ T)) (decode z T n)

theorem candidates_mono (z : V) {F F' : Finset V} (h : F ⊆ F') :
    candidates G z F ⊆ candidates G z F' := by
  apply insert_subset_insert
  exact biUnion_subset_biUnion_of_subset_left _ h

/-- Queries never repeat: every queried vertex was previously on the frontier. -/
theorem step_found_mono (z : V) (b : Bool) (s : State V) :
    s.found ⊆ (step G z b s).found := by
  unfold step
  split_ifs <;> cases b <;> simp

theorem step_asked_mono (z : V) (b : Bool) (s : State V) :
    s.asked ⊆ (step G z b s).asked := by
  unfold step
  split_ifs <;> simp

theorem run_found_mono (z : V) (S : Finset V) : Monotone (fun n => (run G z S n).found) := by
  apply monotone_nat_of_le_succ
  intro n
  exact step_found_mono G z _ _

/-- Exact exploration invariant: discoveries are precisely the queried
vertices in the target animal; every query came from a discovered neighbor. -/
theorem run_invariant (z : V) (S : Finset V) (n : ℕ) :
    (run G z S n).found = (run G z S n).asked ∩ S ∧
      (run G z S n).asked ⊆ candidates G z (run G z S n).found := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    let s := run G z S n
    change (step G z (answer G z S s) s).found =
      (step G z (answer G z S s) s).asked ∩ S ∧
      (step G z (answer G z S s) s).asked ⊆
        candidates G z (step G z (answer G z S s) s).found
    by_cases hs : (frontier G z s).Nonempty
    · have hv : hs.choose ∈ frontier G z s := hs.choose_spec
      have hvc : hs.choose ∈ candidates G z s.found := (mem_sdiff.mp hv).1
      by_cases hS : hs.choose ∈ S
      · simp only [step, answer, dif_pos hs, decide_eq_true hS, if_true]
        constructor
        · rw [show s.found = s.asked ∩ S from ih.1]
          ext x; simp only [mem_insert, mem_inter]; aesop
        · apply insert_subset_iff.mpr
          constructor
          · exact (candidates_mono G z (subset_insert _ _)) hvc
          · exact ih.2.trans (candidates_mono G z (subset_insert _ _))
      · have hb : decide (hs.choose ∈ S) = false := decide_eq_false hS
        simp only [step, answer, dif_pos hs, hb, Bool.false_eq_true, if_false]
        constructor
        · rw [show s.found = s.asked ∩ S from ih.1]
          ext x; simp only [mem_insert, mem_inter]; aesop
        · exact insert_subset_iff.mpr ⟨hvc, ih.2⟩
    · simpa only [step, dif_neg hs] using ih

private theorem frontier_nonempty (z : V) (S : Finset V)
    (hz : z ∈ S) (hconn : (↑S : Set V) ⊆ cluster G (fun x => x ∈ S) z)
    (s : State V) (heq : s.found = s.asked ∩ S)
    (hnot : ¬ S ⊆ s.found) : (frontier G z s).Nonempty := by
  by_cases hzf : z ∈ s.found
  · obtain ⟨x, hx, hxf⟩ := not_subset.mp hnot
    have hr := (hconn hx).2
    obtain ⟨a, ha, b, hb, hab⟩ := reachable_exit hzf hxf hr
    have hbS : b ∈ S := hab.2.2
    have hba : b ∉ s.asked := by
      intro hba
      exact hb (by rw [heq]; exact mem_inter.mpr ⟨hba, hbS⟩)
    refine ⟨b, mem_sdiff.mpr ⟨mem_insert_of_mem (mem_biUnion.mpr ⟨a, ha, ?_⟩), hba⟩⟩
    exact (G.mem_neighborFinset a b).mpr hab.1
  · have hza : z ∉ s.asked := by
      intro hh
      exact hzf (by rw [heq]; exact mem_inter.mpr ⟨hh, hz⟩)
    exact ⟨z, mem_sdiff.mpr ⟨mem_insert_self _ _, hza⟩⟩

private theorem asked_card_of_incomplete (z : V) (S : Finset V)
    (hz : z ∈ S) (hconn : (↑S : Set V) ⊆ cluster G (fun x => x ∈ S) z)
    (n : ℕ) (hnot : ¬ S ⊆ (run G z S n).found) :
    (run G z S n).asked.card = n := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have hprev : ¬ S ⊆ (run G z S n).found := fun hh =>
      hnot (hh.trans (run_found_mono G z S (Nat.le_succ n)))
    have hs := frontier_nonempty G z S hz hconn (run G z S n)
      (run_invariant G z S n).1 hprev
    have hn : hs.choose ∉ (run G z S n).asked := (mem_sdiff.mp hs.choose_spec).2
    simp only [run, step, dif_pos hs]
    rw [card_insert_of_notMem hn, ih hprev]

/-- The queue/frontier exploration must have discovered the complete animal
within `D*r` independent decisions. This is the sharp linear query budget. -/
theorem run_complete (D : ℕ) (hD : 0 < D)
    (hdeg : ∀ x, Fintype.card (G.neighborSet x) ≤ D)
    (z : V) (S : Finset V) (hz : z ∈ S)
    (hconn : (↑S : Set V) ⊆ cluster G (fun x => x ∈ S) z) :
    (run G z S (D*S.card)).found = S := by
  let n := D*S.card
  have hinv := run_invariant G z S n
  have hsub : (run G z S n).found ⊆ S := by rw [hinv.1]; exact inter_subset_right
  apply Subset.antisymm hsub
  by_contra hnot
  have hs := frontier_nonempty G z S hz hconn (run G z S n) hinv.1 hnot
  have hcard := asked_card_of_incomplete G z S hz hconn n hnot
  have hlt : (run G z S n).found.card < S.card := card_lt_card ⟨hsub, hnot⟩
  have hcand : (candidates G z (run G z S n).found).card ≤
      1 + D*(run G z S n).found.card := by
    calc _ ≤ 1 + ((run G z S n).found.biUnion (fun v => G.neighborFinset v)).card := by simpa only [candidates, Nat.add_comm] using card_insert_le z ((run G z S n).found.biUnion (fun v => G.neighborFinset v))
      _ ≤ 1 + ∑ x ∈ (run G z S n).found, (G.neighborFinset x).card := Nat.add_le_add_left card_biUnion_le _
      _ ≤ 1 + ∑ _x ∈ (run G z S n).found, D := by
          apply Nat.add_le_add_left
          apply sum_le_sum; intro x hx
          rw [SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
          exact hdeg x
      _ = 1 + D*(run G z S n).found.card := by simp [Nat.mul_comm]
  have hfront : (run G z S n).asked.card < (candidates G z (run G z S n).found).card := by
    apply card_lt_card
    refine ⟨hinv.2, ?_⟩
    intro hh
    have hv := hs.choose_spec
    exact (mem_sdiff.mp hv).2 (hh (mem_sdiff.mp hv).1)
  have hmul := Nat.mul_lt_mul_of_pos_left hlt hD
  rw [hcard] at hfront
  have hnval : n = D*S.card := rfl
  omega

/-- The success positions determine the entire deterministic exploration. -/
theorem decode_code (z : V) (S : Finset V) (N n : ℕ) (hn : n ≤ N) :
    decode G z (code G z S N) n = run G z S n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [decode, ih (by omega), run]
    congr 1
    have hk : n < N := by omega
    simp only [code, mem_filter, mem_range, hk, true_and]
    cases hb : answer G z S (run G z S n) <;> simp [hb]

theorem code_card (z : V) (S : Finset V) (n : ℕ) :
    (code G z S n).card = (run G z S n).found.card := by
  induction n with
  | zero => simp [code, run]
  | succ n ih =>
    rw [code, range_succ, filter_insert]
    have hn : n ∉ (range n).filter (fun k => answer G z S (run G z S k) = true) := by simp
    by_cases hs : (frontier G z (run G z S n)).Nonempty
    · have hva : hs.choose ∉ (run G z S n).asked := (mem_sdiff.mp hs.choose_spec).2
      have hvf : hs.choose ∉ (run G z S n).found := by
        intro hh
        have hinv := (run_invariant G z S n).1
        rw [hinv] at hh
        exact hva (mem_inter.mp hh).1
      cases hb : answer G z S (run G z S n) <;>
        simp only [hb, Bool.false_eq_true, if_false, if_true, run, step, dif_pos hs]
      · exact ih
      · rw [card_insert_of_notMem hn, card_insert_of_notMem hvf]
        exact congrArg (fun k => k+1) ih
    · have hb : answer G z S (run G z S n) = false := by simp [answer, hs]
      simp only [hb, Bool.false_eq_true, if_false, run, step, dif_neg hs]
      exact ih

/-- Rooted connected animals admit a `D*r`-bit encoding with exactly `r`
successes, giving a binomial rather than squared-degree counting bound. -/
theorem card_rootedAnimals_le_choose (D : ℕ) (hD : 0 < D)
    (hdeg : ∀ x, Fintype.card (G.neighborSet x) ≤ D) (z : V) (r : ℕ) :
    (rootedAnimals G z r).card ≤ (D*r).choose r := by
  classical
  have hproperties (S : Finset V) (hS : S ∈ rootedAnimals G z r) :
      z ∈ S ∧ S.card = r ∧ (↑S : Set V) ⊆ cluster G (fun x => x ∈ S) z := by
    obtain ⟨hi, hc⟩ := mem_filter.mp hS
    obtain ⟨p, hp, heq⟩ := mem_image.mp hi
    subst S
    refine ⟨by simpa using p.start_mem_support, hc, ?_⟩
    intro x hx
    exact walk_support_subset_cluster p (fun v hv => List.mem_toFinset.mpr hv) x (List.mem_toFinset.mp hx)
  have hfinish (S : Finset V) (hS : S ∈ rootedAnimals G z r) :
      (run G z S (D*r)).found = S := by
    obtain ⟨hz, hc, hconn⟩ := hproperties S hS
    simpa only [hc] using run_complete G D hD hdeg z S hz hconn
  calc
    (rootedAnimals G z r).card ≤ ((range (D*r)).powersetCard r).card := by
      apply card_le_card_of_injOn (fun S : Finset V => code G z S (D*r))
      · intro S hS
        change code G z S (D*r) ∈ (range (D*r)).powersetCard r
        rw [mem_powersetCard]
        refine ⟨filter_subset _ _, ?_⟩
        rw [code_card, hfinish S hS, (hproperties S hS).2.1]
      · intro S hS T hT he
        have hd := congrArg (fun C => (decode G z C (D*r)).found) he
        change (decode G z (code G z S (D*r)) (D*r)).found = (decode G z (code G z T (D*r)) (D*r)).found at hd
        rw [decode_code G z S _ _ le_rfl, decode_code G z T _ _ le_rfl,
          hfinish S hS, hfinish T hT] at hd
        exact hd
    _ = (D*r).choose r := by simp

/-- The factorial term gives the sharp universal exponential constant `e`. -/
theorem choose_mul_le_exp (D r : ℕ) :
    ((D*r).choose r : ℝ) ≤ (exp 1 * (D:ℝ))^r := by
  calc ((D*r).choose r : ℝ) ≤ ((D*r : ℕ):ℝ)^r / (r.factorial:ℝ) := Nat.choose_le_pow_div r (D*r)
    _ = (D:ℝ)^r * ((r:ℝ)^r / (r.factorial:ℝ)) := by rw [Nat.cast_mul, mul_pow]; ring
    _ ≤ (D:ℝ)^r * exp (r:ℝ) :=
      mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp (r:ℝ) (Nat.cast_nonneg r) r) (by positivity)
    _ = (exp 1 * (D:ℝ))^r := by
      have he : exp (r:ℝ) = (exp 1)^r := by simpa using Real.exp_nat_mul 1 r
      rw [he, mul_pow, mul_comm]

/-- The fine connected-animal bound, with degree appearing to the first power. -/
theorem card_rootedAnimals_le_exp (D : ℕ) (hD : 0 < D)
    (hdeg : ∀ x, Fintype.card (G.neighborSet x) ≤ D) (z : V) (r : ℕ) :
    ((rootedAnimals G z r).card : ℝ) ≤ (exp 1*(D:ℝ))^r := by
  have hc : ((rootedAnimals G z r).card : ℝ) ≤ ((D*r).choose r : ℝ) := by
    exact_mod_cast card_rootedAnimals_le_choose G D hD hdeg z r
  exact hc.trans (choose_mul_le_exp D r)

/-- The actual cluster-event union, using the probabilities of finite open
intersections. In an independent site law these are exactly `p^|S|`. -/
theorem cluster_probability_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (ω : Ω → V → Prop) (p : ℝ) (hp : 0 ≤ p)
    (hopen : ∀ S : Finset V, μ.real {a | ∀ x ∈ S, ω a x} ≤ p^S.card)
    (D : ℕ) (hD : 0 < D) (hdeg : ∀ x, Fintype.card (G.neighborSet x) ≤ D)
    (z : V) (r : ℕ) (hr : 0 < r) :
    μ.real {a | clusterAtLeast G (ω a) z r} ≤ (exp 1*(D:ℝ)*p)^r := by
  have he : {a | clusterAtLeast G (ω a) z r} =
      ⋃ S ∈ rootedAnimals G z r, {a | ∀ x ∈ S, ω a x} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    exact clusterAtLeast_iff_animal G (ω a) z r hr
  rw [he]
  calc μ.real (⋃ S ∈ rootedAnimals G z r, {a | ∀ x ∈ S, ω a x}) ≤
      ∑ S ∈ rootedAnimals G z r, μ.real {a | ∀ x ∈ S, ω a x} :=
        MeasureTheory.measureReal_biUnion_finset_le _ _
    _ ≤ ∑ S ∈ rootedAnimals G z r, p^r := by
      apply sum_le_sum
      intro S hS
      have hc := (mem_filter.mp hS).2
      simpa only [hc] using hopen S
    _ = ((rootedAnimals G z r).card : ℝ) * p^r := by simp
    _ ≤ (exp 1*(D:ℝ))^r * p^r := mul_le_mul_of_nonneg_right
      (card_rootedAnimals_le_exp G D hD hdeg z r) (pow_nonneg hp r)
    _ = (exp 1*(D:ℝ)*p)^r := (mul_pow _ _ _).symm

/-- Nearest-neighbor specialization at the exact disorder threshold in the
paper. The one-site intersection bound may be supplied by the actual product
Gaussian/uniform environment, without any cluster-tail premise. -/
theorem lattice_cluster_probability_le {Ω : Type*} [MeasurableSpace Ω]
    (d : ℕ) (hd : 0 < d) (μ : MeasureTheory.Measure Ω)
    (ω : Ω → LatticeGeometry.Point d → Prop) (p : ℝ) (hp : 0 ≤ p)
    (hopen : ∀ S : Finset (LatticeGeometry.Point d),
      μ.real {a | ∀ x ∈ S, ω a x} ≤ p^S.card)
    (hpbound : p ≤ 1/(20*(d:ℝ))) (z : LatticeGeometry.Point d)
    (r : ℕ) (hr : 0 < r) :
    μ.real {a | clusterAtLeast (nnGraph d) (ω a) z r} ≤ (exp 1/10)^r := by
  have hdp : 0 < (d:ℝ) := by exact_mod_cast hd
  have hb : exp 1*(2*(d:ℝ))*p ≤ exp 1/10 := by
    have hh := mul_le_mul_of_nonneg_left hpbound (by positivity : 0 ≤ exp 1*(2*(d:ℝ)))
    have he : exp 1*(2*(d:ℝ))*(1/(20*(d:ℝ))) = exp 1/10 := by field_simp; ring
    rwa [he] at hh
  apply (cluster_probability_le (nnGraph d) μ ω p hp hopen (2*d) (by omega)
    nnGraph_degree_le z r hr).trans
  apply pow_le_pow_left₀ (by positivity)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hb

end Paper09.Percolation.Fine
