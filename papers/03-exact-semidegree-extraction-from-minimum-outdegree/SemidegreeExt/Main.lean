import SemidegreeExt.Assembly
import SemidegreeExt.Basic
import SemidegreeExt.Placement
import SemidegreeExt.ClosedForm
import SemidegreeExt.Dense
import SemidegreeExt.Parameters
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Finset.Sort
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

/-!
# Paper statements

Independently readable formal statements of the results in
*Exact semidegree extraction from minimum outdegree*.

All digraphs are loopless (`Loopless G`), matching the paper.
-/

open Finset Digraph Real Filter Topology
open SemidegreeExt

namespace SemidegreeExt

-- `prop_2_1` is provided by `SemidegreeExt.Assembly`.
-- `prop_2_1` lives in `SemidegreeExt.Assembly`.


/-- Universal lower bound: every loopless `n`-vertex digraph with `δ⁺≥d` has
`C n d ≤ q G`. Immediate from Proposition 2.1 and minimality of `C`. -/
theorem C_le_q (n d : ℕ) (hn : 0 < n) (hd : d < n)
    (G : Digraph (Fin n)) (hG : Loopless G) (hdeg : ∀ v, d ≤ outDeg G v) :
    C n d ≤ q G := by
  have hprop := prop_2_1 (n := n) (G := G) (d := d) (c := q G) hG hdeg rfl hn hd
  -- hprop : d(d+1) + q G * (q G + 1) ≤ 2 * q G * n
  exact C_is_least n d hd hprop

/-- Demand of left vertex `i` in the nested-neighborhood flow: `d - i`. -/
def flowDemand (d i : ℕ) : ℕ := d - i

/-- Right-hand cut capacity of `S`: `∑_j min(c, |{i∈S : i<j}|)`. -/
def cutCapacity (n c : ℕ) (S : Finset (Fin n)) : ℕ :=
  ∑ j : Fin n, min c ((S.filter fun i => i.val < j.val).card)

/-- Number of `i ∈ S` with `i.val < j.val` (the right-vertex degree of `j`). -/
def degS {n : ℕ} (S : Finset (Fin n)) (j : Fin n) : ℕ :=
  (S.filter fun i => i.val < j.val).card

/-- When `|S| ≤ c`, the cut capacity equals `∑_{i∈S} (n-1-i.val)`. -/
lemma cut_capacity_small (n c : ℕ) (S : Finset (Fin n)) (hS : S.card ≤ c) :
    cutCapacity n c S = ∑ i ∈ S, (n - 1 - i.val) := by
  classical
  unfold cutCapacity
  have hmin : ∀ j : Fin n, min c ((S.filter fun i => i.val < j.val).card)
      = (S.filter fun i => i.val < j.val).card := by
    intro j
    exact min_eq_right (le_trans (card_filter_le S _) hS)
  simp only [hmin]
  have h2 : (∑ j : Fin n, ((S.filter fun i => i.val < j.val).card))
      = ∑ j : Fin n, ∑ i ∈ S, if i.val < j.val then (1 : ℕ) else 0 := by
    refine sum_congr rfl fun j _ => ?_
    rw [card_eq_sum_ones, sum_filter]
  rw [h2, Finset.sum_comm]
  refine sum_congr rfl fun i _ => ?_
  have h1 : (∑ j : Fin n, (if i.val < j.val then 1 else 0 : ℕ))
      = (univ.filter fun j : Fin n => i.val < j.val).card :=
    sum_boole _ _
  rw [h1]
  have h3 : (univ.filter fun j : Fin n => i.val < j.val)
      = Ioi (i : Fin n) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_Ioi, Fin.lt_iff_val_lt_val]
  rw [h3, Fin.card_Ioi]

/-- Reindex a sum over `S` by the increasing enumeration `orderEmbOfFin`. -/
lemma sum_S_eq_sum_emb {n : ℕ} (S : Finset (Fin n)) (f : ℕ → ℕ) :
    (∑ i ∈ S, f i.val) = ∑ t : Fin S.card, f ((S.orderEmbOfFin rfl t).val) := by
  symm
  refine @Finset.sum_bij (Fin S.card) (Fin n) ℕ _ _ _ _ _
    (fun (t : Fin S.card) _ => S.orderEmbOfFin rfl t) ?_ ?_ ?_ ?_
  · intro t _
    exact Finset.orderEmbOfFin_mem S rfl t
  · intro t₁ _ t₂ _ heq
    exact (S.orderEmbOfFin rfl).injective heq
  · intro i hi
    have hmem : i ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hi
    obtain ⟨t, ht⟩ := hmem
    exact ⟨t, mem_univ t, ht⟩
  · intro t _
    rfl

/-- `min c a = ∑_{t<c} [t < a]`. -/
lemma min_eq_sum_ite (c a : ℕ) :
    min c a = ∑ t ∈ range c, (if t < a then 1 else 0 : ℕ) := by
  have h1 : ∑ t ∈ range c, (if t < a then 1 else 0 : ℕ)
      = ((range c).filter fun t => t < a).card :=
    sum_boole _ _
  rw [h1]
  have h2 : (range c).filter (fun t => t < a) = range (min c a) := by
    ext t
    simp only [mem_filter, mem_range]
    omega
  rw [h2, card_range]

lemma card_filter_lt_emb {n : ℕ} (S : Finset (Fin n)) (t : Fin S.card) :
    (S.filter fun i => i < S.orderEmbOfFin rfl t).card = t.val := by
  have heq : (Iio t).card = (S.filter fun i => i < S.orderEmbOfFin rfl t).card := by
    apply Finset.card_bij (fun (u : Fin S.card) _ => S.orderEmbOfFin rfl u)
    · intro u hu
      exact mem_filter.mpr ⟨S.orderEmbOfFin_mem rfl u,
        (S.orderEmbOfFin rfl).strictMono (mem_Iio.mp hu)⟩
    · intro a _ b _ hab
      exact (S.orderEmbOfFin rfl).injective hab
    · intro i hi
      obtain ⟨u, hu⟩ := (show i ∈ Set.range (S.orderEmbOfFin rfl) by
        rw [range_orderEmbOfFin]; exact (mem_filter.mp hi).1)
      refine ⟨u, mem_Iio.mpr ?_, hu⟩
      apply (S.orderEmbOfFin rfl).lt_iff_lt.mp
      rw [hu]
      exact (mem_filter.mp hi).2
  rw [← heq, Fin.card_Iio]

lemma card_filter_le_emb {n : ℕ} (S : Finset (Fin n)) (t : Fin S.card) :
    (S.filter fun i => i ≤ S.orderEmbOfFin rfl t).card = t.val + 1 := by
  have heq : (Iic t).card = (S.filter fun i => i ≤ S.orderEmbOfFin rfl t).card := by
    apply Finset.card_bij (fun (u : Fin S.card) _ => S.orderEmbOfFin rfl u)
    · intro u hu
      exact mem_filter.mpr ⟨S.orderEmbOfFin_mem rfl u,
        (S.orderEmbOfFin rfl).monotone (mem_Iic.mp hu)⟩
    · intro a _ b _ hab
      exact (S.orderEmbOfFin rfl).injective hab
    · intro i hi
      obtain ⟨u, hu⟩ := (show i ∈ Set.range (S.orderEmbOfFin rfl) by
        rw [range_orderEmbOfFin]; exact (mem_filter.mp hi).1)
      refine ⟨u, mem_Iic.mpr ?_, hu⟩
      apply (S.orderEmbOfFin rfl).le_iff_le.mp
      rw [hu]
      exact (mem_filter.mp hi).2
  rw [← heq, Fin.card_Iic]

/-- For the increasing enumeration, `i_t.val ≥ t`. -/
lemma orderEmbOfFin_val_ge {n : ℕ} (S : Finset (Fin n)) (t : Fin S.card) :
    t.val ≤ (S.orderEmbOfFin rfl t).val := by
  have hs : S.filter (fun i => i < S.orderEmbOfFin rfl t) ⊆ Iio (S.orderEmbOfFin rfl t) := by
    intro i hi
    exact mem_Iio.mpr (mem_filter.mp hi).2
  have hc := card_le_card hs
  rwa [card_filter_lt_emb, Fin.card_Iio] at hc

/-- `degS S j > t` iff `j` lies strictly after the `t`-th element of `S`. -/
lemma degS_gt_iff {n : ℕ} (S : Finset (Fin n)) (t : ℕ) (ht : t < S.card) (j : Fin n) :
    t < degS S j ↔ (S.orderEmbOfFin rfl ⟨t, ht⟩).val < j.val := by
  let u : Fin S.card := ⟨t, ht⟩
  constructor
  · intro h
    by_contra hnot
    have hj : j ≤ S.orderEmbOfFin rfl u := by exact le_of_not_gt hnot
    have hs : S.filter (fun i => i.val < j.val) ⊆ S.filter (fun i => i < S.orderEmbOfFin rfl u) := by
      intro i hi
      exact mem_filter.mpr ⟨(mem_filter.mp hi).1, lt_of_lt_of_le (mem_filter.mp hi).2 hj⟩
    have hc := card_le_card hs
    rw [card_filter_lt_emb] at hc
    unfold degS at h
    change t < _ at h
    change _ ≤ t at hc
    omega
  · intro h
    have hs : S.filter (fun i => i ≤ S.orderEmbOfFin rfl u) ⊆ S.filter (fun i => i.val < j.val) := by
      intro i hi
      exact mem_filter.mpr ⟨(mem_filter.mp hi).1, lt_of_le_of_lt (mem_filter.mp hi).2 h⟩
    have hc := card_le_card hs
    rw [card_filter_le_emb] at hc
    unfold degS
    change t + 1 ≤ _ at hc
    omega

/-- Layer form of the cut capacity. -/
lemma cutCapacity_layer (n c : ℕ) (S : Finset (Fin n)) :
    cutCapacity n c S
      = ∑ t ∈ range c, (univ.filter fun j : Fin n =>
          t < (S.filter fun i => i.val < j.val).card).card := by
  classical
  unfold cutCapacity
  conv_lhs => simp only [min_eq_sum_ite]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun t _ => by
    rw [sum_boole]
    rfl)

/-- (3.4) for `|S| ≥ c`: cut capacity equals `∑_{t<c} (n-1-i_t)`. -/
lemma cut_capacity_eq_first_c (n c : ℕ) (S : Finset (Fin n)) (hSc : c ≤ S.card) :
    cutCapacity n c S
      = ∑ t : Fin c, (n - 1 - (S.orderEmbOfFin rfl ⟨t.val, lt_of_lt_of_le t.isLt hSc⟩).val) := by
  rw [cutCapacity_layer]
  refine Finset.sum_bij (fun t ht => (⟨t, mem_range.mp ht⟩ : Fin c)) ?_ ?_ ?_ ?_
  · intro t ht
    exact mem_univ _
  · intro a _ b _ hab
    exact congrArg Fin.val hab
  · intro t _
    exact ⟨t.val, mem_range.mpr t.isLt, rfl⟩
  · intro t ht
    have htc : t < c := mem_range.mp ht
    have hts : t < S.card := lt_of_lt_of_le htc hSc
    have heq : (univ.filter fun j : Fin n => t < (S.filter fun i => i.val < j.val).card)
        = Ioi (S.orderEmbOfFin rfl ⟨t, hts⟩) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_Ioi]
      exact degS_gt_iff S t hts j
    rw [heq, Fin.card_Ioi]

/-- Cut condition (3.3) when `|S| ≤ c`: each demand `d-i` is at most `n-1-i`. -/
lemma cut_condition_small (n d c : ℕ) (hdn : d < n)
    (S : Finset (Fin n)) (hS : ∀ i ∈ S, i.val < d) (hSc : S.card ≤ c) :
    (∑ i ∈ S, (d - i.val)) ≤ cutCapacity n c S := by
  rw [cut_capacity_small n c S hSc]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' := hS i hi
  omega

/-- Split an ordered finite sum at an arbitrary prefix. -/
lemma sum_fin_prefix_tail {s c : ℕ} (hcs : c ≤ s) (f : Fin s → ℕ) :
    (∑ t, f t) =
      (∑ t : Fin c, f ⟨t.val, lt_of_lt_of_le t.isLt hcs⟩) +
      ∑ t : Fin (s - c), f ⟨c + t.val, by omega⟩ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hcs
  convert Fin.sum_univ_add f using 1 <;> congr 1
  exact Fintype.sum_equiv (finCongr (Nat.add_sub_cancel_left c k)) _ _ (by
    intro t
    congr 1)

/-- Cut condition (3.3): demands of `S` do not exceed the right capacity. -/
lemma cut_condition (n d c : ℕ) (hdn : d < n)
    (hc : d * (d + 1) + c * (c + 1) ≤ 2 * c * n)
    (S : Finset (Fin n)) (hS : ∀ i ∈ S, i.val < d) :
    (∑ i ∈ S, (d - i.val)) ≤ cutCapacity n c S := by
  by_cases hSc : S.card ≤ c
  · exact cut_condition_small n d c hdn S hS hSc
  · -- large cut: s = |S| > c, and s ≤ d since all values < d
    have hsd : S.card ≤ d := by
      have hinj : Set.InjOn (fun i : Fin n => (i : ℕ)) (S : Set _) := by
        intro a _ b _ heq
        exact Fin.ext heq
      have hmaps : Set.MapsTo (fun i : Fin n => (i : ℕ)) (S : Set _) (range d) := by
        intro i hi
        have hi' : i.val < d := hS i hi
        exact mem_range.mpr hi'
      refine le_trans (Finset.card_le_card_of_injOn (fun i : Fin n => (i : ℕ)) hmaps hinj) ?_
      rw [card_range]
    have hcs : c < S.card := lt_of_not_ge hSc
    -- reindex both sums
    rw [cut_capacity_eq_first_c n c S (le_of_lt hcs), sum_S_eq_sum_emb]
    rw [sum_fin_prefix_tail (le_of_lt hcs)]
    let e (t : Fin S.card) := S.orderEmbOfFin rfl t
    have he (t : Fin S.card) : (e t).val < d :=
      hS _ (S.orderEmbOfFin_mem rfl t)
    have hp : (∑ t : Fin c,
        (n - 1 - (e ⟨t.val, lt_of_lt_of_le t.isLt (le_of_lt hcs)⟩).val)) =
        (∑ t : Fin c,
          (d - (e ⟨t.val, lt_of_lt_of_le t.isLt (le_of_lt hcs)⟩).val)) +
          c * (n - 1 - d) := by
      have hconst : c * (n - 1 - d) = ∑ _t : Fin c, (n - 1 - d) := by simp
      rw [hconst, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _
      have := he ⟨t.val, lt_of_lt_of_le t.isLt (le_of_lt hcs)⟩
      omega
    have ht : (∑ t : Fin (S.card - c),
        (d - (e ⟨c + t.val, by omega⟩).val)) ≤
        ∑ t : Fin (d - c), (d - c - t.val) := by
      calc
        _ ≤ ∑ t : Fin (S.card - c), (d - c - t.val) := by
          apply Finset.sum_le_sum
          intro t _
          have := orderEmbOfFin_val_ge S ⟨c + t.val, by omega⟩
          change c + t.val ≤ (e _).val at this
          omega
        _ ≤ _ := by
          rw [Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range]
          exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    have htri : (∑ t : Fin (d - c), (d - c - t.val)) * 2 =
        (d - c) * (d - c + 1) := by
      rw [Fin.sum_univ_eq_sum_range]
      exact sum_range_sub_self _
    have harith : (∑ t : Fin (d - c), (d - c - t.val)) ≤ c * (n - 1 - d) := by
      have hcd : c ≤ d := by omega
      have hsub : d - c + c = d := by omega
      have hnd : n - 1 - d + d + 1 = n := by omega
      nlinarith
    change _ ≤ ∑ t : Fin c, (n - 1 - (e _).val)
    rw [hp]
    exact Nat.add_le_add_left (ht.trans harith) _

set_option maxHeartbeats 2000000 in
/-- Nested-neighborhood placement (Lemma 3.1). -/
lemma nested_placement (n d c : ℕ) (hdn : d < n)
    (hc : d * (d + 1) + c * (c + 1) ≤ 2 * c * n) :
    ∃ F : Finset (Fin n × Fin n),
      (∀ i j, (i, j) ∈ F → i.val < d ∧ i.val < j.val) ∧
      (∀ i, i.val < d → (F.filter (fun e => e.1 = i)).card = d - i.val) ∧
      (∀ j, (F.filter (fun e => e.2 = j)).card ≤ c) := by
  classical
  have hcut : ∀ S : Finset (Fin n), (∑ i ∈ S, (d - i.val)) ≤
      ∑ j : Fin n, min c ((S.filter fun i => i.val < d ∧ i.val < j.val).card) := by
    intro S
    let S' := S.filter fun i => i.val < d
    have h := cut_condition n d c hdn hc S' (by intro i hi; exact (mem_filter.mp hi).2)
    have hsum : (∑ i ∈ S, (d - i.val)) = ∑ i ∈ S', (d - i.val) := by
      symm
      apply sum_subset (filter_subset _ _)
      intro i hi hnot
      have hi' : ¬ i.val < d := by simpa [S', hi] using hnot
      exact Nat.sub_eq_zero_of_le (by omega)
    rw [hsum]
    simpa only [cutCapacity, S', filter_filter, and_assoc] using h
  obtain ⟨F, hF, hout, hin⟩ := exists_unit_placement
    (fun i : Fin n => d - i.val) c (fun (i j : Fin n) => i.val < d ∧ i.val < j.val) (by
      intro S
      convert hcut S using 1
      congr 1
      funext j
      congr 2
      ext i
      simp)
  refine ⟨F, fun i j hij => hF (i,j) hij, ?_, ?_⟩
  · intro i _
    convert hout i using 1
    congr 1
    ext e
    simp
  · intro j
    convert hin j using 1
    congr 1
    ext e
    simp

/-- Extremal construction: forward arcs from Lemma 3.1 plus backward arcs
give a loopless digraph with all outdegrees `d` and `q ≤ c`. -/
lemma extremal_construction (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    ∃ G : Digraph (Fin n),
      Loopless G ∧ (∀ v, outDeg G v = d) ∧ q G = C n d := by
  classical
  obtain ⟨F, hF, hout, hin⟩ := nested_placement n d (C n d) hd (C_spec n d hd)
  let G : Digraph (Fin n) := ⟨fun i j => (i,j) ∈ F ∨ j.val < min i.val d⟩
  have hloop : Loopless G := by
    intro i hi
    rcases hi with hf | hb
    · have := (hF i i hf).2
      omega
    · have := min_le_left i.val d
      omega
  have hrows (i : Fin n) : (F.filter fun e => e.1 = i).card = d - i.val := by
    by_cases hi : i.val < d
    · exact hout i hi
    · have he : F.filter (fun e => e.1 = i) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro e he
        have hh := hF e.1 e.2 (mem_filter.mp he).1
        exact hi ((mem_filter.mp he).2 ▸ hh.1)
      rw [he, card_empty, Nat.sub_eq_zero_of_le (by omega)]
  have hdeg (i : Fin n) : outDeg G i = d := by
    have hforward : (univ.filter fun j : Fin n => (i,j) ∈ F).card =
        (F.filter fun e => e.1 = i).card := by
      apply card_bij (fun j _ => (i,j))
      · intro j hj
        exact mem_filter.mpr ⟨(mem_filter.mp hj).2, rfl⟩
      · intro j _ j' _ he
        exact congrArg Prod.snd he
      · rintro ⟨i',j⟩ he
        obtain rfl := (mem_filter.mp he).2
        exact ⟨j, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp he).1⟩, rfl⟩
    have hback : (univ.filter fun j : Fin n => j.val < min i.val d).card = min i.val d := by
      have hmin : min i.val d < n := (min_le_left _ _).trans_lt i.isLt
      have he : (univ.filter fun j : Fin n => j.val < min i.val d) = Iio (⟨min i.val d, hmin⟩ : Fin n) := by
        ext j
        simp only [mem_filter, mem_univ, true_and, mem_Iio]
        rfl
      rw [he, Fin.card_Iio]
    have hdis : Disjoint (univ.filter fun j : Fin n => (i,j) ∈ F)
        (univ.filter fun j : Fin n => j.val < min i.val d) := by
      apply disjoint_left.mpr
      intro j hj hb
      have hh := (hF i j (mem_filter.mp hj).2).2
      have hb' := (mem_filter.mp hb).2
      have := min_le_left i.val d
      omega
    have heq : univ.filter (G.Adj i) =
        (univ.filter fun j : Fin n => (i,j) ∈ F) ∪
        (univ.filter fun j : Fin n => j.val < min i.val d) := by
      ext j
      simp only [mem_filter, mem_union, mem_univ, true_and]
      rfl
    calc
      outDeg G i = ((univ.filter fun j : Fin n => (i,j) ∈ F) ∪
          (univ.filter fun j : Fin n => j.val < min i.val d)).card := by
        unfold outDeg
        congr 1
        ext j
        simp only [mem_filter, mem_union, mem_univ, true_and]
        rfl
      _ = d := by
        rw [card_union_of_disjoint hdis, hforward, hrows, hback]
        omega
  refine ⟨G, hloop, hdeg, le_antisymm ?_ (C_le_q n d hn hd G hloop (fun i => (hdeg i).ge))⟩
  unfold q
  apply Finset.sup_le
  intro S hS
  have hs : S.Nonempty := (mem_filter.mp hS).2
  let j := S.max' hs
  have hj : j ∈ S := max'_mem S hs
  have hinc : inDegOn G S j ≤ (F.filter fun e => e.2 = j).card := by
    unfold inDegOn
    apply card_le_card_of_injOn (fun i : Fin n => (i,j))
    · intro i hi
      simp only [Finset.mem_coe, mem_filter] at hi
      have hai : G.Adj i j := hi.2
      have hij : i ≤ j := le_max' S i hi.1
      have hf : (i,j) ∈ F := by
        rcases hai with hf | hb
        · exact hf
        · have := min_le_left i.val d
          have hij' : i.val ≤ j.val := hij
          omega
      exact mem_filter.mpr ⟨hf, rfl⟩
    · intro i _ i' _ he
      exact congrArg Prod.fst he
  have hsemi : minSemiDegOn G S ≤ inDegOn G S j := by
    rw [minSemiDegOn, dif_pos hs]
    exact (Finset.inf'_le (semiDegOn G S) hj).trans (min_le_right _ _)
  exact hsemi.trans (hinc.trans (hin j))

/-- Theorem 1.1. Exact value of the extremum `q(n,d)`, with extremal loopless digraph
of all outdegrees exactly `d`. -/
theorem theorem_1_1 (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    (∀ G : Digraph (Fin n), Loopless G → (∀ v, d ≤ outDeg G v) → C n d ≤ q G) ∧
    (∃ G : Digraph (Fin n), Loopless G ∧ (∀ v, outDeg G v = d) ∧ q G = C n d) := by
  constructor
  · intro G hG hdeg
    exact C_le_q n d hn hd G hG hdeg
  · -- extremal construction: Lemma 3.1 + backward arcs
    exact extremal_construction n d hn hd

/-- Equation (1.5), with the extremum defined as a genuine minimum over graphs. -/
theorem qMin_eq_C (n d : ℕ) (hn : 0 < n) (hd : d < n) : qMin n d = C n d := by
  obtain ⟨G, hG, hdeg, hq⟩ := extremal_construction n d hn hd
  have hmem : C n d ∈ {k : ℕ | ∃ G : Digraph (Fin n),
      Loopless G ∧ (∀ v, d ≤ outDeg G v) ∧ q G = k} :=
    ⟨G, hG, fun v => (hdeg v).ge, hq⟩
  unfold qMin
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨_, hmem⟩
  rintro k ⟨H, hH, hHdeg, rfl⟩
  exact C_le_q n d hn hd H hH hHdeg

/-- Full finite identity in Theorem 1.1. -/
theorem exact_value (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    qMin n d = C n d ∧ (qMin n d : ℝ) = Nat.ceil (CReal n d) := by
  rw [qMin_eq_C n d hn hd]
  exact ⟨rfl, C_closed_form n d hn hd⟩

/-- Corollary 1.2, including the finite identity, existence of the limit,
and equality with the paper's liminf parameter. -/
theorem corollary_1_2 (α : ℝ) (hα : 0 < α) (hα' : α < 1) :
    (∀ n : ℕ, NAlpha α ≤ n → h n α = (C n (Nat.ceil (α*n)) : ℝ)/n) ∧
    Tendsto (fun n : ℕ => h n α) atTop (𝓝 (1-sqrt (1-α^2))) ∧
    hAlpha α = 1-sqrt (1-α^2) := by
  have hid : ∀ n : ℕ, NAlpha α ≤ n → h n α = (C n (Nat.ceil (α*n)) : ℝ)/n := by
    intro n hn
    obtain ⟨hn0, hdn⟩ := dense_feasible α hα hα' n hn
    unfold h
    rw [qMin_eq_C n _ hn0 hdn]
  have ht : Tendsto (fun n : ℕ => h n α) atTop (𝓝 (1-sqrt (1-α^2))) := by
    apply (C_dense_limit α hα hα').congr'
    exact eventually_atTop.mpr ⟨NAlpha α, fun n hn => (hid n hn).symm⟩
  exact ⟨hid, ht, ht.liminf_eq⟩

/-- The directed degeneracy reformulation in Section 4. -/
theorem q_le_iff_weaklyDegenerate {V : Type*} [Fintype V] (G : Digraph V) (c : ℕ) :
    q G ≤ c ↔ WeaklyDegenerate G (c+1) := by
  classical
  constructor
  · intro hq S hS
    obtain ⟨v, hv, hc⟩ := exists_semiDegOn_le (G := G) rfl hS
    have hh : semiDegOn G S v ≤ c := hc.trans hq
    have hm : outDegOn G S v ≤ c ∨ inDegOn G S v ≤ c := min_le_iff.mp hh
    exact ⟨v, hv, hm.imp (fun h => by omega) (fun h => by omega)⟩
  · intro hdeg
    unfold q
    apply Finset.sup_le
    intro S hS
    have hs : S.Nonempty := (mem_filter.mp hS).2
    obtain ⟨v, hv, hlow⟩ := hdeg S hs
    rw [minSemiDegOn, dif_pos hs]
    apply (inf'_le_iff hs).mpr
    refine ⟨v, hv, ?_⟩
    unfold semiDegOn
    exact min_le_iff.mpr (hlow.imp (fun h => by omega) (fun h => by omega))

/-- Demand of left vertex `i` in the nested-neighborhood flow: `d - i`. -/
theorem lemma_3_1 (n d c : ℕ) (hd : 1 ≤ d) (hdn : d < n)
    (hc : d * (d + 1) + c * (c + 1) ≤ 2 * c * n) :
    ∃ F : Finset (Fin n × Fin n),
      (∀ i j, (i, j) ∈ F → i.val < d ∧ i.val < j.val) ∧
      (∀ i, i.val < d → (F.filter (fun e => e.1 = i)).card = d - i.val) ∧
      (∀ j, (F.filter (fun e => e.2 = j)).card ≤ c) :=
  nested_placement n d c hdn hc

end SemidegreeExt
