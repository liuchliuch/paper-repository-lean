import K44K35Free.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Log

/-!
# Padding and the final amplification in Theorem 1

The lemmas here prove that adjoining isolated vertices preserves bipartiteness,
`K_{3,5}`-freeness, and the exact number of `K_{4,4}` copies. The final conditional
engine converts the paper's construction at powers of three to every sufficiently
large number of vertices. Its construction premise is explicitly stated; it is
not a proof of the geometric construction.
-/

namespace K44K35Free
open Finset

variable {V W : Type} [Fintype V] [Fintype W]

omit [Fintype V] [Fintype W] in
/-- A finite subset of the image of an embedding is the image of its preimage. -/
theorem map_preimage_of_range (f : V ↪ W) (A : Finset W)
    (hA : ∀ a ∈ A, a ∈ Set.range f) :
    (A.preimage f f.injective.injOn).map f = A := by
  classical
  ext w
  simp only [mem_map, mem_preimage]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact hv
  · intro hw
    obtain ⟨v, rfl⟩ := hA w hw
    exact ⟨v, hw, rfl⟩

/-- Pushing a graph along an embedding adds only isolated vertices, so no new
forbidden common neighbourhood is created. -/
theorem isK35Free_map (G : SimpleGraph V) (f : V ↪ W) (hG : IsK35Free G) :
    IsK35Free (G.map f) := by
  classical
  intro X hX
  by_cases hR : ∀ x ∈ X, x ∈ Set.range f
  · let Y := X.preimage f f.injective.injOn
    have hmap : Y.map f = X := map_preimage_of_range f X hR
    have hY : Y.card = 3 := by rw [← hX, ← hmap, card_map]
    have hsub : commonNeighbors (G.map f) X ⊆ (commonNeighbors G Y).map f := by
      intro w hw
      obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < X.card)
      obtain ⟨v, u, hvu, hv, hu⟩ := (SimpleGraph.map_adj f G w x).mp
        (mem_commonNeighbors.mp hw x hx)
      apply mem_map.mpr
      refine ⟨v, mem_commonNeighbors.mpr ?_, hv⟩
      intro y hy
      have hfy : f y ∈ X := by rw [← hmap]; exact mem_map.mpr ⟨y, hy, rfl⟩
      have hh := mem_commonNeighbors.mp hw (f y) hfy
      rw [← hv, SimpleGraph.map_adj_apply] at hh
      exact hh
    exact (card_le_card hsub).trans (by simpa using hG Y hY)
  · have hempty : commonNeighbors (G.map f) X = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro w hw
      apply hR
      intro x hx
      obtain ⟨v, u, hvu, hv, hu⟩ := (SimpleGraph.map_adj f G w x).mp
        (mem_commonNeighbors.mp hw x hx)
      exact ⟨u, hu⟩
    rw [hempty]
    simp

omit [Fintype V] [Fintype W] in
/-- A copy supported on the original vertices is preserved by graph padding. -/
theorem isK44Pair_map_iff (G : SimpleGraph V) (f : V ↪ W) (A B : Finset V) :
    IsK44Pair (G.map f) (A.map f) (B.map f) ↔ IsK44Pair G A B := by
  classical
  simp only [IsK44Pair, card_map]
  constructor
  · rintro ⟨hA, hB, hD, hAdj⟩
    refine ⟨hA, hB, ?_, ?_⟩
    · exact Finset.disjoint_left.mpr fun a ha hb =>
        Finset.disjoint_left.mp hD
          (mem_map.mpr ⟨a, ha, rfl⟩) (mem_map.mpr ⟨a, hb, rfl⟩)
    · intro a b ha hb
      exact SimpleGraph.map_adj_apply.mp (hAdj (mem_map.mpr ⟨a, ha, rfl⟩)
        (mem_map.mpr ⟨b, hb, rfl⟩))
  · rintro ⟨hA, hB, hD, hAdj⟩
    refine ⟨hA, hB, ?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro w hwA hwB
      obtain ⟨a, ha, rfl⟩ := mem_map.mp hwA
      obtain ⟨b, hb, hab⟩ := mem_map.mp hwB
      have heq : b = a := f.injective hab
      subst b
      exact Finset.disjoint_left.mp hD ha hb
    · intro a b ha hb
      obtain ⟨a', ha', rfl⟩ := mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := mem_map.mp hb
      exact SimpleGraph.map_adj_apply.mpr (hAdj ha' hb')

omit [Fintype V] [Fintype W] in
/-- Every copy in a padded graph uses only original vertices. -/
theorem isK44Pair_map_range (G : SimpleGraph V) (f : V ↪ W)
    {A B : Finset W} (h : IsK44Pair (G.map f) A B) :
    (∀ a ∈ A, a ∈ Set.range f) ∧ (∀ b ∈ B, b ∈ Set.range f) := by
  classical
  obtain ⟨a₀, ha₀⟩ := card_pos.mp (by rw [h.1]; norm_num : 0 < A.card)
  obtain ⟨b₀, hb₀⟩ := card_pos.mp (by rw [h.2.1]; norm_num : 0 < B.card)
  constructor
  · intro a ha
    obtain ⟨a', b', _, ha', _⟩ := (SimpleGraph.map_adj f G a b₀).mp (h.2.2.2 ha hb₀)
    exact ⟨a', ha'⟩
  · intro b hb
    obtain ⟨a', b', _, _, hb'⟩ := (SimpleGraph.map_adj f G a₀ b).mp (h.2.2.2 ha₀ hb)
    exact ⟨b', hb'⟩

/-- The embedding on pairs of finite vertex sets induced by a vertex embedding. -/
def sidePairEmbedding (f : V ↪ W) :
    (Finset V × Finset V) ↪ (Finset W × Finset W) :=
  { toFun := fun p => (p.1.map f, p.2.map f)
    inj' := by
      rintro ⟨A, B⟩ ⟨C, D⟩ h
      have hA := Finset.map_injective f (congrArg Prod.fst h)
      have hB := Finset.map_injective f (congrArg Prod.snd h)
      exact Prod.ext hA hB }

/-- Padding gives a bijection of the oriented copies. -/
theorem orientedK44_map (G : SimpleGraph V) (f : V ↪ W) :
    orientedK44 (G.map f) = (orientedK44 G).map (sidePairEmbedding f) := by
  classical
  ext p
  rcases p with ⟨A, B⟩
  constructor
  · intro hp
    have h := mem_orientedK44.mp hp
    obtain ⟨hA, hB⟩ := isK44Pair_map_range G f h
    let A' := A.preimage f f.injective.injOn
    let B' := B.preimage f f.injective.injOn
    have hmA : A'.map f = A := map_preimage_of_range f A hA
    have hmB : B'.map f = B := map_preimage_of_range f B hB
    apply mem_map.mpr
    refine ⟨(A', B'), mem_orientedK44.mpr ?_, ?_⟩
    · apply (isK44Pair_map_iff G f A' B').mp
      rwa [hmA, hmB]
    · change (A'.map f, B'.map f) = (A, B)
      rw [hmA, hmB]
  · rintro hp
    obtain ⟨⟨A', B'⟩, hp', hp⟩ := mem_map.mp hp
    change (A'.map f, B'.map f) = (A, B) at hp
    cases hp
    exact mem_orientedK44.mpr ((isK44Pair_map_iff G f A' B').mpr
      (mem_orientedK44.mp hp'))

/-- Adjoining isolated vertices preserves the exact copy count. -/
theorem numK44_map (G : SimpleGraph V) (f : V ↪ W) :
    numK44 (G.map f) = numK44 G := by
  unfold numK44 numOrientedK44
  rw [orientedK44_map, card_map]

/-- Actual padding to any larger vertex count. -/
theorem pad_graph (G : SimpleGraph V) (hG : IsK35Free G) (hbip : G.IsBipartite)
    (n : ℕ) (hn : Fintype.card V ≤ n) :
    ∃ (W : Type) (_ : Fintype W) (H : SimpleGraph W),
      Fintype.card W = n ∧ IsK35Free H ∧ H.IsBipartite ∧ numK44 H = numK44 G := by
  let W := V ⊕ Fin (n - Fintype.card V)
  let f : V ↪ W := Function.Embedding.inl
  refine ⟨W, inferInstance, G.map f, ?_, isK35Free_map G f hG, hbip.map f, numK44_map G f⟩
  simp only [W, Fintype.card_sum, Fintype.card_fin]
  omega

/-- The largest relevant power of three has the two bounds used in the paper. -/
theorem exists_power_three_scale (n : ℕ) (hn : 2 ≤ n) :
    ∃ k : ℕ, 2 * (3 ^ k) ^ 3 ≤ n ∧ n < 54 * (3 ^ k) ^ 3 := by
  let k := Nat.log 27 (n / 2)
  have hpos : n / 2 ≠ 0 := by omega
  have hlow : 27 ^ k ≤ n / 2 := Nat.pow_log_le_self 27 hpos
  have hhigh : n / 2 < 27 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hc : (3 ^ k) ^ 3 = 27 ^ k := by
    rw [← pow_mul, Nat.mul_comm k 3, pow_mul]
    norm_num
  refine ⟨k, ?_, ?_⟩
  · rw [hc]
    omega
  · rw [hc]
    rw [pow_succ] at hhigh
    omega

/-- At sufficiently large vertex sizes, the chosen power of three also exceeds
any fixed field-size threshold. -/
theorem exists_power_three_scale_ge (q₀ n : ℕ)
    (hn : max 2 (54 * q₀ ^ 3) ≤ n) :
    ∃ k : ℕ, q₀ ≤ 3 ^ k ∧ 2 * (3 ^ k) ^ 3 ≤ n ∧ n < 54 * (3 ^ k) ^ 3 := by
  obtain ⟨k, hlo, hhi⟩ := exists_power_three_scale n (le_trans (le_max_left _ _) hn)
  refine ⟨k, ?_, hlo, hhi⟩
  by_contra h
  have hq : 3 ^ k ≤ q₀ := by omega
  have hp : (3 ^ k) ^ 3 ≤ q₀ ^ 3 := Nat.pow_le_pow_left hq 3
  have hn₀ : 54 * q₀ ^ 3 ≤ n := le_trans (le_max_right _ _) hn
  omega

/-- The conditional final amplification step of Theorem 1. Its premise is the
actual existence of the constructed bipartite graphs at every sufficiently large
power of three, with the stated number of copies. Padding and all asymptotic
arithmetic are proved here. -/
theorem amplify_power_three_construction
    (κ : ℝ) (hκ : 0 < κ) (q₀ : ℕ)
    (hconstruct : ∀ k : ℕ, q₀ ≤ 3 ^ k →
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
        Fintype.card V = 2 * (3 ^ k) ^ 3 ∧ IsK35Free G ∧ G.IsBipartite ∧
          κ * (3 ^ k : ℝ) ^ 9 ≤ numK44 G) :
    0 < κ / 54 ^ 3 ∧
      ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
          Fintype.card V = n ∧ IsK35Free G ∧ G.IsBipartite ∧
            κ / 54 ^ 3 * (n : ℝ) ^ 3 ≤ numK44 G := by
  refine ⟨by positivity, max 2 (54 * q₀ ^ 3), ?_⟩
  intro n hn
  obtain ⟨k, hq, hlo, hhi⟩ := exists_power_three_scale_ge q₀ n hn
  obtain ⟨V, instV, G, hcard, hfree, hbip, hcopies⟩ := hconstruct k hq
  obtain ⟨W, instW, H, hW, hHfree, hHbip, hcount⟩ :=
    pad_graph G hfree hbip n (by rw [hcard]; exact hlo)
  refine ⟨W, instW, H, hW, hHfree, hHbip, ?_⟩
  rw [hcount]
  have hnr : (n : ℝ) ≤ 54 * (3 ^ k : ℝ) ^ 3 := by
    exact_mod_cast hhi.le
  have hpow : (n : ℝ) ^ 3 ≤ (54 * (3 ^ k : ℝ) ^ 3) ^ 3 := by
    gcongr
  have hscale : (n : ℝ) ^ 3 ≤ 54 ^ 3 * (3 ^ k : ℝ) ^ 9 := by
    convert hpow using 1
    ring
  have hmul := mul_le_mul_of_nonneg_left hscale (le_of_lt hκ)
  have hbound : κ / 54 ^ 3 * (n : ℝ) ^ 3 ≤ κ * (3 ^ k : ℝ) ^ 9 := by
    nlinarith
  exact hbound.trans hcopies

end K44K35Free
