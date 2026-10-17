import MEJF.HeterogeneousGraph
import MEJF.OrderStatistics
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fin.Rev

/-! The exact sorted degree-demand frontier (6.9), derived from actual graph support. -/
namespace MEJF.HeterogeneousFrontier
open Finset HeterogeneousGraph
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {N : ℕ}

def capacity (N r : ℕ) : ℕ := r.choose 2 + r*(N-r)

def Admissible (w : Fin N → ℕ) (S : Finset (Fin N)) : Prop :=
  ∀ A ⊆ S, ∑ i ∈ A, w i ≤ capacity N A.card

/-- Actual graph support, including exact requested degrees and zero outside. -/
def Supported (w : Fin N → ℕ) (S : Finset (Fin N)) : Prop :=
  ∃ R : Fin N → Fin N → Prop, (∀ i j, R i j → ¬ R j i) ∧
    (∀ i ∈ S, GraphBound.outDegree R i = w i) ∧
    (∀ i ∉ S, GraphBound.outDegree R i = 0)

lemma supported_iff_admissible (w : Fin N → ℕ) (S : Finset (Fin N)) :
    Supported w S ↔ Admissible w S := by
  simpa only [Supported, Admissible, capacity, Fintype.card_fin] using oriented_degree_on_iff_cuts S w

def initialSet (N s : ℕ) : Finset (Fin N) := univ.filter fun i => i.val < s

lemma prefix_image (s : ℕ) (hs : s ≤ N) :
    (univ : Finset (Fin s)).image (Fin.castLE hs) = initialSet N s := by
  ext i
  simp only [mem_image, mem_univ, true_and, initialSet, mem_filter]
  constructor
  · rintro ⟨k,rfl⟩
    exact k.isLt
  · intro hi
    exact ⟨⟨i.val,hi⟩,Fin.ext rfl⟩

lemma card_prefix (s : ℕ) (hs : s ≤ N) : (initialSet N s).card = s := by
  rw [← prefix_image s hs, card_image_of_injective _ (Fin.castLE_injective hs)]
  simp

/-- A strictly increasing finite sequence of naturals is bounded below by its index. -/
lemma strictMono_index_le {s : ℕ} (f : Fin s → ℕ) (hf : StrictMono f) (i : Fin s) :
    i.val ≤ f i := by
  have aux : ∀ k (hk : k < s), k ≤ f ⟨k,hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hprev : k < s := by omega
      have hstep := hf (show (⟨k,hprev⟩ : Fin s) < ⟨k+1,hk⟩ from by simp)
      have := ih hprev
      omega
  exact aux i.val i.isLt

/-- The kth selected index among r indices below s is at most s-r+k. -/
lemma strictMono_index_upper {r s : ℕ} (f : Fin r → Fin s) (hf : StrictMono f)
    (i : Fin r) : (f i).val ≤ s-r+i.val := by
  let g : Fin r → ℕ := fun k => (f k.rev).rev.val
  have hg : StrictMono g := by
    intro a b hab
    have hrev : b.rev < a.rev := Fin.rev_lt_rev.mpr hab
    have hf' := hf hrev
    exact Fin.rev_lt_rev.mpr hf'
  have h := strictMono_index_le g hg i.rev
  simp only [g, Fin.rev_rev, Fin.val_rev] at h
  have hi := i.isLt
  have hfi := (f i).isLt
  omega

lemma admissible_image_iff {K : Type*} [Fintype K] [DecidableEq K]
    (w : Fin N → ℕ) (f : K → Fin N) (hf : Function.Injective f) :
    Admissible w (univ.image f) ↔
      ∀ C : Finset K, ∑ i ∈ C, w (f i) ≤ capacity N C.card := by
  constructor
  · intro h C
    have hc := h (C.image f) (image_subset_image (subset_univ C))
    simpa only [sum_image hf.injOn, card_image_of_injective _ hf] using hc
  · intro h A hA
    obtain ⟨C,hC⟩ := subset_univ_image_iff.mp hA
    rw [← hC, sum_image hf.injOn, card_image_of_injective _ hf]
    exact h C

/-- Among supports of size s, the s smallest monotone demands are easiest. -/
theorem prefix_admissible_of_support (w : Fin N → ℕ) (hw : Monotone w)
    (S : Finset (Fin N)) (s : ℕ) (hS : S.card = s) (had : Admissible w S) :
    Admissible w (initialSet N s) := by
  have hs : s ≤ N := by simpa [hS] using card_le_univ S
  let e : Fin s ↪o Fin N := S.orderEmbOfFin hS
  have him : univ.image e = S := S.image_orderEmbOfFin_univ hS
  have hsource : ∀ C : Finset (Fin s), ∑ i ∈ C, w (e i) ≤ capacity N C.card := by
    apply (admissible_image_iff w e e.injective).mp
    simpa only [him] using had
  rw [← prefix_image s hs]
  apply (admissible_image_iff w (Fin.castLE hs) (Fin.castLE_injective hs)).mpr
  intro C
  apply le_trans (Finset.sum_le_sum (fun i _ => ?_)) (hsource C)
  apply hw
  change i.val ≤ (e i).val
  exact strictMono_index_le (fun k => (e k).val) (Fin.val_strictMono.comp e.strictMono) i

def tailIndex (s r : ℕ) (hs : s ≤ N) (hr : r ≤ s) (k : Fin r) : Fin N :=
  ⟨s-r+k.val,by omega⟩

def tailSum (w : Fin N → ℕ) (s r : ℕ) (hs : s ≤ N) (hr : r ≤ s) : ℕ :=
  ∑ k : Fin r, w (tailIndex s r hs hr k)

lemma tailIndex_injective (s r : ℕ) (hs : s ≤ N) (hr : r ≤ s) :
    Function.Injective (tailIndex s r hs hr) := by
  intro a b hab
  apply Fin.ext
  have := congrArg Fin.val hab
  dsimp [tailIndex] at this
  omega

lemma tail_subset_prefix (s r : ℕ) (hs : s ≤ N) (hr : r ≤ s) :
    (univ.image (tailIndex s r hs hr)) ⊆ initialSet N s := by
  intro i hi
  obtain ⟨k,_,rfl⟩ := mem_image.mp hi
  simp only [initialSet, mem_filter, mem_univ, true_and, tailIndex]
  have := k.isLt
  omega

/-- A monotone weight's maximum sum over r elements of the first s positions
is exactly the sum of the last r of those s positions. -/
theorem subset_sum_le_tailSum (w : Fin N → ℕ) (hw : Monotone w)
    (s : ℕ) (hs : s ≤ N) (A : Finset (Fin N)) (hA : A ⊆ initialSet N s) :
    ∑ i ∈ A, w i ≤ tailSum w s A.card hs (by
      have h := card_le_card hA
      simpa only [card_prefix s hs] using h) := by
  let r := A.card
  have hr : r ≤ s := by
    have h := card_le_card hA
    simpa only [card_prefix s hs] using h
  let e : Fin r ↪o Fin N := A.orderEmbOfFin rfl
  let f : Fin r → Fin s := fun k =>
    ⟨(e k).val,(mem_filter.mp (hA (A.orderEmbOfFin_mem rfl k))).2⟩
  have hf : StrictMono f := by
    intro a b hab
    exact e.strictMono hab
  have hsum : (∑ i ∈ A, w i) = ∑ k : Fin r, w (e k) := by
    have h := Finset.sum_image (f := w) (s := univ) e.injective.injOn
    rw [A.image_orderEmbOfFin_univ rfl] at h
    exact h
  rw [hsum]
  apply Finset.sum_le_sum
  intro k hk
  apply hw
  change (f k).val ≤ s-r+k.val
  exact strictMono_index_upper f hf k

/-- Precisely the largest-r constraints from (6.9), with the vacuous r=0 case
included and zero-based indices representing the paper's one-based ranks. -/
def SortedCell (w : Fin N → ℕ) (s : ℕ) : Prop :=
  ∃ hs : s ≤ N, ∀ r (hr : r ≤ s), tailSum w s r hs hr ≤ capacity N r

theorem prefix_admissible_iff_sortedCell (w : Fin N → ℕ) (hw : Monotone w)
    (s : ℕ) (hs : s ≤ N) : Admissible w (initialSet N s) ↔ SortedCell w s := by
  constructor
  · intro h
    refine ⟨hs,fun r hr => ?_⟩
    have hc := h (univ.image (tailIndex s r hs hr)) (tail_subset_prefix s r hs hr)
    simpa only [sum_image (tailIndex_injective s r hs hr).injOn,
      card_image_of_injective _ (tailIndex_injective s r hs hr), card_univ,
      Fintype.card_fin, tailSum] using hc
  · rintro ⟨hs',h⟩ A hA
    have hr : A.card ≤ s := by
      have hh := card_le_card hA
      simpa only [card_prefix s hs] using hh
    exact (subset_sum_le_tailSum w hw s hs A hA).trans (h A.card hr)

/-- Cut feasibility is invariant under a permutation of labels. -/
lemma admissible_reindex_iff (w : Fin N → ℕ) (σ : Equiv.Perm (Fin N))
    (S : Finset (Fin N)) :
    Admissible (w ∘ σ) S ↔ Admissible w (S.image σ) := by
  constructor
  · intro h A hA
    obtain ⟨B,hBS,hBA⟩ := subset_image_iff.mp hA
    rw [← hBA, sum_image σ.injective.injOn, card_image_of_injective _ σ.injective]
    exact h B hBS
  · intro h A hA
    have hh := h (A.image σ) (image_subset_image hA)
    simpa only [sum_image σ.injective.injOn,
      card_image_of_injective _ σ.injective, Function.comp_apply] using hh

/-- Exactly s demands are supportable by an actual oriented graph iff the
largest-r constraints among the globally smallest s sorted demands hold. -/
theorem supported_card_iff_sortedCell (w : Fin N → ℕ) (s : ℕ) :
    (∃ S : Finset (Fin N), S.card = s ∧ Supported w S) ↔
      SortedCell (OrderStatistics.stat w) s := by
  let σ := Tuple.sort w
  have hmono : Monotone (w ∘ σ) := Tuple.monotone_sort w
  constructor
  · rintro ⟨S,hcard,hgraph⟩
    have had : Admissible w S := (supported_iff_admissible w S).mp hgraph
    let T := S.image σ.symm
    have hTcard : T.card = s := by
      simpa only [T,card_image_of_injective _ σ.symm.injective] using hcard
    have hTad : Admissible (w ∘ σ) T := by
      apply (admissible_reindex_iff w σ T).mpr
      simpa [T,image_image,Function.comp_def] using had
    have hs : s ≤ N := by simpa [hcard] using card_le_univ S
    have hp := prefix_admissible_of_support (w ∘ σ) hmono T s hTcard hTad
    exact (prefix_admissible_iff_sortedCell (w ∘ σ) hmono s hs).mp hp
  · intro hcell
    obtain ⟨hs,hconds⟩ := hcell
    have hp : Admissible (w ∘ σ) (initialSet N s) :=
      (prefix_admissible_iff_sortedCell (w ∘ σ) hmono s hs).mpr ⟨hs,hconds⟩
    refine ⟨(initialSet N s).image σ,?_,?_⟩
    · rw [card_image_of_injective _ σ.injective, card_prefix s hs]
    · apply (supported_iff_admissible _ _).mpr
      exact (admissible_reindex_iff w σ (initialSet N s)).mp hp

/-- Cardinalities achievable by genuine finite oriented graphs. -/
def supportedSizes (w : Fin N → ℕ) : Finset ℕ :=
  (range (N+1)).filter fun s => ∃ S : Finset (Fin N), S.card = s ∧ Supported w S

/-- The exact finite sorted constraints from (6.9). -/
def sortedSizes (w : Fin N → ℕ) : Finset ℕ :=
  (range (N+1)).filter fun s => SortedCell (OrderStatistics.stat w) s

/-- Actual largest support size, defined independently from the sorted formula. -/
def maximumSupported (w : Fin N → ℕ) : ℕ := (supportedSizes w).sup id

/-- The paper's s* from (6.9), with its finite maximum evaluated as a finite sup. -/
def sStar (w : Fin N → ℕ) : ℕ := (sortedSizes w).sup id

theorem supportedSizes_eq_sortedSizes (w : Fin N → ℕ) :
    supportedSizes w = sortedSizes w := by
  ext s
  simp only [supportedSizes,sortedSizes,mem_filter,supported_card_iff_sortedCell]

/-- Exact identification of (6.9) with the largest genuinely supportable set. -/
theorem maximumSupported_eq_sStar (w : Fin N → ℕ) : maximumSupported w = sStar w := by
  unfold maximumSupported sStar
  rw [supportedSizes_eq_sortedSizes]

lemma empty_supported (w : Fin N → ℕ) : Supported w ∅ := by
  apply (supported_iff_admissible w ∅).mpr
  intro A hA
  have : A = ∅ := subset_empty.mp hA
  simp [this,capacity]

lemma supportedSizes_nonempty (w : Fin N → ℕ) : (supportedSizes w).Nonempty := by
  refine ⟨0,mem_filter.mpr ⟨?_,∅,by simp,empty_supported w⟩⟩
  exact mem_range.mpr (by omega)

/-- The finite maximum is attained by an actual oriented graph, including the
all-zero feasible support case. -/
theorem sStar_attained (w : Fin N → ℕ) :
    ∃ S : Finset (Fin N), S.card = sStar w ∧ Supported w S := by
  have hm := Finset.sup_mem_of_nonempty (s := supportedSizes w) (f := id)
    (supportedSizes_nonempty w)
  obtain ⟨s,hs,hse⟩ := hm
  have hfeas := (mem_filter.mp hs).2
  have heq : s = sStar w := by
    exact (show s = maximumSupported w from hse).trans (maximumSupported_eq_sStar w)
  simpa only [heq] using hfeas

/-- Any actual oriented graph whose degrees meet demands on a set supports no
more than s* vertices. Exact degree equality is unnecessary for the upper bound. -/
theorem qualifying_card_le_sStar (w : Fin N → ℕ) (R : Fin N → Fin N → Prop)
    (hR : ∀ i j, R i j → ¬ R j i) (S : Finset (Fin N))
    (hdeg : ∀ i ∈ S, w i ≤ GraphBound.outDegree R i) : S.card ≤ sStar w := by
  have had : Admissible w S := by
    intro A hAS
    simpa only [capacity, Fintype.card_fin] using
      demand_cut_of_oriented R hR w A (fun i hi => hdeg i (hAS hi))
  have hsupp : Supported w S := (supported_iff_admissible w S).mpr had
  have hmem : S.card ∈ supportedSizes w := by
    apply mem_filter.mpr
    refine ⟨mem_range.mpr ?_,S,rfl,hsupp⟩
    have := card_le_univ S
    simpa only [Fintype.card_fin] using Nat.lt_succ_of_le this
  have hle : S.card ≤ maximumSupported w := Finset.le_sup (f := id) hmem
  rw [maximumSupported_eq_sStar] at hle
  exact hle

/-- The sorted frontier is a symmetric function of the demand tuple. -/
theorem sStar_perm (w : Fin N → ℕ) (σ : Equiv.Perm (Fin N)) :
    sStar (w ∘ σ) = sStar w := by
  have hstat : OrderStatistics.stat (w ∘ σ) = OrderStatistics.stat w :=
    funext (OrderStatistics.stat_perm w σ)
  unfold sStar sortedSizes
  rw [hstat]

lemma multiset_filter_decidable_irrel {B : Type*} (p : B → Prop)
    (d₁ d₂ : DecidablePred p) (s : Multiset B) :
    @Multiset.filter B p d₁ s = @Multiset.filter B p d₂ s := by
  cases Subsingleton.elim d₁ d₂
  rfl

/-- Equality of demand multisets gives equality of every sorted rank. -/
lemma stat_eq_of_multiset_eq (u v : Fin N → ℕ)
    (hm : univ.val.map u = univ.val.map v) :
    OrderStatistics.stat u = OrderStatistics.stat v := by
  have hc : ∀ x, OrderStatistics.count u (· ≤ x) = OrderStatistics.count v (· ≤ x) := by
    intro x
    have h := congrArg (fun s : Multiset ℕ => (s.filter (fun a => a ≤ x)).card) hm
    simp only [Multiset.filter_map,Multiset.card_map,Function.comp_def] at h
    simp only [OrderStatistics.count,Finset.card_def,Finset.filter_val]
    convert h using 1 <;> congr 1 <;> exact multiset_filter_decidable_irrel _ _ _ _
  funext k
  apply le_antisymm
  · apply (OrderStatistics.stat_le_iff_count u k _).mpr
    rw [hc]
    exact (OrderStatistics.stat_le_iff_count v k _).mp le_rfl
  · apply (OrderStatistics.stat_le_iff_count v k _).mpr
    rw [← hc]
    exact (OrderStatistics.stat_le_iff_count u k _).mp le_rfl

/-- Therefore s* depends only on the unordered demand multiset. -/
theorem sStar_eq_of_multiset_eq (u v : Fin N → ℕ)
    (hm : univ.val.map u = univ.val.map v) : sStar u = sStar v := by
  have hstat := stat_eq_of_multiset_eq u v hm
  unfold sStar sortedSizes
  rw [hstat]

/-- The source's displayed edge capacity r(2N-r-1)/2, including r=0,
is exactly the choose-plus-cross-edge form used by the Hall proof. -/
lemma capacity_eq_source_formula (r : ℕ) (hr : r ≤ N) :
    capacity N r = r*(2*N-r-1)/2 := by
  by_cases hz : r = 0
  · simp [hz,capacity]
  · have hN : r+(N-r) = N := Nat.add_sub_of_le hr
    have hlin : (2*N-r-1)+r+1 = 2*N := by omega
    have hc := HeterogeneousGraph.two_choose_two r
    have heq : 2*capacity N r = r*(2*N-r-1) := by
      dsimp [capacity]
      nlinarith
    rw [← heq]
    omega

end
end MEJF.HeterogeneousFrontier
