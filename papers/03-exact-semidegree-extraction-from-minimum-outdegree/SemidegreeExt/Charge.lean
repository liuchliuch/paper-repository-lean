import SemidegreeExt.Peeling
import Mathlib.Tactic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup
import Mathlib.Order.Interval.Finset.Nat

/-!
# Pointwise charge bound (incremental)
-/

open Finset Digraph Nat
open Classical

namespace SemidegreeExt

variable {n : ℕ} {G : Digraph (Fin n)} {c : ℕ}

/-- Marked arcs charged to `v`. -/
noncomputable def charged (G : Digraph (Fin n)) (c : ℕ) (L : List (Fin n)) (v : Fin n) :
    Finset (Fin n × Fin n) :=
  (markedOfList G c L).filter fun e => chargeTo L e = v

/-- Vertices deleted strictly after `v` in `L`. -/
def laterFinset (L : List (Fin n)) (v : Fin n) : Finset (Fin n) :=
  univ.filter fun u => L.idxOf v < L.idxOf u

lemma mem_laterFinset_iff {L : List (Fin n)} {v u : Fin n} :
    u ∈ laterFinset L v ↔ L.idxOf v < L.idxOf u := by
  simp [laterFinset]

/-- A later vertex of a complete list lies in the peel prefix. -/
lemma later_subset_peelPrefix {L : List (Fin n)} (hcomplete : L.toFinset = univ)
    (v : Fin n) :
    laterFinset L v ⊆ peelPrefix L (L.idxOf v) := by
  intro u hu
  have hu_idx : L.idxOf v < L.idxOf u := mem_laterFinset_iff.1 hu
  have huL : u ∈ L := by
    have h : u ∈ univ := mem_univ u
    rw [← hcomplete] at h
    exact List.mem_toFinset.1 h
  exact mem_peelPrefix_iff.2 ⟨huL, Nat.le_of_lt hu_idx⟩


/-- Case analysis of `chargeTo` and `markedOfList` at a fixed charged vertex. -/
lemma charged_cases {G : Digraph (Fin n)} {c : ℕ} {L : List (Fin n)} {v : Fin n}
    {a b : Fin n} (h : (a, b) ∈ charged G c L v) :
    (a = v ∧ L.idxOf a < L.idxOf b ∧ G.Adj a b ∧ typeOOf G c L a) ∨
    (b = v ∧ L.idxOf b < L.idxOf a ∧ G.Adj a b ∧ ¬ typeOOf G c L b) := by
  simp only [charged, mem_filter, mem_univ, true_and] at h
  obtain ⟨hmarked, hcharge⟩ := h
  simp only [markedOfList, mem_filter, mem_univ, true_and] at hmarked
  obtain ⟨hadj, hmark⟩ := hmarked
  by_cases h12 : L.idxOf a < L.idxOf b
  · have hcharge' : a = v := by
      simp only [chargeTo, if_pos h12] at hcharge
      exact hcharge
    have htype : typeOOf G c L a := by
      simpa [h12] using hmark
    exact Or.inl ⟨hcharge', h12, hadj, htype⟩
  · have h21 : L.idxOf b < L.idxOf a := by
      by_contra hne
      push_neg at hne
      have heq : L.idxOf a = L.idxOf b := by omega
      have hfalse : False := by
        have hmark' : (if L.idxOf a < L.idxOf b then typeOOf G c L a
            else if L.idxOf b < L.idxOf a then ¬ typeOOf G c L b else False) := hmark
        rw [if_neg h12] at hmark'
        rw [if_neg (by omega)] at hmark'
        exact hmark'
      exact hfalse
    have hcharge' : b = v := by
      simp only [chargeTo, if_neg h12] at hcharge
      exact hcharge
    have htype : ¬ typeOOf G c L b := by
      have hmark' : (if L.idxOf a < L.idxOf b then typeOOf G c L a
          else if L.idxOf b < L.idxOf a then ¬ typeOOf G c L b else False) := hmark
      rw [if_neg h12] at hmark'
      rw [if_pos h21] at hmark'
      exact hmark'
    exact Or.inr ⟨hcharge', h21, hadj, htype⟩

/-- Under type O, charged arcs are out-arcs of `v` to later vertices. -/
lemma charged_typeO_subset {G : Digraph (Fin n)} {c : ℕ} {L : List (Fin n)}
    {v : Fin n} (htype : typeOOf G c L v) :
    charged G c L v ⊆ (univ.filter fun e : Fin n × Fin n =>
      e.1 = v ∧ e.2 ∈ laterFinset L v ∧ G.Adj e.1 e.2) := by
  intro e he
  obtain ⟨a, b⟩ := e
  obtain h | h := charged_cases he
  · obtain ⟨h1, h2, h3, _⟩ := h
    have h1' : v = a := h1.symm
    subst h1'
    have hlat : b ∈ laterFinset L v := mem_laterFinset_iff.2 h2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨rfl, hlat, h3⟩⟩
  · obtain ⟨h1, h2, h3, h4⟩ := h
    have h1' : v = b := h1.symm
    subst h1'
    exact absurd htype h4

/-- Under type I, charged arcs are in-arcs of `v` from later vertices. -/
lemma charged_typeI_subset {G : Digraph (Fin n)} {c : ℕ} {L : List (Fin n)}
    {v : Fin n} (htype : ¬ typeOOf G c L v) :
    charged G c L v ⊆ (univ.filter fun e : Fin n × Fin n =>
      e.2 = v ∧ e.1 ∈ laterFinset L v ∧ G.Adj e.1 e.2) := by
  intro e he
  obtain ⟨a, b⟩ := e
  obtain h | h := charged_cases he
  · obtain ⟨h1, h2, h3, h4⟩ := h
    have h1' : v = a := h1.symm
    subst h1'
    exact absurd h4 htype
  · obtain ⟨h1, h2, h3, _⟩ := h
    have h1' : v = b := h1.symm
    subst h1'
    have hlat : a ∈ laterFinset L v := mem_laterFinset_iff.2 h2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨rfl, hlat, h3⟩⟩


/-- Type-O charges map injectively into out-neighbours in the prefix. -/
lemma charged_typeO_card_le_out {G : Digraph (Fin n)} {c : ℕ} {L : List (Fin n)}
    {v : Fin n} (htype : typeOOf G c L v) (hcomplete : L.toFinset = univ) :
    (charged G c L v).card ≤ outDegOn G (peelPrefix L (L.idxOf v)) v := by
  have hsub := charged_typeO_subset (htype := htype)
  refine le_trans (card_le_card hsub) ?_
  have hinj : Set.InjOn (fun e : Fin n × Fin n => e.2)
      ((univ.filter fun e : Fin n × Fin n =>
        e.1 = v ∧ e.2 ∈ laterFinset L v ∧ G.Adj e.1 e.2) : Set _) := by
    rintro ⟨a₁, b₁⟩ he₁ ⟨a₂, b₂⟩ he₂ hEq
    have he₁' : a₁ = v ∧ b₁ ∈ laterFinset L v ∧ G.Adj a₁ b₁ := by
      simpa [mem_filter, mem_univ, true_and] using he₁
    have he₂' : a₂ = v ∧ b₂ ∈ laterFinset L v ∧ G.Adj a₂ b₂ := by
      simpa [mem_filter, mem_univ, true_and] using he₂
    obtain ⟨h1, _, _⟩ := he₁'
    obtain ⟨h1', _, _⟩ := he₂'
    rw [h1, h1', Prod.mk.injEq]
    exact ⟨rfl, hEq⟩
  have himg : ((univ.filter fun e : Fin n × Fin n =>
      e.1 = v ∧ e.2 ∈ laterFinset L v ∧ G.Adj e.1 e.2)).image
        (fun e : Fin n × Fin n => e.2)
      ⊆ (peelPrefix L (L.idxOf v)).filter (G.Adj v) := by
    intro u hu
    obtain ⟨e, he, hu'⟩ := Finset.mem_image.1 hu
    have he' : e.1 = v ∧ e.2 ∈ laterFinset L v ∧ G.Adj e.1 e.2 := by
      simpa [mem_filter, mem_univ, true_and] using he
    obtain ⟨h1, h2, h3⟩ := he'
    refine Finset.mem_filter.2 ⟨?_, by rw [← hu']; rw [← h1]; exact h3⟩
    rw [← hu']
    exact later_subset_peelPrefix hcomplete v h2
  have hcard : ((univ.filter fun e : Fin n × Fin n =>
      e.1 = v ∧ e.2 ∈ laterFinset L v ∧ G.Adj e.1 e.2)).card
      = (((univ.filter fun e : Fin n × Fin n =>
        e.1 = v ∧ e.2 ∈ laterFinset L v ∧ G.Adj e.1 e.2)).image
          (fun e : Fin n × Fin n => e.2)).card :=
    (Finset.card_image_of_injOn hinj).symm
  rw [hcard]
  refine le_trans (card_le_card himg) ?_
  unfold outDegOn
  exact le_rfl


/-- Type-I charges map injectively into in-neighbours in the prefix. -/
lemma charged_typeI_card_le_in {G : Digraph (Fin n)} {c : ℕ} {L : List (Fin n)}
    {v : Fin n} (htype : ¬ typeOOf G c L v) (hcomplete : L.toFinset = univ) :
    (charged G c L v).card ≤ inDegOn G (peelPrefix L (L.idxOf v)) v := by
  have hsub := charged_typeI_subset (htype := htype)
  refine le_trans (card_le_card hsub) ?_
  have hinj : Set.InjOn (fun e : Fin n × Fin n => e.1)
      ((univ.filter fun e : Fin n × Fin n =>
        e.2 = v ∧ e.1 ∈ laterFinset L v ∧ G.Adj e.1 e.2) : Set _) := by
    rintro ⟨a₁, b₁⟩ he₁ ⟨a₂, b₂⟩ he₂ hEq
    have he₁' : b₁ = v ∧ a₁ ∈ laterFinset L v ∧ G.Adj a₁ b₁ := by
      simpa [mem_filter, mem_univ, true_and] using he₁
    have he₂' : b₂ = v ∧ a₂ ∈ laterFinset L v ∧ G.Adj a₂ b₂ := by
      simpa [mem_filter, mem_univ, true_and] using he₂
    obtain ⟨h1, _, _⟩ := he₁'
    obtain ⟨h1', _, _⟩ := he₂'
    rw [h1, h1', Prod.mk.injEq]
    exact ⟨hEq, rfl⟩
  have himg : ((univ.filter fun e : Fin n × Fin n =>
      e.2 = v ∧ e.1 ∈ laterFinset L v ∧ G.Adj e.1 e.2)).image
        (fun e : Fin n × Fin n => e.1)
      ⊆ (peelPrefix L (L.idxOf v)).filter (fun u => G.Adj u v) := by
    intro u hu
    obtain ⟨e, he, hu'⟩ := Finset.mem_image.1 hu
    have he' : e.2 = v ∧ e.1 ∈ laterFinset L v ∧ G.Adj e.1 e.2 := by
      simpa [mem_filter, mem_univ, true_and] using he
    obtain ⟨h1, h2, h3⟩ := he'
    refine Finset.mem_filter.2 ⟨?_, by rw [← hu']; rw [← h1]; exact h3⟩
    rw [← hu']
    exact later_subset_peelPrefix hcomplete v h2
  have hcard : ((univ.filter fun e : Fin n × Fin n =>
      e.2 = v ∧ e.1 ∈ laterFinset L v ∧ G.Adj e.1 e.2)).card
      = (((univ.filter fun e : Fin n × Fin n =>
        e.2 = v ∧ e.1 ∈ laterFinset L v ∧ G.Adj e.1 e.2)).image
          (fun e : Fin n × Fin n => e.1)).card :=
    (Finset.card_image_of_injOn hinj).symm
  rw [hcard]
  refine le_trans (card_le_card himg) ?_
  unfold inDegOn
  exact le_rfl

/-- `laterFinset` has cardinality `laterCount` for a complete nodup list. -/
lemma laterFinset_card {L : List (Fin n)} (hcomplete : L.toFinset = univ)
    (hnd : L.Nodup) (v : Fin n) :
    (laterFinset L v).card = laterCount L v := by
  unfold laterFinset laterCount
  classical
  have hmem (u : Fin n) : u ∈ L := by
    apply List.mem_toFinset.mp
    rw [hcomplete]
    exact mem_univ _
  have hcard : (univ.filter fun u : Fin n => L.idxOf v < L.idxOf u).card =
      (Ioo (L.idxOf v) L.length).card := by
    apply card_bij (fun u _ => L.idxOf u)
    · intro u hu
      exact mem_Ioo.mpr ⟨(mem_filter.mp hu).2,
        List.idxOf_lt_length_of_mem (hmem u)⟩
    · intro u _ w _ heq
      exact (List.idxOf_inj (hmem u) (hmem w)).mp heq
    · intro i hi
      have hib := (mem_Ioo.mp hi).2
      refine ⟨L[i], ?_, ?_⟩
      · apply mem_filter.mpr
        refine ⟨mem_univ _, ?_⟩
        rw [List.idxOf_getElem hnd i hib]
        exact (mem_Ioo.mp hi).1
      · exact List.idxOf_getElem hnd i hib
  rw [hcard, Nat.card_Ioo]
  omega

/-- Pointwise charge bound `charged(v) ≤ min c (laterCount L v)`. -/
lemma charge_to_vertex_le_min (G : Digraph (Fin n)) (c : ℕ) (hc : q G ≤ c)
    (v : Fin n) (hv : v ∈ peelOrder G c hc univ) :
    (charged G c (peelOrder G c hc univ) v).card
      ≤ min c (laterCount (peelOrder G c hc univ) v) := by
  set L := peelOrder G c hc univ
  have hcomplete : L.toFinset = univ := peelOrder_complete G c hc
  have hnd : L.Nodup := peelOrder_nodup G c hc
  have hctrl : semiDegOn G (peelPrefix L (L.idxOf v)) v ≤ c :=
    peelOrder_control G c hc v hv
  have hlc := laterFinset_card hcomplete hnd v
  by_cases htype : typeOOf G c L v
  · have h1 : (charged G c L v).card ≤ c :=
      le_trans (charged_typeO_card_le_out htype hcomplete) htype
    -- also ≤ laterCount via image ⊆ laterFinset
    have h2 : (charged G c L v).card ≤ laterCount L v := by
      refine le_trans (card_le_card (charged_typeO_subset (htype := htype))) ?_
      have hinj : Set.InjOn (fun e : Fin n × Fin n => e.2)
          ((univ.filter fun e : Fin n × Fin n =>
            e.1 = v ∧ e.2 ∈ laterFinset L v ∧ G.Adj e.1 e.2) : Set _) := by
        rintro ⟨a₁, b₁⟩ he₁ ⟨a₂, b₂⟩ he₂ hEq
        have he₁' : a₁ = v ∧ b₁ ∈ laterFinset L v ∧ G.Adj a₁ b₁ := by
          simpa [mem_filter, mem_univ, true_and] using he₁
        have he₂' : a₂ = v ∧ b₂ ∈ laterFinset L v ∧ G.Adj a₂ b₂ := by
          simpa [mem_filter, mem_univ, true_and] using he₂
        obtain ⟨h1, _, _⟩ := he₁'
        obtain ⟨h1', _, _⟩ := he₂'
        rw [h1, h1', Prod.mk.injEq]
        exact ⟨rfl, hEq⟩
      have hsub : ((univ.filter fun e : Fin n × Fin n =>
          e.1 = v ∧ e.2 ∈ laterFinset L v ∧ G.Adj e.1 e.2)).image
            (fun e : Fin n × Fin n => e.2) ⊆ laterFinset L v := by
        intro u hu
        obtain ⟨e, he, hu'⟩ := Finset.mem_image.1 hu
        have he' : e.1 = v ∧ e.2 ∈ laterFinset L v ∧ G.Adj e.1 e.2 := by
          simpa [mem_filter, mem_univ, true_and] using he
        rw [← hu']
        exact he'.2.1
      refine le_trans (le_of_eq (Finset.card_image_of_injOn hinj).symm) ?_
      refine le_trans (card_le_card hsub) ?_
      rw [hlc]
    exact le_min h1 h2
  · have hin : inDegOn G (peelPrefix L (L.idxOf v)) v ≤ c := by
      unfold semiDegOn at hctrl
      have hnot : ¬ outDegOn G (peelPrefix L (L.idxOf v)) v ≤ c := htype
      omega
    have h1 : (charged G c L v).card ≤ c :=
      le_trans (charged_typeI_card_le_in htype hcomplete) hin
    have h2 : (charged G c L v).card ≤ laterCount L v := by
      refine le_trans (card_le_card (charged_typeI_subset (htype := htype))) ?_
      have hinj : Set.InjOn (fun e : Fin n × Fin n => e.1)
          ((univ.filter fun e : Fin n × Fin n =>
            e.2 = v ∧ e.1 ∈ laterFinset L v ∧ G.Adj e.1 e.2) : Set _) := by
        rintro ⟨a₁, b₁⟩ he₁ ⟨a₂, b₂⟩ he₂ hEq
        have he₁' : b₁ = v ∧ a₁ ∈ laterFinset L v ∧ G.Adj a₁ b₁ := by
          simpa [mem_filter, mem_univ, true_and] using he₁
        have he₂' : b₂ = v ∧ a₂ ∈ laterFinset L v ∧ G.Adj a₂ b₂ := by
          simpa [mem_filter, mem_univ, true_and] using he₂
        obtain ⟨h1, _, _⟩ := he₁'
        obtain ⟨h1', _, _⟩ := he₂'
        rw [h1, h1', Prod.mk.injEq]
        exact ⟨hEq, rfl⟩
      have hsub : ((univ.filter fun e : Fin n × Fin n =>
          e.2 = v ∧ e.1 ∈ laterFinset L v ∧ G.Adj e.1 e.2)).image
            (fun e : Fin n × Fin n => e.1) ⊆ laterFinset L v := by
        intro u hu
        obtain ⟨e, he, hu'⟩ := Finset.mem_image.1 hu
        have he' : e.2 = v ∧ e.1 ∈ laterFinset L v ∧ G.Adj e.1 e.2 := by
          simpa [mem_filter, mem_univ, true_and] using he
        rw [← hu']
        exact he'.2.1
      refine le_trans (le_of_eq (Finset.card_image_of_injOn hinj).symm) ?_
      refine le_trans (card_le_card hsub) ?_
      rw [hlc]
    exact le_min h1 h2


/-- Reindexing: for a complete nodup `L` of length `n`, summing `f (L.idxOf v)`
over `v : Fin n` equals summing `f i` over `i < n`. -/
lemma sum_idxOf_eq_sum_range {L : List (Fin n)} (hcomplete : L.toFinset = univ)
    (hnd : L.Nodup) (hlen : L.length = n) (f : ℕ → ℕ) :
    (∑ v : Fin n, f (L.idxOf v)) = ∑ i ∈ range n, f i := by
  classical
  have hmem (v : Fin n) : v ∈ L := by
    have : v ∈ L.toFinset := by
      rw [hcomplete]
      exact mem_univ v
    exact List.mem_toFinset.1 this
  have hlt (v : Fin n) : L.idxOf v < L.length :=
    List.idxOf_lt_length_of_mem (hmem v)
  have hinj : ∀ v₁ v₂ : Fin n, L.idxOf v₁ = L.idxOf v₂ → v₁ = v₂ := by
    intro v₁ v₂ h
    exact (List.idxOf_inj (hmem v₁) (hmem v₂)).mp h
  have hsurj : ∀ i ∈ range n, ∃ v : Fin n, L.idxOf v = i := by
    intro i hi
    have hib : i < L.length := by simp [mem_range] at hi; omega
    refine ⟨L[i], List.idxOf_getElem hnd i hib⟩
  refine Finset.sum_bij (fun v _ => L.idxOf v) ?_ ?_ ?_ ?_
  · intro v _
    simp only [mem_range]
    have := hlt v
    omega
  · intro v₁ _ v₂ _ h
    exact hinj v₁ v₂ h
  · intro i hi
    obtain ⟨v, hv⟩ := hsurj i hi
    exact ⟨v, mem_univ v, hv⟩
  · intro v _
    rfl

/-- Sum of pointwise charges closes `marked_charge_le`. -/
lemma marked_charge_le' (G : Digraph (Fin n)) (c : ℕ) (hc : q G ≤ c) :
    (markedOfList G c (peelOrder G c hc univ)).card ≤ ∑ i ∈ range n, min c i := by
  classical
  set L := peelOrder G c hc univ
  have hcomplete : L.toFinset = univ := peelOrder_complete G c hc
  have hnd : L.Nodup := peelOrder_nodup G c hc
  have hlen : L.length = n := by
    have h1 : L.toFinset.card = n := by
      rw [hcomplete]
      exact Fintype.card_fin n
    have h2 : L.toFinset.card = L.length := by
      show L.dedup.length = L.length
      rw [List.dedup_eq_self.2 hnd]
    omega
  have hfib : (markedOfList G c L).card
      = ∑ v : Fin n, (charged G c L v).card := by
    have H : Set.MapsTo (chargeTo L) (markedOfList G c L : Set _) (univ : Finset (Fin n)) :=
      fun e _ => mem_univ _
    have h := Finset.card_eq_sum_card_fiberwise (f := chargeTo L)
      (s := markedOfList G c L) (t := univ) H
    -- #s = ∑ b ∈ univ, #{a ∈ s | chargeTo L a = b}
    rw [h]
    show (∑ b ∈ univ, _) = _
    simp only [charged]
  rw [hfib]
  have hpt : ∀ v : Fin n, (charged G c L v).card ≤ min c (laterCount L v) := by
    intro v
    by_cases hv : v ∈ L
    · exact charge_to_vertex_le_min G c hc v hv
    · have : charged G c L v = ∅ := by
        ext e
        simp only [charged, mem_filter, not_mem_empty, iff_false]
        intro hef
        obtain ⟨a, b⟩ := e
        have he : (a, b) ∈ charged G c L v := by
          simpa [charged] using hef
        obtain h | h := charged_cases he
        · obtain ⟨h1, _, _, _⟩ := h
          have ha : a ∈ L := by
            have : a ∈ L.toFinset := by
              rw [hcomplete]
              exact mem_univ a
            exact List.mem_toFinset.1 this
          rw [h1] at ha
          exact hv ha
        · obtain ⟨h1, _, _, _⟩ := h
          have hb : b ∈ L := by
            have : b ∈ L.toFinset := by
              rw [hcomplete]
              exact mem_univ b
            exact List.mem_toFinset.1 this
          rw [h1] at hb
          exact hv hb
      rw [this]
      exact Nat.zero_le _
  have hswap : (∑ v : Fin n, min c (laterCount L v)) = ∑ i ∈ range n, min c i := by
    have hlc : ∀ v : Fin n, laterCount L v = n - 1 - L.idxOf v := by
      intro v
      unfold laterCount
      omega
    simp only [hlc]
    have hsum := sum_idxOf_eq_sum_range hcomplete hnd hlen
      (fun i => min c (n - 1 - i))
    -- ∑ i ∈ range n, min c (n-1-i) = ∑ i ∈ range n, min c i
    have hflip : (∑ i ∈ range n, min c (n - 1 - i)) = ∑ i ∈ range n, min c i := by
      refine Finset.sum_bij (fun i _ => n - 1 - i) ?_ ?_ ?_ ?_
      · intro i hi
        simp only [mem_range] at hi ⊢
        omega
      · intro i₁ hi₁ i₂ hi₂ h
        simp only [mem_range] at hi₁ hi₂
        have h1 : i₁ ≤ n - 1 := by omega
        have h2 : i₂ ≤ n - 1 := by omega
        have h' : n - 1 - i₁ = n - 1 - i₂ := h
        omega
      · intro i hi
        simp only [mem_range] at hi
        refine ⟨n - 1 - i, ?_, ?_⟩
        · simp only [mem_range]
          omega
        · have h1 : i ≤ n - 1 := by omega
          have : n - 1 - (n - 1 - i) = i := by omega
          exact this
      · intro i _
        rfl
    rw [hsum, hflip]
  calc
    (∑ v : Fin n, (charged G c L v).card) ≤ (∑ v : Fin n, min c (laterCount L v)) :=
      Finset.sum_le_sum fun v _ => hpt v
    _ = ∑ i ∈ range n, min c i := hswap


end SemidegreeExt
