import Paper13.GraphH
import Mathlib.Combinatorics.SimpleGraph.Coloring

/-! # The port assembly and its graph properties (paper Lemma 4). -/
namespace Paper13
open SimpleGraph
open scoped BigOperators
abbrev GkVert (k : ℕ) := Fin k × Fin 7

def Gk (k : ℕ) : SimpleGraph (GkVert k) where
  Adj a b := (a.1 = b.1 ∧ H.Adj a.2 b.2) ∨
    (a.2 = Hport ∧ b.2 = Hport ∧ (T k).Adj a.1 b.1)
  symm := by
    rintro a b (h | h)
    · exact Or.inl ⟨h.1.symm, H.symm h.2⟩
    · exact Or.inr ⟨h.2.1, h.1, (T k).symm h.2.2⟩
  loopless := by
    rintro a (h | h)
    · exact H.loopless _ h.2
    · exact (T k).loopless _ h.2.2

instance (k : ℕ) : DecidableRel (Gk k).Adj := fun a b =>
  inferInstanceAs (Decidable ((a.1 = b.1 ∧ H.Adj a.2 b.2) ∨
    (a.2 = Hport ∧ b.2 = Hport ∧ (T k).Adj a.1 b.1)))

def GkPort (k : ℕ) (v : Fin k) : GkVert k := (v, Hport)

def GkCopyHom {k : ℕ} (v : Fin k) : H →g Gk k where
  toFun u := (v, u)
  map_rel' h := Or.inl ⟨rfl, h⟩

def GkPortHom (k : ℕ) : T k →g Gk k where
  toFun v := (v, Hport)
  map_rel' h := Or.inr ⟨rfl, rfl, h⟩

lemma Gk_num_verts (k : ℕ) : Fintype.card (GkVert k) = 7 * k := by
  simp [GkVert, mul_comm]

lemma Gk_neighborFinset {k : ℕ} (v : Fin k) (u : Fin 7) :
    (Gk k).neighborFinset (v,u) =
      (H.neighborFinset u).image (fun w => (v,w)) ∪
      (if u = Hport then ((T k).neighborFinset v).image (fun w => (w,Hport)) else ∅) := by
  ext ⟨w,t⟩
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, Finset.mem_image,
    Prod.mk.injEq, Gk]
  by_cases hu : u = Hport
  · simp only [hu, ↓reduceIte, Finset.mem_image, SimpleGraph.mem_neighborFinset, Prod.mk.injEq]
    aesop
  · simp only [hu, ↓reduceIte, Finset.not_mem_empty, or_false]
    aesop

lemma Gk_degree {k : ℕ} (v : Fin k) (u : Fin 7) :
    (Gk k).degree (v,u) = H.degree u + if u = Hport then (T k).degree v else 0 := by
  change ((Gk k).neighborFinset (v,u)).card = _
  rw [Gk_neighborFinset]
  have hinj1 : Function.Injective (fun w : Fin 7 => (v,w)) := fun a b h => (Prod.mk.inj h).2
  have hinj2 : Function.Injective (fun w : Fin k => (w,Hport)) := fun a b h => (Prod.mk.inj h).1
  by_cases hu : u = Hport
  · rw [if_pos hu, if_pos hu, Finset.card_union_of_disjoint]
    · rw [Finset.card_image_of_injective _ hinj1, Finset.card_image_of_injective _ hinj2]
      rfl
    · apply Finset.disjoint_left.mpr
      rintro x hx hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hy
      have hb' : (T k).Adj v b := by simpa using hb
      have he' : b = v := congrArg Prod.fst he
      subst b
      exact (T k).loopless _ hb'
  · rw [if_neg hu, if_neg hu, Finset.union_empty, Finset.card_image_of_injective _ hinj1]
    rfl

lemma Gk_num_edges (k : ℕ) (hk : 7 ≤ k) : (Gk k).edgeFinset.card = 9*k - 1 := by
  letI := neZero_of_seven_le hk
  have hs : ∑ x : GkVert k, (Gk k).degree x = 16 * k + 2 * (k-1) := by
    rw [Fintype.sum_prod_type]
    simp only [Gk_degree, Finset.sum_add_distrib]
    simp only [H_sum_degrees, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [T_sum_degrees hk]
    simp
    omega
  have h := SimpleGraph.sum_degrees_eq_twice_card_edges (G := Gk k)
  rw [hs] at h
  omega

lemma Gk_connected (k : ℕ) (hk : 7 ≤ k) : (Gk k).Connected := by
  letI := neZero_of_seven_le hk
  letI : Nonempty (GkVert k) := ⟨(0,0)⟩
  constructor
  rintro ⟨v,u⟩ ⟨w,t⟩
  exact ((H_connected u Hport).map (GkCopyHom v)).trans
    (((T_connected hk v w).map (GkPortHom k)).trans
      ((H_connected Hport t).map (GkCopyHom w)))

lemma Gk_maxDegree (k : ℕ) (hk : 7 ≤ k) : (Gk k).maxDegree = 5 := by
  letI := neZero_of_seven_le hk
  apply Nat.le_antisymm
  · apply SimpleGraph.maxDegree_le_of_forall_degree_le
    rintro ⟨v,u⟩
    rw [Gk_degree]
    by_cases hu : u = Hport
    · rw [if_pos hu, hu, H_port_degree]
      have := T_degree_le hk v
      omega
    · rw [if_neg hu]
      have := H_degree_le_four u
      omega
  · have h := (Gk k).degree_le_maxDegree (0,Hport)
    rw [Gk_degree, if_pos rfl, H_port_degree, T_center_degree hk] at h
    exact h

lemma Gk_non_bipartite (k : ℕ) (hk : 7 ≤ k) : ¬ Nonempty ((Gk k).Coloring (Fin 2)) := by
  let v : Fin k := ⟨0, by omega⟩
  rintro ⟨c⟩
  have h12 := c.valid (show (Gk k).Adj (v,1) (v,2) from Or.inl ⟨rfl,H_edge_12⟩)
  have h25 := c.valid (show (Gk k).Adj (v,2) (v,5) from Or.inl ⟨rfl,H_edge_25⟩)
  have h15 := c.valid (show (Gk k).Adj (v,1) (v,5) from Or.inl ⟨rfl,H_edge_15⟩)
  have ha := (c (v,1)).isLt
  have hb := (c (v,2)).isLt
  have hc := (c (v,5)).isLt
  have h12' : (c (v,1)).val ≠ (c (v,2)).val := fun h => h12 (Fin.ext h)
  have h25' : (c (v,2)).val ≠ (c (v,5)).val := fun h => h25 (Fin.ext h)
  have h15' : (c (v,1)).val ≠ (c (v,5)).val := fun h => h15 (Fin.ext h)
  omega

/-- Every cycle graph is 2-regular; the degree-five port excludes that possibility. -/
lemma Gk_not_cycle (k : ℕ) (hk : 7 ≤ k) : ¬ (Gk k).IsRegularOfDegree 2 := by
  intro h
  letI nz := neZero_of_seven_le hk
  have he := h.degree_eq ((0 : Fin k),Hport)
  rw [Gk_degree, if_pos rfl, H_port_degree, T_degree_zero hk] at he
  omega

lemma Gk_degree_one_iff {k : ℕ} (hk : 7 ≤ k) (x : GkVert k) :
    (Gk k).degree x = 1 ↔ x.2 = 0 ∨ x.2 = 6 := by
  letI := neZero_of_seven_le hk
  rcases x with ⟨v,u⟩
  have ht : 1 ≤ (T k).degree v := by rw [T_degree hk]; split_ifs <;> omega
  fin_cases u <;> simp [Gk_degree, Hport, H_degree, ht] <;> omega

lemma Gk_degree_two_iff {k : ℕ} (hk : 7 ≤ k) (x : GkVert k) :
    (Gk k).degree x = 2 ↔ x.2 = 3 := by
  letI := neZero_of_seven_le hk
  rcases x with ⟨v,u⟩
  have ht : 1 ≤ (T k).degree v := by rw [T_degree hk]; split_ifs <;> omega
  fin_cases u <;> simp [Gk_degree, Hport, H_degree, ht] <;> omega

/-- Intrinsic recognition of the two vertices supporting a leaf in each gadget. -/
lemma Gk_has_leaf_iff {k : ℕ} (hk : 7 ≤ k) (x : GkVert k) :
    (∃ y, (Gk k).Adj x y ∧ (Gk k).degree y = 1) ↔ x.2 = 1 ∨ x.2 = 5 := by
  constructor
  · rintro ⟨⟨v,u⟩, hxy, hy⟩
    have hu := (Gk_degree_one_iff hk (v,u)).mp hy
    change u = 0 ∨ u = 6 at hu
    rcases hu with hu | hu <;> subst u
    · rcases hxy with ⟨he,h⟩ | ⟨_,h,_⟩
      · left
        have : ∀ t : Fin 7, H.Adj t 0 → t = 1 := by decide
        exact this x.2 h
      · norm_num [Hport, Fin.ext_iff] at h
    · rcases hxy with ⟨he,h⟩ | ⟨_,h,_⟩
      · right
        have : ∀ t : Fin 7, H.Adj t 6 → t = 5 := by decide
        exact this x.2 h
      · norm_num [Hport, Fin.ext_iff] at h
  · intro hx
    rcases x with ⟨v,u⟩
    change u = 1 ∨ u = 5 at hx
    rcases hx with hx | hx
    · refine ⟨(v,0), Or.inl ⟨rfl, ?_⟩, (Gk_degree_one_iff hk _).mpr (Or.inl rfl)⟩
      simpa only [hx] using H.symm H_edge_01
    · refine ⟨(v,6), Or.inl ⟨rfl, ?_⟩, (Gk_degree_one_iff hk _).mpr (Or.inr rfl)⟩
      simpa only [hx] using H_edge_56

lemma Gk_iso_has_leaf {k : ℕ} (φ : (Gk k ≃g Gk k)) (x : GkVert k) :
    (∃ y, (Gk k).Adj (φ x) y ∧ (Gk k).degree y = 1) ↔
    (∃ y, (Gk k).Adj x y ∧ (Gk k).degree y = 1) := by
  constructor
  · rintro ⟨y,hy,hd⟩
    refine ⟨φ.symm y, ?_, ?_⟩
    · simpa using φ.symm.map_adj_iff.mpr hy
    · rw [← Paper13.SimpleGraph.Iso.degree_eq φ.symm y, hd]
  · rintro ⟨y,hy,hd⟩
    refine ⟨φ y, φ.map_adj_iff.mpr hy, ?_⟩
    rw [← Paper13.SimpleGraph.Iso.degree_eq φ y, hd]

lemma Gk_iso_snd15 {k : ℕ} (hk : 7 ≤ k) (φ : (Gk k ≃g Gk k)) (x : GkVert k) :
    ((φ x).2 = 1 ↔ x.2 = 1) ∧ ((φ x).2 = 5 ↔ x.2 = 5) := by
  have hleaf := Gk_iso_has_leaf φ x
  rw [Gk_has_leaf_iff hk, Gk_has_leaf_iff hk] at hleaf
  have hd := Paper13.SimpleGraph.Iso.degree_eq φ x
  have hd1 : ∀ y : GkVert k, y.2 = 1 → (Gk k).degree y = 3 := by
    rintro ⟨v,u⟩ hu; change u = 1 at hu; subst u; simp [Gk_degree, Hport, H_degree_1]
  have hd5 : ∀ y : GkVert k, y.2 = 5 → (Gk k).degree y = 4 := by
    rintro ⟨v,u⟩ hu; change u = 5 at hu; subst u; simp [Gk_degree, Hport, H_degree_5]
  constructor
  · constructor
    · intro h
      rcases hleaf.mp (Or.inl h) with h' | h'
      · exact h'
      · have := hd1 _ h; have := hd5 _ h'; omega
    · intro h
      rcases hleaf.mpr (Or.inl h) with h' | h'
      · exact h'
      · have := hd1 _ h; have := hd5 _ h'; omega
  · constructor
    · intro h
      rcases hleaf.mp (Or.inr h) with h' | h'
      · have := hd5 _ h; have := hd1 _ h'; omega
      · exact h'
    · intro h
      rcases hleaf.mpr (Or.inr h) with h' | h'
      · have := hd5 _ h; have := hd1 _ h'; omega
      · exact h'

/-- Coordinate 2 is the unique non-leaf, non-leaf-support vertex adjacent to coordinate 1. -/
lemma Gk_snd_two_iff {k : ℕ} (hk : 7 ≤ k) (x : GkVert k) :
    x.2 = 2 ↔ ((Gk k).degree x ≠ 1 ∧
      ¬ (∃ y, (Gk k).Adj x y ∧ (Gk k).degree y = 1) ∧
      ∃ y, (Gk k).Adj x y ∧ y.2 = 1) := by
  rw [Gk_has_leaf_iff hk]
  simp only [ne_eq, Gk_degree_one_iff hk]
  constructor
  · intro hx
    refine ⟨by simp [hx], by simp [hx], (x.1,1), ?_, rfl⟩
    left
    refine ⟨rfl, ?_⟩
    simpa [hx] using H.symm H_edge_12
  · rintro ⟨hn,hl,⟨⟨v,u⟩,ha,hu⟩⟩
    change u = 1 at hu
    rcases ha with ⟨_,ha⟩ | ⟨_,ha,_⟩
    · rw [hu] at ha
      have hclass : ∀ t : Fin 7, H.Adj t 1 → t = 0 ∨ t = 2 ∨ t = 5 := by decide
      rcases hclass x.2 ha with h | h | h
      · exact False.elim (hn (Or.inl h))
      · exact h
      · exact False.elim (hl (Or.inr h))
    · simp [hu, Hport, Fin.ext_iff] at ha

lemma Gk_iso_snd_two {k : ℕ} (hk : 7 ≤ k) (φ : (Gk k ≃g Gk k)) (x : GkVert k) :
    (φ x).2 = 2 ↔ x.2 = 2 := by
  rw [Gk_snd_two_iff hk, Gk_snd_two_iff hk]
  rw [← Paper13.SimpleGraph.Iso.degree_eq φ x, Gk_iso_has_leaf]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · rintro ⟨y,hy,hs⟩
    refine ⟨φ.symm y, ?_, ?_⟩
    · simpa using φ.symm.map_adj_iff.mpr hy
    · exact (Gk_iso_snd15 hk φ (φ.symm y)).1.mp (by simpa using hs)
  · rintro ⟨y,hy,hs⟩
    exact ⟨φ y, φ.map_adj_iff.mpr hy, (Gk_iso_snd15 hk φ y).1.mpr hs⟩

lemma Gk_snd_zero_iff {k : ℕ} (hk : 7 ≤ k) (x : GkVert k) :
    x.2 = 0 ↔ (Gk k).degree x = 1 ∧ ∃ y, (Gk k).Adj x y ∧ y.2 = 1 := by
  rw [Gk_degree_one_iff hk]
  constructor
  · intro hx
    refine ⟨Or.inl hx, (x.1,1), Or.inl ⟨rfl, ?_⟩, rfl⟩
    simpa [hx] using H_edge_01
  · rintro ⟨hx, ⟨⟨v,u⟩,ha,hu⟩⟩
    rcases hx with hx | hx
    · exact hx
    · change u = 1 at hu
      rcases ha with ⟨_,ha⟩ | ⟨_,ha,_⟩
      · rw [hx, hu] at ha
        exact False.elim ((by decide : ¬ H.Adj 6 1) ha)
      · simp [hu, Hport, Fin.ext_iff] at ha

lemma Gk_iso_snd_zero {k : ℕ} (hk : 7 ≤ k) (φ : Gk k ≃g Gk k) (x : GkVert k) :
    (φ x).2 = 0 ↔ x.2 = 0 := by
  rw [Gk_snd_zero_iff hk, Gk_snd_zero_iff hk, ← Paper13.SimpleGraph.Iso.degree_eq φ x]
  refine and_congr Iff.rfl ?_
  constructor
  · rintro ⟨y,hy,hs⟩
    refine ⟨φ.symm y, ?_, ?_⟩
    · simpa using φ.symm.map_adj_iff.mpr hy
    · exact (Gk_iso_snd15 hk φ (φ.symm y)).1.mp (by simpa using hs)
  · rintro ⟨y,hy,hs⟩
    exact ⟨φ y, φ.map_adj_iff.mpr hy, (Gk_iso_snd15 hk φ y).1.mpr hs⟩

/-- All seven local positions are intrinsically recognizable after attachment. -/
lemma Gk_iso_snd {k : ℕ} (hk : 7 ≤ k) (φ : Gk k ≃g Gk k) (x : GkVert k) :
    (φ x).2 = x.2 := by
  have h0 := Gk_iso_snd_zero hk φ x
  obtain ⟨h1,h5⟩ := Gk_iso_snd15 hk φ x
  have h2 := Gk_iso_snd_two hk φ x
  have hd := Paper13.SimpleGraph.Iso.degree_eq φ x
  have hleaf : ((φ x).2 = 0 ∨ (φ x).2 = 6) ↔ (x.2 = 0 ∨ x.2 = 6) := by
    rw [← Gk_degree_one_iff hk, ← Gk_degree_one_iff hk, ← hd]
  have h3 : (φ x).2 = 3 ↔ x.2 = 3 := by
    rw [← Gk_degree_two_iff hk, ← Gk_degree_two_iff hk, ← hd]
  generalize hx : x.2 = u at *
  generalize hp : (φ x).2 = t at *
  fin_cases u <;> fin_cases t <;> simp_all

lemma Gk_iso_fst_same_copy {k : ℕ} (hk : 7 ≤ k) (φ : Gk k ≃g Gk k)
    (v : Fin k) (u : Fin 7) : (φ (v,u)).1 = (φ (v,Hport)).1 := by
  have hedge (a b : Fin 7) (hab : H.Adj a b) (ha : a ≠ Hport) :
      (φ (v,a)).1 = (φ (v,b)).1 := by
    have h := φ.map_adj_iff.mpr (show (Gk k).Adj (v,a) (v,b) from Or.inl ⟨rfl,hab⟩)
    rcases h with h | h
    · exact h.1
    · have h' := Gk_iso_snd hk φ (v,a)
      exact False.elim (ha (h'.symm.trans h.1))
  have h01 := hedge 0 1 H_edge_01 (by decide)
  have h12 := hedge 1 2 H_edge_12 (by decide)
  have h23 := hedge 2 3 H_edge_23 (by decide)
  have h34 := hedge 3 4 H_edge_34 (by decide)
  have h54 := hedge 5 4 (H.symm H_edge_45) (by decide)
  have h65 := hedge 6 5 (H.symm H_edge_56) (by decide)
  change (φ (v,u)).1 = (φ (v,4)).1
  fin_cases u <;> first | rfl | exact h34 | exact h54 | exact h65.trans h54 |
    exact h23.trans h34 | exact h12.trans (h23.trans h34) |
    exact h01.trans (h12.trans (h23.trans h34))

/-- The automorphism induced on gadget indices. -/
def GkIndexIso {k : ℕ} (hk : 7 ≤ k) (φ : Gk k ≃g Gk k) : T k ≃g T k where
  toFun v := (φ (v,Hport)).1
  invFun v := (φ.symm (v,Hport)).1
  left_inv v := by
    have hp : φ (v,Hport) = ((φ (v,Hport)).1,Hport) := by
      apply Prod.ext
      · rfl
      · exact Gk_iso_snd hk φ (v,Hport)
    have h := congrArg (fun x => (φ.symm x).1) hp
    simpa using h.symm
  right_inv v := by
    have hp : φ.symm (v,Hport) = ((φ.symm (v,Hport)).1,Hport) := by
      apply Prod.ext
      · rfl
      · exact Gk_iso_snd hk φ.symm (v,Hport)
    have h := congrArg (fun x => (φ x).1) hp
    simpa using h.symm
  map_rel_iff' := by
    intro v w
    have hp : ∀ v, φ (v,Hport) = ((φ (v,Hport)).1,Hport) := by
      intro v
      apply Prod.ext
      · rfl
      · exact Gk_iso_snd hk φ (v,Hport)
    have h := φ.map_adj_iff (v := (v,Hport)) (w := (w,Hport))
    simp only [Gk, Gk_iso_snd hk φ (v,Hport), Gk_iso_snd hk φ (w,Hport),
      and_false, false_or, true_and] at h
    have hno : ¬ H.Adj Hport Hport := H.loopless _
    simpa only [hno, and_false, false_or] using h

lemma Gk_aut_trivial (k : ℕ) (hk : 7 ≤ k) : ∀ φ : Gk k ≃g Gk k, φ = 1 := by
  intro φ
  have hi := T_aut_trivial k hk (GkIndexIso hk φ)
  have hfix (v : Fin k) : (φ (v,Hport)).1 = v := by
    exact congrArg (fun ψ : T k ≃g T k => ψ v) hi
  apply RelIso.ext
  rintro ⟨v,u⟩
  apply Prod.ext
  · exact (Gk_iso_fst_same_copy hk φ v u).trans (hfix v)
  · exact Gk_iso_snd hk φ (v,u)

/-- Complete graph statement of Lemma 4, with exact maximum degree. -/
theorem lemma4 (k : ℕ) (hk : 7 ≤ k) : (Gk k).Connected ∧
    Fintype.card (GkVert k) = 7*k ∧ (Gk k).edgeFinset.card = 9*k-1 ∧
    (Gk k).maxDegree = 5 ∧ (∀ φ : Gk k ≃g Gk k, φ = 1) ∧
    ¬ Nonempty ((Gk k).Coloring (Fin 2)) ∧ ¬ (Gk k).IsRegularOfDegree 2 :=
  ⟨Gk_connected k hk, Gk_num_verts k, Gk_num_edges k hk, Gk_maxDegree k hk,
   Gk_aut_trivial k hk, Gk_non_bipartite k hk, Gk_not_cycle k hk⟩
end Paper13


