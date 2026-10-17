import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Sigma
import Mathlib.Tactic

/-! Unit-capacity bipartite placement, proved by a Hall gadget. Each allowed
pair has its own gate, so two demand copies cannot select the same pair. -/
open Finset
namespace SemidegreeExt
open Classical

lemma card_pair_fiber {A B : Type*} [Fintype A] [Fintype B]
    (P : A → B → Prop) (b : B) :
    ((univ.filter fun e : A × B => P e.1 e.2).filter fun e => e.2 = b).card =
      (univ.filter fun a => P a b).card := by
  classical
  symm
  apply Finset.card_bij (fun a _ => (a, b))
  · intro a ha
    simpa using ha
  · intro a _ a' _ h
    exact congrArg Prod.fst h
  · rintro ⟨a, b'⟩ he
    simp only [mem_filter, mem_univ, true_and] at he
    obtain rfl := he.2
    exact ⟨a, by simp [he.1], rfl⟩

/-- Integral bipartite placement with capacity one on every pair. -/
theorem exists_unit_placement {A B : Type*} [Fintype A] [Fintype B]
    (r : A → ℕ) (c : ℕ) (R : A → B → Prop)
    (hcut : ∀ S : Finset A, (∑ a ∈ S, r a) ≤
      ∑ b : B, min c ((S.filter fun a => R a b).card)) :
    ∃ F : Finset (A × B),
      (∀ e ∈ F, R e.1 e.2) ∧
      (∀ a, (F.filter fun e => e.1 = a).card = r a) ∧
      (∀ b, (F.filter fun e => e.2 = b).card ≤ c) := by
  classical
  let D := Σ a : A, Fin (r a)
  let E := A × B
  let L := D ⊕ E
  let Q := E ⊕ (B × Fin c)
  let rel : L → Q → Prop
    | .inl x, .inl e => x.1 = e.1 ∧ R e.1 e.2
    | .inl _, .inr _ => False
    | .inr e, .inl e' => e = e'
    | .inr e, .inr z => e.2 = z.1
  let t (x : L) : Finset Q := univ.filter (rel x)
  have hall : ∀ U : Finset L, U.card ≤ (U.biUnion t).card := by
    intro U
    let X := U.toLeft
    let Y := U.toRight
    let S : Finset A := X.image Sigma.fst
    let T : Finset B := Y.image Prod.snd
    let Z : Finset E := univ.filter fun e => e.1 ∈ S ∧ R e.1 e.2 ∧ e.2 ∉ T
    have hX : X.card ≤ ∑ a ∈ S, r a := by
      calc
        X.card ≤ (S.sigma fun a => (univ : Finset (Fin (r a)))).card := by
          apply card_le_card
          intro x hx
          exact mem_sigma.mpr ⟨mem_image.mpr ⟨x, hx, rfl⟩, mem_univ _⟩
        _ = _ := by simp
    have hZ : Z.card = ∑ b : B, if b ∈ T then 0 else (S.filter fun a => R a b).card := by
      rw [card_eq_sum_card_fiberwise (f := Prod.snd) (t := univ) (fun _ _ => mem_univ _)]
      apply sum_congr rfl
      intro b _
      by_cases hb : b ∈ T
      · have hz : Z.filter (fun e => e.2 = b) = ∅ := by
          ext e
          simp only [mem_filter, notMem_empty, iff_false, not_and]
          intro he heb
          exact (mem_filter.mp he).2.2.2 (heb ▸ hb)
        rw [hz, card_empty, if_pos hb]
      · rw [if_neg hb]
        symm
        apply card_bij (fun a _ => (a, b))
        · intro a ha
          exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,
            (mem_filter.mp ha).1, (mem_filter.mp ha).2, hb⟩, rfl⟩
        · intro a _ a' _ he
          exact congrArg Prod.fst he
        · rintro ⟨a, b'⟩ he
          have he' := mem_filter.mp he
          obtain rfl := he'.2
          exact ⟨a, mem_filter.mpr ⟨(mem_filter.mp he'.1).2.1,
            (mem_filter.mp he'.1).2.2.1⟩, rfl⟩
    have hcap : (∑ b : B, min c ((S.filter fun a => R a b).card)) ≤ T.card * c + Z.card := by
      rw [hZ]
      have hT : T.card * c = ∑ b : B, if b ∈ T then c else 0 := by simp [← sum_filter]
      rw [hT, ← sum_add_distrib]
      apply sum_le_sum
      intro b _
      by_cases hb : b ∈ T <;> simp [hb, min_le_left, min_le_right]
    have hd : Disjoint Y Z := by
      apply disjoint_left.mpr
      intro e he hz
      exact (mem_filter.mp hz).2.2.2 (mem_image.mpr ⟨e, he, rfl⟩)
    have hsub : (Y ∪ Z).disjSum (T.product (univ : Finset (Fin c))) ⊆ U.biUnion t := by
      intro q hq
      cases q with
      | inl e =>
        have he : e ∈ Y ∪ Z := by simpa using hq
        rcases mem_union.mp he with hy | hz
        · exact mem_biUnion.mpr ⟨.inr e, by simpa [Y] using hy, by simp [t, rel]⟩
        · have hz' := (mem_filter.mp hz).2
          obtain ⟨x, hx, hxa⟩ := mem_image.mp hz'.1
          exact mem_biUnion.mpr ⟨.inl x, by simpa [X] using hx,
            by simp [t, rel, hxa, hz'.2.1]⟩
      | inr z =>
        have hz : z.1 ∈ T := by simpa using hq
        obtain ⟨e, he, heb⟩ := mem_image.mp hz
        exact mem_biUnion.mpr ⟨.inr e, by simpa [Y] using he, by simp [t, rel, heb]⟩
    have hn := card_le_card hsub
    have hprod : (T.product (univ : Finset (Fin c))).card = T.card * c := by
      change (T ×ˢ (univ : Finset (Fin c))).card = _
      simp
    rw [card_disjSum, card_union_of_disjoint hd, hprod] at hn
    have hu : X.card + Y.card = U.card := card_toLeft_add_card_toRight
    have hc := hcut S
    omega
  obtain ⟨f, hfi, hfr⟩ := (all_card_le_biUnion_card_iff_existsInjective' t).mp hall
  have hf (x : L) : rel x (f x) := (mem_filter.mp (hfr x)).2
  have row_edge (x : D) : ∃ e : E, f (.inl x) = .inl e ∧ x.1 = e.1 ∧ R e.1 e.2 := by
    have h := hf (.inl x)
    cases he : f (.inl x) with
    | inl e => exact ⟨e, rfl, by simpa [he, rel] using h⟩
    | inr z => simp [he, rel] at h
  choose g hg hga hgR using row_edge
  have hgi : Function.Injective g := by
    intro x y hxy
    apply Sum.inl_injective
    apply hfi
    rw [hg, hg, hxy]
  let F := univ.image g
  have hmem (e : E) : e ∈ F ↔ ∃ x : D, g x = e := by simp [F]
  refine ⟨F, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨x, rfl⟩ := (hmem e).mp he
    exact hgR x
  · intro a
    have hrow : (univ : Finset (Fin (r a))).card = (F.filter fun e => e.1 = a).card := by
      apply card_bij (fun k _ => g ⟨a, k⟩)
      · intro k _
        exact mem_filter.mpr ⟨(hmem _).mpr ⟨_, rfl⟩, (hga _).symm⟩
      · intro k _ k' _ he
        exact eq_of_heq (Sigma.mk.inj (hgi he)).2
      · intro e he
        obtain ⟨⟨a', k⟩, rfl⟩ := (hmem e).mp (mem_filter.mp he).1
        have ha : a' = a := (hga _).trans (mem_filter.mp he).2
        subst a'
        exact ⟨k, mem_univ _, rfl⟩
    simpa using hrow.symm
  · intro b
    have hecol (e : E) (he : e ∈ F) : ∃ z : B × Fin c,
        f (.inr e) = .inr z ∧ e.2 = z.1 := by
      have h := hf (.inr e)
      cases heq : f (.inr e) with
      | inl e' =>
        have hee : e = e' := by simpa [heq, rel] using h
        obtain ⟨x, hx⟩ := (hmem e).mp he
        have bad : (Sum.inr e : L) = .inl x := hfi (by rw [heq, hg, hx, hee])
        cases bad
      | inr z => exact ⟨z, rfl, by simpa [heq, rel] using h⟩
    let H := F.filter fun e => e.2 = b
    have hh (e : H) : ∃ k : Fin c, f (.inr e.val) = .inr (b, k) := by
      obtain ⟨⟨b', k⟩, hk, hb'⟩ := hecol e.val (mem_filter.mp e.property).1
      have hbb : b' = b := hb'.symm.trans (mem_filter.mp e.property).2
      subst b'
      exact ⟨k, hk⟩
    choose k hk using hh
    have hki : Function.Injective k := by
      intro e e' he
      apply Subtype.ext
      apply Sum.inr_injective
      apply hfi
      rw [hk, hk, he]
    have := Fintype.card_le_of_injective k hki
    rwa [Fintype.card_coe, Fintype.card_fin] at this
end SemidegreeExt
