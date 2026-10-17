import GeometricMedianCoresets.IndexedSample
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Tactic

/-! Every unordered `m`-subset has exactly `m!` ordered injective enumerations. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace GeometricMedianCoresets.SampleFibers

/-- The subset underlying an injective ordered sample. -/
def image {n m : ℕ} (e : Fin m ↪ Fin n) : Finset (Fin n) := Finset.univ.image e

lemma image_card {n m : ℕ} (e : Fin m ↪ Fin n) : (image e).card = m := by
  simp [image, Finset.card_image_of_injective _ e.injective]

/-- Enumerate a fixed subset using any permutation of its canonical enumeration. -/
def enumerate {n m : ℕ} (I : Finset (Fin n)) (hI : I.card = m) (p : Equiv.Perm (Fin m)) :
    Fin m ↪ Fin n where
  toFun j := ((Finset.equivFinOfCardEq hI).symm (p j)).val
  inj' := Subtype.val_injective.comp ((Finset.equivFinOfCardEq hI).symm.injective.comp p.injective)

lemma image_enumerate {n m : ℕ} (I : Finset (Fin n)) (hI : I.card = m) (p : Equiv.Perm (Fin m)) :
    image (enumerate I hI p) = I := by
  ext k
  simp only [image, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact ((Finset.equivFinOfCardEq hI).symm (p j)).property
  · intro hk
    refine ⟨p.symm ((Finset.equivFinOfCardEq hI) ⟨k,hk⟩), ?_⟩
    simp [enumerate]

/-- The full fiber is a copy of the permutation group on `Fin m`. -/
def fiberEquiv {n m : ℕ} (I : Finset (Fin n)) (hI : I.card = m) :
    Equiv.Perm (Fin m) ≃ {e : Fin m ↪ Fin n // image e = I} :=
  Equiv.ofBijective (fun p => ⟨enumerate I hI p, image_enumerate I hI p⟩) (by
    constructor
    · intro p q hpq
      apply Equiv.ext
      intro j
      have hj := congrArg (fun e : {e : Fin m ↪ Fin n // image e = I} => e.val j) hpq
      exact (Finset.equivFinOfCardEq hI).symm.injective (Subtype.ext hj)
    · intro e
      have hmem : ∀ j, e.val j ∈ I := by
        intro j
        have hi : e.val j ∈ image e.val := Finset.mem_image.2 ⟨j, Finset.mem_univ j, rfl⟩
        exact Eq.mp (congrArg (fun J : Finset (Fin n) => e.val j ∈ J) e.property) hi
      let f : Fin m → Fin m := fun j => (Finset.equivFinOfCardEq hI) ⟨e.val j, hmem j⟩
      have hf : Function.Injective f := by
        intro j k hjk
        apply e.val.injective
        exact congrArg Subtype.val ((Finset.equivFinOfCardEq hI).injective hjk)
      let p : Equiv.Perm (Fin m) := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
      refine ⟨p, ?_⟩
      apply Subtype.ext
      apply Function.Embedding.ext
      intro j
      change ((Finset.equivFinOfCardEq hI).symm ((Finset.equivFinOfCardEq hI)
        ⟨e.val j, hmem j⟩)).val = e.val j
      simp)

lemma card_fiber {n m : ℕ} (I : Finset (Fin n)) (hI : I.card = m) :
    ((Finset.univ : Finset (Fin m ↪ Fin n)).filter (fun e => image e = I)).card = m.factorial := by
  have h := Fintype.card_congr (fiberEquiv I hI)
  rw [Fintype.card_subtype, Fintype.card_perm, Fintype.card_fin] at h
  exact h.symm

/-- Counting an arbitrary event can be done on subsets or on ordered injective tuples. -/
theorem card_event {n m : ℕ} (E : Finset (Fin n) → Prop) :
    ((Finset.univ : Finset (Fin m ↪ Fin n)).filter (fun e => E (image e))).card =
      m.factorial * (((Finset.univ : Finset (Fin n)).powersetCard m).filter E).card := by
  let s := (Finset.univ : Finset (Fin m ↪ Fin n)).filter (fun e => E (image e))
  let t := ((Finset.univ : Finset (Fin n)).powersetCard m).filter E
  have hmap : Set.MapsTo image (s : Set (Fin m ↪ Fin n)) (t : Set (Finset (Fin n))) := by
    intro e he
    obtain ⟨_, he⟩ := Finset.mem_filter.1 he
    exact Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, image_card e⟩, he⟩
  have hc := Finset.card_eq_sum_card_fiberwise hmap
  have hfiber : ∀ I ∈ t, (s.filter (fun e => image e = I)).card = m.factorial := by
    intro I hi
    obtain ⟨hI, hE⟩ := Finset.mem_filter.1 hi
    have hfilter : s.filter (fun e => image e = I) =
        (Finset.univ : Finset (Fin m ↪ Fin n)).filter (fun e => image e = I) := by
      ext e
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨h ▸ hE, h⟩
    rw [hfilter, card_fiber I (Finset.mem_powersetCard.1 hI).2]
  change s.card = _
  rw [hc]
  calc _ = ∑ I ∈ t, m.factorial := Finset.sum_congr rfl hfiber
    _ = _ := by simp [t, mul_comm]

/-- The total number of ordered injective tuples is `m! * choose(n,m)`. -/
theorem card_embeddings (n m : ℕ) : Fintype.card (Fin m ↪ Fin n) = m.factorial * n.choose m := by
  have hc := card_event (n := n) (m := m) (fun _ => True)
  simpa using hc

end GeometricMedianCoresets.SampleFibers
