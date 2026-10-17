import Paper23.CertificateSparse

/-! Soundness interfaces used by the explicit sixfold bounding certificate.
All numerical obligations are finite kernel checks on the original labelled
cubes. The source is never replaced by a presentation matrix assumption. -/
namespace Paper23.Bounding
open Cubical CertificateChecks

/-- A decoded term belongs to the original ordered degree-three cubical basis. -/
def ValidThree (k : ℕ) : Prop := IsCube (decodeCube k) ∧ degree (decodeCube k) = 3

instance (k : ℕ) : Decidable (ValidThree k) := by
  unfold ValidThree IsCube
  infer_instance

/-- Cell permutation preserves pairwise closure disjointness and degree. -/
theorem validThree_of_perm (a b : ℕ)
    (h : (decodeCube a).Perm (decodeCube b)) (hb : ValidThree b) : ValidThree a := by
  refine ⟨⟨h.length_eq.trans hb.1.1, ?_⟩, ?_⟩
  · exact h.symm.pairwise hb.1.2 (fun h => Disjoint.symm h)
  · exact ((h.map GraphCell.dimension).sum_eq).trans hb.2

theorem validThree_of_canonical_list (entries : List (ℕ × ℤ)) (canons : List ℕ)
    (hc : ∀ k ∈ canons, ValidThree k)
    (hp : ∀ p ∈ entries, ∃ k ∈ canons, (decodeCube p.1).Perm (decodeCube k)) :
    ∀ p ∈ entries, ValidThree p.1 := by
  intro p hp'
  obtain ⟨k,hk,hperm⟩ := hp p hp'
  exact validThree_of_perm p.1 k hperm (hc k hk)

theorem codeChain_mem_three (entries : List (ℕ × ℤ))
    (h : ∀ p ∈ entries, ValidThree p.1) : codeChain entries ∈ Chains 3 := by
  induction entries with
  | nil => exact (Chains 3).zero_mem
  | cons p xs ih =>
    rw [codeChain_cons]
    apply (Chains 3).add_mem
    · apply (Chains 3).smul_mem
      exact Finsupp.single_mem_supported ℤ 1 (h p (by simp))
    · apply ih
      intro p hp
      exact h p (by simp [hp])

/-- A checked leaf normal form denotes precisely the actual boundary of the
leaf source, with the corresponding sixfold target subtracted. -/
theorem leaf_sound (fuel : ℕ) (entries target normal : List (ℕ × ℤ))
    (valid : ∀ p ∈ entries, ValidThree p.1)
    (checked : collapse fuel (((codeDifferential entries) ++ scaleEntries (-6) target).map
      (fun p => [p])) = [normal]) :
    codeChain normal = boundary (codeChain entries) + (-6 : ℤ) • codeChain target := by
  have h := normalization_sound fuel _ normal checked
  rw [codeChain_append, codeChain_scaleEntries,
    codeChain_codeDifferential _ (fun p hp => (valid p hp).1.2)] at h
  exact h

/-- Checked merges preserve both the boundary and the target summands. -/
theorem node_sound (left right normal : List (ℕ × ℤ))
    (ls rs lt rt : RawChain)
    (hl : codeChain left = boundary ls + (-6 : ℤ) • lt)
    (hr : codeChain right = boundary rs + (-6 : ℤ) • rt)
    (checked : merge left right = normal) :
    codeChain normal = boundary (ls+rs) + (-6 : ℤ) • (lt+rt) := by
  rw [← checked, codeChain_merge, hl, hr, map_add, smul_add]
  abel

/-- A zero root gives six times the actual target as an integral boundary. -/
theorem bounding_of_zero (source target : RawChain)
    (h : (0 : RawChain) = boundary source + (-6 : ℤ) • target) :
    boundary source = (6 : ℕ) • target := by
  have hn : (-6 : ℤ) • target = -((6 : ℕ) • target) := by
    simp only [neg_smul]
    rfl
  rw [hn, ← sub_eq_add_neg] at h
  exact sub_eq_zero.mp h.symm

end Paper23.Bounding
