import Paper17.Extension
import Paper17.BarycentricCover
import Mathlib.Data.Fintype.Sort

/-! Chain-valued interpolation using an actual subordinate partition of unity. -/
noncomputable section
open scoped Topology BigOperators
open Set Function
namespace Paper17
variable {ι X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A normalized locally finite partition whose active faces are nested gives
an actual continuous map into the chain-convex target. -/
theorem chain_partition_value_mem {Y : Set E} {r : E → E → Prop}
    (h : ExtensionHypotheses Y r) (β : PartitionOfUnity (Finset ι) X Set.univ)
    (q : Finset ι → E) (hq : ∀ s, q s ∈ Y)
    (hmono : ∀ s t, s.Nonempty → s ⊆ t → r (q s) (q t))
    (x : X) (hne : ∀ s, β s x ≠ 0 → s.Nonempty)
    (hchain : ∀ s t, β s x ≠ 0 → β t x ≠ 0 → s ⊆ t ∨ t ⊆ s) :
    (∑ᶠ s, β s x • q s) ∈ Y := by
  classical
  have hfin := β.locallyFinite.point_finite x
  let S := hfin.toFinset
  have hS : S.Nonempty := by
    by_contra hn
    have hz : ∀ s, β s x = 0 := by
      intro s
      by_contra hs
      exact hn ⟨s, hfin.mem_toFinset.mpr hs⟩
    have hh := β.sum_eq_one (Set.mem_univ x)
    simp [hz] at hh
  have hactive : ∀ s : ↥S, β s.val x ≠ 0 := fun s => hfin.mem_toFinset.mp s.property
  have hcardinj : Function.Injective (fun s : ↥S => s.val.card) := by
    intro s t hcard
    apply Subtype.ext
    rcases hchain s t (hactive s) (hactive t) with hst | hts
    · exact Finset.eq_of_subset_of_card_le hst hcard.ge
    · exact (Finset.eq_of_subset_of_card_le hts hcard.le).symm
  let ord : LinearOrder ↥S := LinearOrder.lift' (fun s : ↥S => s.val.card) hcardinj
  letI : LinearOrder ↥S := ord
  haveI : Nonempty ↥S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  have hcardpos : 0 < Fintype.card ↥S := Fintype.card_pos_iff.mpr inferInstance
  let k := Fintype.card ↥S - 1
  have hk : Fintype.card ↥S = k + 1 := by dsimp [k]; omega
  let eo := @monoEquivOfFin ↥S inferInstance ord (k + 1) hk
  let e : Fin (k + 1) ≃ ↥S := eo.toEquiv
  let ys : Fin (k + 1) → E := fun j => q (e j).val
  have hys : ∀ j, ys j ∈ Y := fun j => hq _
  have hychain : ∀ i j : Fin (k + 1), i.val ≤ j.val → r (ys i) (ys j) := by
    intro i j hij
    have horder := @OrderIso.monotone (Fin (k + 1)) ↥S inferInstance ord.toPartialOrder.toPreorder
      eo i j (show i ≤ j from hij)
    have hcard : (e i).val.card ≤ (e j).val.card := horder
    have hsubset : (e i).val ⊆ (e j).val := by
      rcases hchain (e i) (e j) (hactive (e i)) (hactive (e j)) with hsub | hsub
      · exact hsub
      · exact (Finset.eq_of_subset_of_card_le hsub hcard).symm.le
    exact hmono _ _ (hne _ (hactive (e i))) hsubset
  apply h.chain_convex k ys hys hychain
  apply β.finsum_smul_mem_convex (Set.mem_univ x) _ (convex_convexHull ℝ (Set.range ys))
  intro s hs
  apply subset_convexHull ℝ _
  have hsS : s ∈ S := hfin.mem_toFinset.mpr hs
  refine ⟨e.symm ⟨s, hsS⟩, ?_⟩
  change q ((e (e.symm ⟨s, hsS⟩)).val) = q s
  rw [e.apply_symm_apply]

end Paper17
