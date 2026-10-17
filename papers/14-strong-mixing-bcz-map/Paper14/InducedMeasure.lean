import Paper14.Kac
import Paper14.CountableBranches
open MeasureTheory Measure Filter Set Function
open scoped ENNReal
namespace Paper14
noncomputable section

lemma measurableEmbedding_iterate {α : Type*} [MeasurableSpace α]
    {T : α → α} (hT : MeasurableEmbedding T) (n : ℕ) : MeasurableEmbedding T^[n] := by
  induction n with
  | zero => exact MeasurableEmbedding.id
  | succ n ih => simpa only [iterate_succ'] using hT.comp ih

/-- Distinct positive first-return branches have disjoint images under an
injective map: any collision would exhibit a strictly earlier return. -/
lemma disjoint_firstReturn_images {α : Type*} {T : α → α} {Y : Set α}
    (hT : Injective T) : Pairwise (Disjoint on (fun n : ℕ =>
      T^[n + 1] '' {x ∈ Y | firstReturnTime T Y x = n + 1})) := by
  intro n m hnm
  change Disjoint (T^[n + 1] '' _) (T^[m + 1] '' _)
  rw [disjoint_left]
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  have hlt : ∀ n m : ℕ, n < m → ∀ x y : α,
      x ∈ Y → firstReturnTime T Y x = n + 1 →
      y ∈ Y → firstReturnTime T Y y = m + 1 →
      T^[m + 1] y = T^[n + 1] x → False := by
    intro n m hnm x y hx hxret hy hyret heq
    have hiter : T^[n + 1] (T^[m - n] y) = T^[n + 1] x := by
      rw [← iterate_add_apply]
      convert heq using 1 <;> congr 1 <;> omega
    have hhit : T^[m - n] y = x := hT.iterate (n + 1) hiter
    have hle : firstReturnTime T Y y ≤ m - n :=
      firstReturn_le (by omega) (hhit ▸ hx)
    omega
  rcases lt_or_gt_of_ne hnm with h | h
  · exact hlt n m h x y hx.1 hx.2 hy.1 hy.2 hxy
  · exact hlt m n h y x hy.1 hy.2 hx.1 hx.2 hxy.symm

/-- The induced map preserves the unnormalized restriction. It suffices
that the original map is a measure-preserving measurable embedding; recurrence
supplies the missing zero branch almost everywhere. -/
theorem induced_preserves_restriction {α : Type*} [MeasurableSpace α]
    {T : α → α} {Y : Set α} {μ : Measure α} [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hEmb : MeasurableEmbedding T)
    (hY : MeasurableSet Y) :
    MeasurePreserving (inducedMap T Y) (μ.restrict Y) (μ.restrict Y) := by
  classical
  let A : ℕ → Set α := fun n => {x ∈ Y | firstReturnTime T Y x = n + 1}
  let C : ℕ → Set α := fun n => T^[n + 1] '' A n
  have hA : ∀ n, MeasurableSet (A n) := fun n =>
    hY.inter ((measurableSet_singleton (n + 1)).preimage (measurable_firstReturn hT.measurable hY))
  have hC : ∀ n, MeasurableSet (C n) := fun n =>
    (measurableEmbedding_iterate hEmb (n + 1)).measurableSet_image.mpr (hA n)
  have hdisA : Pairwise (Disjoint on A) := by
    intro n m hnm
    change Disjoint (A n) (A m)
    rw [disjoint_left]
    intro x hx hm
    have h1 := hx.2
    have h2 := hm.2
    change firstReturnTime T Y x = n + 1 at h1
    change firstReturnTime T Y x = m + 1 at h2
    exact hnm (by omega)
  have hdisC : Pairwise (Disjoint on C) := disjoint_firstReturn_images hEmb.injective
  have hcover : (⋃ n : ℕ, A n) =ᵐ[μ] Y := by
    filter_upwards [ae_return_exists hT hY] with x hx
    apply propext
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact hn.1
    · intro hxy
      have hs := (firstReturn_spec (hx hxy)).1
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : firstReturnTime T Y x ≠ 0)
      exact mem_iUnion.mpr ⟨n, hxy, hn⟩
  have hsub : (⋃ n : ℕ, C n) ⊆ Y := by
    intro z hz
    obtain ⟨n, x, hx, rfl⟩ := mem_iUnion.mp hz
    have hex : ∃ k, 0 < k ∧ T^[k] x ∈ Y := by
      by_contra he
      have hz := firstReturnTime_of_not_exists he
      have := hx.2
      omega
    simpa only [hx.2] using (firstReturn_spec hex).2
  have hmeas := measurable_inducedMap hT.measurable hY
  have hmap : Measure.map (inducedMap T Y) (μ.restrict Y) =
      μ.restrict (⋃ n : ℕ, C n) := by
    rw [← Measure.restrict_congr_set hcover, Measure.restrict_iUnion hdisA hA,
      Measure.map_sum hmeas.aemeasurable, Measure.restrict_iUnion hdisC hC]
    congr 1
    funext n
    have heq : inducedMap T Y =ᵐ[μ.restrict (A n)] T^[n + 1] := by
      filter_upwards [ae_restrict_mem (hA n)] with x hx
      simp only [inducedMap, hx.2]
    rw [Measure.map_congr heq]
    exact ((hT.iterate (n + 1)).restrict_image_emb (measurableEmbedding_iterate hEmb (n + 1)) (A n)).map_eq
  refine ⟨hmeas, ?_⟩
  apply Measure.eq_of_le_of_measure_univ_eq
  · rw [hmap]
    exact Measure.restrict_mono_set μ hsub
  · simp only [Measure.map_apply hmeas MeasurableSet.univ, preimage_univ]

end
end Paper14
