import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.Restrict

/-! A measurable map assembled from countably many measure-preserving branches. -/
open MeasureTheory Set Function
namespace Paper14

/-- A bijection between measurable sets preserves their restricted measures
if each member of a countable measurable partition is a branch of a
measure-preserving measurable equivalence. -/
theorem measurePreserving_countable_branches
    {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [Countable ι]
    {μ : Measure α} {ν : Measure β} {s : Set α} {t : Set β}
    {f : α → β} (hf : Measurable f) (hs : MeasurableSet s)
    (p : α → ι) (hp : ∀ i, MeasurableSet {x | p x = i})
    (e : ι → α ≃ᵐ β) (he : ∀ i, MeasurePreserving (e i) μ ν)
    (hb : ∀ x ∈ s, e (p x) x = f x) (hbij : BijOn f s t) :
    MeasurePreserving f (μ.restrict s) (ν.restrict t) := by
  classical
  let d : ι → Set α := fun i => s ∩ {x | p x = i}
  have hd : ∀ i, MeasurableSet (d i) := fun i => hs.inter (hp i)
  have hdis : Pairwise (Disjoint on d) := by
    intro i j hij
    change Disjoint (d i) (d j)
    rw [disjoint_left]
    intro x hxi hxj
    exact hij (hxi.2.symm.trans hxj.2)
  have hcover : (⋃ i, d i) = s := by
    ext x
    simp only [mem_iUnion, d, mem_inter_iff, mem_setOf_eq]
    exact ⟨fun ⟨_, hx, _⟩ => hx, fun hx => ⟨p x, hx, rfl⟩⟩
  have hbranch (i : ι) : EqOn f (e i) (d i) := by
    intro x hx
    rcases hx with ⟨hxs, hxi⟩
    change p x = i at hxi
    simpa only [hxi] using (hb x hxs).symm
  have himage (i : ι) : e i '' d i = f '' d i :=
    (hbranch i).image_eq.symm
  have himdis : Pairwise (Disjoint on (fun i => e i '' d i)) := by
    intro i j hij
    change Disjoint (e i '' d i) (e j '' d j)
    rw [himage i, himage j, disjoint_left]
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, heq⟩
    have hxz := hbij.injOn hx.1 hz.1 heq.symm
    subst z
    exact (Set.disjoint_left.mp (hdis hij)) hx hz
  have himcover : (⋃ i, e i '' d i) = t := by
    simp_rw [himage]
    rw [← image_iUnion, hcover, hbij.image_eq]
  refine ⟨hf, ?_⟩
  calc
    Measure.map f (μ.restrict s)
        = Measure.map f (Measure.sum (fun i => μ.restrict (d i))) := by
            rw [← Measure.restrict_iUnion hdis hd, hcover]
    _ = Measure.sum (fun i => Measure.map f (μ.restrict (d i))) :=
      Measure.map_sum hf.aemeasurable
    _ = Measure.sum (fun i => ν.restrict (e i '' d i)) := by
      congr 1
      funext i
      rw [Measure.map_congr ((ae_restrict_mem (hd i)).mono (hbranch i))]
      exact ((he i).restrict_image_emb (e i).measurableEmbedding (d i)).map_eq
    _ = ν.restrict t := by
      rw [← Measure.restrict_iUnion himdis (fun i => (e i).measurableEmbedding.measurableSet_image.mpr (hd i)), himcover]

end Paper14
