import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Data.PNat.Defs

/-! Missing measurable-Sigma API for this project's pinned Mathlib version.
Every result is derived from the actual infimum-of-maps Sigma structure. -/
namespace MEJF.MeasurableSigma

/-- Positive sizes carry the discrete measurable structure. -/
instance pnatMeasurableSpace : MeasurableSpace ℕ+ := ⊤

instance pnatDiscreteMeasurableSpace : DiscreteMeasurableSpace ℕ+ :=
  ⟨fun _ => trivial⟩

instance pnatMeasurableSingletonClass : MeasurableSingletonClass ℕ+ :=
  ⟨fun _ => trivial⟩

@[simp] theorem measurableSet_pnat (s : Set ℕ+) : MeasurableSet s := trivial

variable {I : Type*} {β : I → Type*} [mβ : ∀ i, MeasurableSpace (β i)]
    {Y : Type*} [mY : MeasurableSpace Y]

/-- Each fiber inclusion is measurable in the actual disjoint-union structure. -/
theorem measurable_sigma_mk (i : I) : Measurable (Sigma.mk i : β i → Sigma β) := by
  apply Measurable.of_le_map
  change (⨅ j, (mβ j).map (Sigma.mk j)) ≤ (mβ i).map (Sigma.mk i)
  exact iInf_le _ i

/-- A map out of a Sigma type is measurable iff every fiber restriction is. -/
theorem measurable_sigma_iff {f : Sigma β → Y} :
    Measurable f ↔ ∀ i, Measurable (f ∘ Sigma.mk i) := by
  constructor
  · intro hf i
    exact hf.comp (measurable_sigma_mk i)
  · intro hf
    apply Measurable.of_comap_le
    change mY.comap f ≤ ⨅ i, (mβ i).map (Sigma.mk i)
    apply le_iInf
    intro i
    apply MeasurableSpace.comap_le_iff_le_map.mp
    simpa only [MeasurableSpace.comap_comp] using (hf i).comap_le

/-- An implicit-index form convenient in `.comp` expressions. -/
theorem measurable_sigma_mk' {i : I} : Measurable (Sigma.mk i : β i → Sigma β) :=
  measurable_sigma_mk i

/-- The size/index projection is measurable. This actually needs no
countability or discreteness assumption on the target measurable structure. -/
theorem measurable_sigma_fst [MeasurableSpace I] : Measurable (Sigma.fst : Sigma β → I) := by
  apply measurable_sigma_iff.mpr
  intro i
  exact measurable_const

end MEJF.MeasurableSigma
