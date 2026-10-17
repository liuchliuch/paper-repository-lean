import Paper14.PrimitiveVoidProof
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set Function Filter
open scoped ENNReal
namespace Paper14
noncomputable section

def verticalStrip (L U : ℝ) (f g : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Ioc L U ∧ f x.1 < x.2 ∧ x.2 ≤ g x.1}

lemma measurableSet_verticalStrip (L U : ℝ) {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet (verticalStrip L U f g) :=
  (measurable_fst measurableSet_Ioc).inter
    ((measurableSet_lt (hf.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hg.comp measurable_fst)))

/-- Exact area of a measurable strip between arbitrary vertical graphs. -/
lemma volume_verticalStrip (L U : ℝ) {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) :
    volume (verticalStrip L U f g) = ∫⁻ s in Ioc L U, ENNReal.ofReal (g s-f s) := by
  change (volume.prod volume) (verticalStrip L U f g) = _
  rw [Measure.prod_apply (measurableSet_verticalStrip L U hf hg)]
  have heq : (fun s : ℝ => volume (Prod.mk s ⁻¹' verticalStrip L U f g)) =
      (Ioc L U).indicator (fun s => ENNReal.ofReal (g s-f s)) := by
    funext s
    by_cases hs : s ∈ Ioc L U
    · have hset : Prod.mk s ⁻¹' verticalStrip L U f g = Ioc (f s) (g s) := by
        ext t
        simp only [verticalStrip,mem_preimage,mem_setOf_eq,mem_Ioc]
        exact and_iff_right hs
      rw [hset,Real.volume_Ioc,indicator_of_mem hs]
    · have hset : Prod.mk s ⁻¹' verticalStrip L U f g = ∅ := by
        ext t
        simp only [verticalStrip,mem_preimage,mem_setOf_eq,hs,false_and,not_false_eq_true,mem_empty_iff_false]
      rw [hset,measure_empty,indicator_of_notMem hs]
  rw [heq,lintegral_indicator measurableSet_Ioc]

def appendixLowerStrip (r : ℝ) (p q : ℕ) : Set (ℝ × ℝ) :=
  verticalStrip (6/7) r (fun s => ((p : ℝ)*s+r)/(q : ℝ)) (fun s => ((p : ℝ)*s+1)/(q : ℝ))

lemma measurableSet_appendixLowerStrip (r : ℝ) (p q : ℕ) : MeasurableSet (appendixLowerStrip r p q) :=
  measurableSet_verticalStrip _ _ (by fun_prop) (by fun_prop)

/-- Exact unnormalized area of the actual lower-moment strip (51). -/
lemma volume_appendixLowerStrip {r : ℝ} (hr : r ≤ 1) (p q : ℕ) :
    volume (appendixLowerStrip r p q) = ENNReal.ofReal ((r-6/7)*((1-r)/(q : ℝ))) := by
  rw [appendixLowerStrip,volume_verticalStrip _ _ (by fun_prop) (by fun_prop)]
  have heq (s : ℝ) : ((p : ℝ)*s+1)/(q : ℝ)-((p : ℝ)*s+r)/(q : ℝ) = (1-r)/(q : ℝ) := by ring
  simp_rw [heq]
  rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioc,
    ← ENNReal.ofReal_mul (div_nonneg (sub_nonneg.mpr hr) (Nat.cast_nonneg _))]
  congr 1
  ring

end
end Paper14
