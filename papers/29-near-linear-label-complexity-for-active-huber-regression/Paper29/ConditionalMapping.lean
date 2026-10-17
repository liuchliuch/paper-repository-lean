import Paper29.GeneralInformation

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Paper29.GeneralInformation

theorem information_map {Ω U S T : Type} [MeasurableSpace Ω] [MeasurableSpace U]
    [MeasurableSpace S] [MeasurableSpace T] (μ : Measure Ω) (F : Ω → U) (X : U → S) (Y : U → T)
    (hF : Measurable F) (hX : Measurable X) (hY : Measurable Y) :
    information (μ.map F) X Y = information μ (fun ω => X (F ω)) (fun ω => Y (F ω)) := by
  unfold information
  rw [Measure.map_map (hX.prodMk hY) hF,Measure.map_map hX hF,Measure.map_map hY hF]
  rfl

/-- Measurable transformations of the source/response preserve the actual
conditional kernel and its disintegration, including arbitrary conditioning alphabets. -/
theorem ConditionalLaw.map {Ω U V H : Type} [MeasurableSpace Ω] [MeasurableSpace U]
    [MeasurableSpace V] [MeasurableSpace H] (μ : Measure Ω) (Urv : Ω → U) (Hrv : Ω → H)
    (K : H → Measure U) (hK : ConditionalLaw μ Urv Hrv K) (F : U → V) (hF : Measurable F) :
    ConditionalLaw μ (fun ω => F (Urv ω)) Hrv (fun h => (K h).map F) := by
  refine ⟨?_,?_,?_⟩
  · intro A hA
    simpa only [Measure.map_apply hF hA] using hK.1 (F ⁻¹' A) (hF hA)
  · intro h
    letI := hK.2.1 h
    exact Measure.isProbabilityMeasure_map hF.aemeasurable
  · intro A D hA hD
    simpa only [Measure.map_apply hF hA,Set.mem_preimage] using hK.2.2 (F ⁻¹' A) D (hF hA) hD

end Paper29.GeneralInformation
