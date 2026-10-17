import Paper14.InvariantComponents

open MeasureTheory Set Function Filter
namespace Paper14
noncomputable section

lemma measurePreserving_of_ae_factor {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {μ : Measure E} {ν : Measure F} {T : E → E} {S : F → F} {g : E → F}
    (hT : MeasurePreserving T μ μ) (hg : MeasurePreserving g μ ν) (hS : Measurable S)
    (hsemi : ∀ᵐ x ∂μ, g (T x) = S (g x)) : MeasurePreserving S ν ν := by
  refine ⟨hS,?_⟩
  rw [← hg.map_eq,Measure.map_map hS hg.measurable]
  have hh : Measure.map (g ∘ T) μ = Measure.map (S ∘ g) μ := Measure.map_congr hsemi
  rw [← hh]
  rw [← Measure.map_map hg.measurable hT.measurable,hT.map_eq]

lemma ergodic_of_ae_factor {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {μ : Measure E} {ν : Measure F} {T : E → E} {S : F → F} {g : E → F}
    (hT : Ergodic T μ) (hg : MeasurePreserving g μ ν) (hS : Measurable S)
    (hsemi : ∀ᵐ x ∂μ, g (T x) = S (g x)) : Ergodic S ν := by
  refine ⟨measurePreserving_of_ae_factor hT.toMeasurePreserving hg hS hsemi,?_⟩
  constructor
  intro A hA hAS
  have hpre : T ⁻¹' (g ⁻¹' A) =ᵐ[μ] g ⁻¹' A := by
    filter_upwards [hsemi] with x hx
    apply propext
    change (g (T x) ∈ A) ↔ (g x ∈ A)
    rw [hx]
    exact Set.ext_iff.mp hAS (g x)
  have hz : μ (g ⁻¹' A) = 0 ∨ μ (g ⁻¹' A)ᶜ = 0 := by
    simpa only [ae_eq_empty,ae_eq_univ] using
      hT.quasiErgodic.ae_empty_or_univ₀ (hg.measurable hA).nullMeasurableSet hpre
  rw [hg.measure_preimage hA.nullMeasurableSet,← Set.preimage_compl,
    hg.measure_preimage hA.compl.nullMeasurableSet] at hz
  apply eventuallyConst_set'.mpr
  rcases hz with hz | hz
  · exact Or.inl (ae_eq_empty.mpr hz)
  · exact Or.inr (ae_eq_univ.mpr hz)

end
end Paper14
