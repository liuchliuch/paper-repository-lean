import Paper38.DeterministicMain
import Paper38.SourceExpected
import Paper38.HighProbabilityMain
import Paper38.SourceSharpness
import Paper38.SourceParticleLimit
import Paper38.SourceAffine
import Paper38.SourceSamplingLemmas
import Paper38.CosineSource
import Paper38.SourceGeometry
import Paper38.SourceNonGaussian

/-! Public complete source main-theorem contracts. Known unformalized external
analysis/statistics are explicit ordinary theorem parameters. The original
Gaussian SVGD conclusions are derived in production, never fields of inputs. -/
noncomputable section
universe u
namespace Paper38.Main

abbrev AnalyticBaselines := ∀ d : ℕ, ExternalAnalyticInputs.Baselines d
abbrev StatisticalBaselines := ∀ d : ℕ, 1 ≤ d → ExternalStatisticalInputs.Baselines d

theorem theorem21 (analysis : AnalyticBaselines) : Specification.Theorem21 :=
  DeterministicMain.theorem21 analysis

theorem theorem22 (analysis : AnalyticBaselines) (statistics : StatisticalBaselines) :
    Specification.Theorem22 :=
  SourceExpected.theorem22 (theorem21 analysis) analysis statistics

theorem proposition23 (statistics : StatisticalBaselines) : Specification.Proposition23 :=
  SourceSharpness.proposition23 (fun d hd => (statistics d hd).matching)

theorem theorem24 (analysis : AnalyticBaselines) (statistics : StatisticalBaselines) :
    Specification.Theorem24 :=
  HighProbabilityMain.theorem24_with_baselines (theorem21 analysis) analysis statistics

theorem corollary25 (analysis : AnalyticBaselines) (statistics : StatisticalBaselines) :
    Specification.Corollary25 :=
  SourceExpected.corollary25 (theorem21 analysis) analysis statistics

theorem proposition26 (analysis : AnalyticBaselines) : Production.Specification26 :=
  SourceParticleLimit.proposition26 analysis

theorem corollary27 (analysis : AnalyticBaselines)
    (stronglaws : ∀ (Ω : Type u) [MeasurableSpace Ω] (d : ℕ),
      ExternalEmpiricalTransport.RawEmpiricalStrongLaws Ω d)
    (separation : ∀ d : ℕ, ExternalEmpiricalTransport.QuadraticTransportSeparation d) :
    Production.Specification27.{u} :=
  SourceNonGaussian.corollary27 analysis stronglaws separation

theorem lemma42_minimizer : Specification.Lemma42_minimizer := by
  intro d V α β hV
  obtain ⟨z,_,_,hstar⟩ := GaussianGradientFlow.exists_unique_minimizer hV
  exact ⟨HilbertCoordinates.toModel d z,hstar⟩

theorem lemma51 (analysis : AnalyticBaselines) : Specification.Lemma51 :=
  SourceMomentFlow.lemma51 analysis

theorem lemma41 (analysis : AnalyticBaselines) : GeometrySpecification.Lemma41 :=
  SourceGeometry.lemma41 analysis

theorem lemma42 : GeometrySpecification.Lemma42 := SourceGeometry.lemma42

theorem proposition43 (analysis : AnalyticBaselines) : GeometrySpecification.Proposition43 :=
  SourceGeometry.proposition43 analysis

theorem lemma61 (analysis : AnalyticBaselines) : SourceAffine.Lemma61 :=
  SourceAffine.lemma61 analysis

theorem lemma63 (analysis : AnalyticBaselines) : SourceAffine.Lemma63 :=
  SourceAffine.lemma63 analysis

theorem example91 (analysis : AnalyticBaselines) (statistics : StatisticalBaselines)
    {ε : ℝ} (hε : 0 < ε) (hεupper : ε ≤ 1/10) : CosineSource.ExpectedConvergence ε :=
  CosineSource.theorem22_applies (theorem22 analysis statistics) hε hεupper

end Paper38.Main
