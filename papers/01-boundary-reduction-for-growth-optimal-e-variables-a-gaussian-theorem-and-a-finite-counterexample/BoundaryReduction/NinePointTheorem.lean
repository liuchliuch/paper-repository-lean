import BoundaryReduction.NinePointMeanCoordinates

open Real Set BigOperators MeasureTheory
open scoped Classical
namespace BoundaryReduction.NinePoint

/-- Finite priors specified directly by actual mean parameters. -/
structure MeanPrior (C : Set MeanSpace) where
  n : ℕ
  weights : FinProb (Fin n)
  parameter : Fin n → meanImage
  admissible : ∀ i, (parameter i : MeanSpace) ∈ C

noncomputable def MeanPrior.toNatural {C : Set MeanSpace} (F : MeanPrior C) : FinitePrior C :=
  ⟨F.n,F.weights,fun i => naturalParameter (F.parameter i),fun i => by
    rw [mean_naturalParameter]
    exact F.admissible i⟩

noncomputable def MeanPrior.prob {C : Set MeanSpace} (F : MeanPrior C) : FinProb (Fin 9) :=
  F.toNatural.prob

lemma MeanPrior.mass_formula {C : Set MeanSpace} (F : MeanPrior C) (y : Fin 9) :
    F.prob.w y = ∑ i, F.weights.w i*(meanLaw (F.parameter i)).w y := rfl

noncomputable def FinitePrior.toMean {C : Set MeanSpace} (F : FinitePrior C) : MeanPrior C :=
  ⟨F.n,F.weights,fun i => ⟨esMean (pt (F.parameter i)),⟨F.parameter i,rfl⟩⟩,F.admissible⟩

lemma FinitePrior.toMean_prob {C : Set MeanSpace} (F : FinitePrior C) : F.toMean.prob = F.prob := by
  apply prob_ext
  intro y
  simp only [MeanPrior.prob,MeanPrior.toNatural,FinitePrior.prob,FinitePrior.mass,FinitePrior.toMean,naturalParameter_mean]

noncomputable def meanInformation (C : Set MeanSpace) : ℝ :=
  sInf {x : ℝ | ∃ F : MeanPrior C, x = FinProb.klPos F.prob baseProb}

/-- Reparametrization preserves exactly the paper's set of finite mixtures. -/
theorem meanInformation_eq (C : Set MeanSpace) : meanInformation C = information C := by
  unfold meanInformation information
  congr 1
  ext x
  constructor
  · rintro ⟨F,rfl⟩
    exact ⟨F.toNatural,rfl⟩
  · rintro ⟨F,rfl⟩
    exact ⟨F.toMean,by rw [FinitePrior.toMean_prob]⟩

/-- Theorem 3.1 with actual mean-coordinate priors and the original Euclidean ball. -/
theorem theorem_3_1_mean :
    (IsOpen (Metric.ball (0 : MeanSpace) r₀) ∧ (0 : MeanSpace) ∈ Metric.ball 0 r₀ ∧
      IsCompact (closure (Metric.ball (0 : MeanSpace) r₀)) ∧
      closure (Metric.ball (0 : MeanSpace) r₀) ⊆ meanImage ∧
      frontier (Metric.ball (0 : MeanSpace) r₀) = boundary) ∧
    (0 < meanInformation exterior ∧ meanInformation exterior < 2*10^(-15:ℤ) ∧
      (7:ℝ)*10^(-12:ℤ) < meanInformation boundary) ∧
    (∀ W : ProbabilityMeasure boundary,
      ¬ (∀ μ : meanImage, r₀ ≤ ‖(μ : MeanSpace)‖ →
        FinProb.klPos (meanBoundaryMixture W) baseProb ≤
          FinProb.expect (meanLaw μ) (fun y => log ((meanBoundaryMixture W).w y/p0 y)))) := by
  refine ⟨excluded_ball_geometry,?_,no_mean_borel_boundary_global⟩
  simp_rw [meanInformation_eq]
  exact theorem_3_1_information

end BoundaryReduction.NinePoint
