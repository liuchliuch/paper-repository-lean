import Paper38.ModelBridges
import Paper38.Transport

/-!
# Explicit ordinary empirical-transport inputs for Corollary 2.7

These are propositions passed as arguments, with no axiom declarations. They
contain arbitrary i.i.d. observations, their raw empirical law/mean/covariance,
and the genuine quadratic transport infimum. They contain no whitening,
Gaussian coefficient, particle flow, limiting cloud, spectral comparison or
non-Gaussian consistency conclusion.

Raw empirical transport: Varadarajan, "On the convergence of sample probability
distributions", Sankhya 19 (1958), pp.23--26 (a.s. weak convergence), together
with the ordinary scalar strong law for the finite second moment and Villani,
Optimal Transport: Old and New, Springer Grundlehren 338 (2009), Theorem 6.9
(Wasserstein convergence iff weak convergence plus p-th moment convergence),
DOI 10.1007/978-3-540-71050-9. The mean and covariance limits are the ordinary
coordinate/product strong laws; no fourth moment is assumed.

Separation: the zero-cost equality criterion for the quadratic Kantorovich
problem on Euclidean probability measures. It follows from existence of an
optimal plan for the nonnegative continuous cost (Villani, Theorem 4.1): a
zero-cost optimal plan is concentrated on the diagonal, hence has equal
marginals. No finite second moment is needed for this zero-cost implication.
The reverse implication is the diagonal coupling, already proved locally.
-/

noncomputable section
namespace Paper38.ExternalEmpiricalTransport

open Paper38.Model MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- Population moments in the actual Euclidean model. -/
def populationMean {d : ℕ} (ν : Measure (E d)) : E d := ∫ x, x ∂ν

def populationCovariance {d : ℕ} (ν : Measure (E d)) : Mat d :=
  fun i j => ∫ x, (x - populationMean ν) i * (x - populationMean ν) j ∂ν

/-- The ordinary empirical W₂ and raw moment strong laws, on any one specified
probability space. Positive counts n+1 avoid a spurious zero-particle law. -/
def RawEmpiricalStrongLaws (Ω : Type*) [MeasurableSpace Ω] (d : ℕ) : Prop :=
  ∀ (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure (E d)) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → E d),
    (∀ n, Measurable (X n)) → iIndepFun X P →
    (∀ n, Measure.map (X n) P = ν) → Integrable (fun x : E d => ‖x‖ ^ 2) ν →
    ∀ᵐ ω ∂P,
      Tendsto (fun n => Transport.w2sq
        (empiricalLaw (fun i : Fin (n + 1) => X i ω)) ν) atTop (𝓝 0) ∧
      Tendsto (fun n => empiricalMean (fun i : Fin (n + 1) => X i ω))
        atTop (𝓝 (populationMean ν)) ∧
      Tendsto (fun n => empiricalCovariance (fun i : Fin (n + 1) => X i ω))
        atTop (𝓝 (populationCovariance ν))

/-- The standard zero-cost separation implication, for the actual transport
infimum over measures with the two prescribed marginals. -/
def QuadraticTransportSeparation (d : ℕ) : Prop :=
  ∀ (μ ν : Measure (E d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
    Transport.w2sq μ ν = 0 → μ = ν

end Paper38.ExternalEmpiricalTransport
