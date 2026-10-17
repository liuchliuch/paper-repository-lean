import BoundaryReduction
/-
Copyright (c) 2026. Solution side of the official Lean comparator.
Imports the real proofs from the `BoundaryReduction` library.
-/
import BoundaryReduction.MainStatements
import BoundaryReduction.FirstExit
import BoundaryReduction.GrowBound
import BoundaryReduction.FiniteKL

import BoundaryReduction.BorelCounterexample
import BoundaryReduction.GaussianKL

open Real BigOperators
open scoped MeasureTheory

/-!
# Solution statements

Names must match the challenge statements in type.
-/

namespace Verification

/-- Lemma 4.3, proved in `BoundaryReduction.FirstExit`. -/
theorem lemma_4_3 :
    ∀ {d : ℕ} (B : Set (EuclideanSpace ℝ (Fin d)))
      (g : EuclideanSpace ℝ (Fin d) → ℝ) (c : ℝ),
      IsOpen B → (0 : EuclideanSpace ℝ (Fin d)) ∈ B →
      BoundaryReduction.RaywiseConvex g → g 0 ≤ c →
      (∀ r ∈ frontier B, c ≤ g r) →
      ∀ μ, μ ∉ B → c ≤ g μ := by
  intro d B g c hB_open hB_zero hg hg0 hboundary μ hμ
  exact BoundaryReduction.first_exit_propagation
    hB_open hB_zero hg hg0 hboundary hμ

/-- Lemma 2.1 finite engine, proved in `BoundaryReduction.GrowBound`. -/
theorem lemma_2_1_finite :
    ∀ {α : Type*} [Fintype α]
      (w₀ wr : α → ℝ) (S : α → ℝ),
      (∀ y, 0 < w₀ y) → (∀ y, 0 < wr y) →
      (∀ y, 0 < S y) → (0 < ∑ y, w₀ y * S y) →
      (∑ y, wr y = 1) → (∑ y, w₀ y = 1) →
      (∑ y, wr y * log (S y))
        ≤ (∑ y, wr y * log (wr y / w₀ y)) + log (∑ y, w₀ y * S y) := by
  intro α _ w₀ wr S h0 hr hS hm h1 h2
  -- Package plain weight functions as `FinProb` and apply the library theorem.
  let p₀ : BoundaryReduction.FinProb α :=
    ⟨w₀, fun y => le_of_lt (h0 y), by simpa using h2⟩
  let r : BoundaryReduction.FinProb α :=
    ⟨wr, fun y => le_of_lt (hr y), by simpa using h1⟩
  have hm' : 0 < BoundaryReduction.FinProb.expect p₀ S := by
    simpa [BoundaryReduction.FinProb.expect, p₀] using hm
  have h := BoundaryReduction.FinProb.grow_info_core_of_pos
    (p₀ := p₀) (r := r) (S := S)
    (fun y => h0 y) (fun y => hr y) (fun y => hS y) hm'
  simpa [BoundaryReduction.FinProb.klPos, BoundaryReduction.FinProb.expect,
    p₀, r] using h

end Verification


/-- Appendix A: the actual eight component means and KL sum. -/
theorem Verification.lemma_A_1 :
    (∀ k : Fin 8, BoundaryReduction.NinePoint.r₀ <
      ‖BoundaryReduction.NinePoint.esMean (BoundaryReduction.NinePoint.compPt 200 k)‖) ∧
    (∑ y : Fin 9, BoundaryReduction.NinePoint.Qt 200 y *
      Real.log (BoundaryReduction.NinePoint.Qt 200 y / BoundaryReduction.NinePoint.p0 y)) <
      (1.001:ℝ)*10^(-15:ℤ) := by
  exact BoundaryReduction.NinePoint.lemma_A_1

/-- Theorem 3.1 information values over all finite priors on actual component means. -/
theorem Verification.theorem_3_1_information :
    0 < BoundaryReduction.NinePoint.information BoundaryReduction.NinePoint.exterior ∧
    BoundaryReduction.NinePoint.information BoundaryReduction.NinePoint.exterior < (2:ℝ)*10^(-15:ℤ) ∧
    (7:ℝ)*10^(-12:ℤ) <
      BoundaryReduction.NinePoint.information BoundaryReduction.NinePoint.boundary := by
  exact BoundaryReduction.NinePoint.theorem_3_1_information

/-- Theorem 3.1 Borel obstruction, in the family's natural coordinates. -/
theorem Verification.no_borel_boundary_global :
    ∀ (W : MeasureTheory.Measure (ℝ × ℝ)) [MeasureTheory.IsProbabilityMeasure W],
    (∀ᵐ θ ∂W, ‖BoundaryReduction.NinePoint.esMean (BoundaryReduction.NinePoint.pt θ)‖ =
      BoundaryReduction.NinePoint.r₀) →
    ¬ (∀ θ : ℝ × ℝ,
      BoundaryReduction.NinePoint.r₀ ≤ ‖BoundaryReduction.NinePoint.esMean (BoundaryReduction.NinePoint.pt θ)‖ →
      BoundaryReduction.FinProb.klPos (BoundaryReduction.NinePoint.borelProb W)
        BoundaryReduction.NinePoint.baseProb ≤
      BoundaryReduction.FinProb.expect (BoundaryReduction.NinePoint.tiltProb θ)
        (fun y => Real.log ((BoundaryReduction.NinePoint.borelProb W).w y /
          BoundaryReduction.NinePoint.p0 y))) := by
  intro W hW hsupport
  exact BoundaryReduction.NinePoint.no_borel_boundary_global W hsupport

/-- Natural-log Pinsker on an arbitrary finite positive alphabet. -/
theorem Verification.pinsker :
    ∀ {α : Type*} [Fintype α] (p q : BoundaryReduction.FinProb α),
      (∀ y, 0 < p.w y) → (∀ y, 0 < q.w y) →
      2 * (BoundaryReduction.FinProb.tv p q)^2 ≤ BoundaryReduction.FinProb.klPos p q := by
  intro α _ p q hp hq
  exact BoundaryReduction.FinProb.pinsker p q hp hq


/-- Convexity of actual compact Borel log mixtures in (4.12). -/
theorem Verification.gaussian_log_mixture_convex :
    ∀ {d : ℕ} {Γ : Set (BoundaryReduction.Gaussian.Space d)} [CompactSpace Γ]
      (K : BoundaryReduction.Gaussian.Space d →L[ℝ] BoundaryReduction.Gaussian.Space d)
      (W : MeasureTheory.Measure Γ) [MeasureTheory.IsProbabilityMeasure W],
    ConvexOn ℝ Set.univ (BoundaryReduction.Gaussian.phi K W) := by
  intro d Γ _ K W _
  exact BoundaryReduction.Gaussian.convex_phi K W

/-- The Gaussian translation integral (4.13) is convex, with its integrability proved. -/
theorem Verification.gaussian_expected_log_convex :
    ∀ {d : ℕ} {Γ : Set (BoundaryReduction.Gaussian.Space d)} [CompactSpace Γ]
      (K : BoundaryReduction.Gaussian.Space d →L[ℝ] BoundaryReduction.Gaussian.Space d)
      (W : MeasureTheory.Measure Γ) [MeasureTheory.IsProbabilityMeasure W]
      (Z : MeasureTheory.Measure (BoundaryReduction.Gaussian.Space d)) [ProbabilityTheory.IsGaussian Z]
      (R : NNReal),
      (∀ r : Γ, ‖(r : BoundaryReduction.Gaussian.Space d)‖ ≤ R) →
      ConvexOn ℝ Set.univ (BoundaryReduction.Gaussian.expectedLog K W Z) := by
  intro d Γ _ K W _ Z _ R hR
  exact BoundaryReduction.Gaussian.convex_expectedLog K W Z R hR

/-- The entropy functional is weakly continuous for compact Borel priors. -/
theorem Verification.gaussian_weak_entropy_continuous :
    ∀ {d : ℕ} {Γ : Set (BoundaryReduction.Gaussian.Space d)} [CompactSpace Γ]
      (K : BoundaryReduction.Gaussian.Space d →L[ℝ] BoundaryReduction.Gaussian.Space d)
      (Z : MeasureTheory.Measure (BoundaryReduction.Gaussian.Space d)) [ProbabilityTheory.IsGaussian Z]
      (R : NNReal),
      (∀ r : Γ, ‖(r : BoundaryReduction.Gaussian.Space d)‖ ≤ R) →
      (∀ v : BoundaryReduction.Gaussian.Space d, 0 ≤ inner ℝ v (K v)) →
      Continuous (BoundaryReduction.Gaussian.mixtureEntropy K Z : MeasureTheory.ProbabilityMeasure Γ → ℝ) := by
  intro d Γ _ K Z _ R hR hK
  exact BoundaryReduction.Gaussian.continuous_mixtureEntropy K Z R hR hK

/-- Actual Borel KL minimizer existence on any bounded open neighborhood's boundary. -/
theorem Verification.gaussian_kl_minimizer_exists :
    ∀ {d : ℕ}
      (K : BoundaryReduction.Gaussian.Space d →L[ℝ] BoundaryReduction.Gaussian.Space d)
      (Z : MeasureTheory.Measure (BoundaryReduction.Gaussian.Space d)) [ProbabilityTheory.IsGaussian Z],
      (∫ x, x ∂Z) = 0 →
      (∀ v : BoundaryReduction.Gaussian.Space d,
        ProbabilityTheory.variance (BoundaryReduction.Gaussian.precisionForm K v) Z = inner ℝ v (K v)) →
      ∀ (B : Set (BoundaryReduction.Gaussian.Space d)),
      1 ≤ d → IsOpen B → (0 : BoundaryReduction.Gaussian.Space d) ∈ B → Bornology.IsBounded B →
      ∃ W : MeasureTheory.ProbabilityMeasure (frontier B),
      ∀ V : MeasureTheory.ProbabilityMeasure (frontier B),
        InformationTheory.klDiv (BoundaryReduction.Gaussian.mixtureMeasure K Z W) Z ≤
          InformationTheory.klDiv (BoundaryReduction.Gaussian.mixtureMeasure K Z V) Z := by
  intro d K Z _ hcenter hvariance B hd hB h0 hb
  exact BoundaryReduction.Gaussian.exists_boundary_kl_minimizer K Z hcenter hvariance hd hB h0 hb

open Real Set BigOperators MeasureTheory ProbabilityTheory InformationTheory
open scoped Classical NNReal ENNReal

section
open BoundaryReduction BoundaryReduction.NEF

/-- Full source statement: lemma_2_1. -/
theorem Verification.lemma_2_1_general :
    ∀ {α ι : Type*} [MeasurableSpace α] {d : ℕ}
    (P₀ : Measure α) [IsProbabilityMeasure P₀]
    (Y : α → EuclideanSpace ℝ (Fin d)) (hY : Measurable Y)
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : IsOpen Θ)
    (hexp : ∀ θ ∈ Θ, Integrable (fun x => exp (inner ℝ θ (Y x))) P₀)
    (parameter : ι → EuclideanSpace ℝ (Fin d))
    (hparameter : ∀ i, parameter i ∈ Θ),
    MeasureGrow.growth P₀ (fun i => law P₀ Y (parameter i)) ≤
      (↑(MeasureGrow.information P₀ (fun i => law P₀ Y (parameter i))) : EReal) := by
  exact @BoundaryReduction.NEF.lemma_2_1

end

section
open BoundaryReduction BoundaryReduction.NinePoint

/-- Full source statement: theorem_3_1_mean. -/
theorem Verification.theorem_3_1_mean :
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
  exact @BoundaryReduction.NinePoint.theorem_3_1_mean

end

section
open BoundaryReduction BoundaryReduction.FiniteExponential

/-- Full source statement: proposition_3_2_full. -/
theorem Verification.proposition_3_2_full :
    ∀ {α : Type} [Fintype α] [Nonempty α] {d : ℕ}
    (p : FinProb α) (hp : ∀ y, 0 < p.w y) (Y : α → E d)
    (hd : 1 ≤ d)
    (hminimal : ∀ (a : E d) (b : ℝ), (∀ y, inner ℝ a (Y y) = b) → a = 0)
    (hmean : (∑ y, p.w y • Y y) = 0)
    (B : Set (E d)) (h0 : (0 : E d) ∈ B)
    (hcontained : closure B ⊆ Set.range (mean p hp Y))
    (V : Finset α) (hV : V.Nonempty) (normal : V → E d)
    (hexpose : ∀ v : V, ∀ y, y ≠ (v : α) → inner ℝ (normal v) (Y y) < inner ℝ (normal v) (Y v))
    (g : α → ℝ) {L η : ℝ} (hL : 0 < L) (hη : 0 < η)
    (hg : ∀ y, |g y| ≤ L) (hpg : FinProb.expect p g = 0)
    (hsep : ∀ r : frontier B, η ≤ FinProb.expect
      (meanLaw p hp Y ⟨(r : E d),hcontained (frontier_subset_closure r.2)⟩) g),
    information p hp Y (Set.range (mean p hp Y) \ B) ≤ -log (vertexMass p V) ∧
    η^2/(2*L^2) ≤ information p hp Y (frontier B) ∧
    (-log (vertexMass p V) < η^2/(2*L^2) →
      information p hp Y (Set.range (mean p hp Y) \ B) < information p hp Y (frontier B) ∧
      ∀ W : ProbabilityMeasure (frontier B),
        ¬ (∀ μ : Set.range (mean p hp Y), (μ : E d) ∉ B →
          FinProb.klPos (meanBoundaryMixture p hp Y hminimal B hcontained W) p ≤
            FinProb.expect (meanLaw p hp Y μ)
              (fun y => log ((meanBoundaryMixture p hp Y hminimal B hcontained W).w y/p.w y)))) := by
  exact @BoundaryReduction.FiniteExponential.proposition_3_2_full

end

section
open BoundaryReduction BoundaryReduction.Gaussian

/-- Full source statement: proposition_4_2_iff. -/
theorem Verification.proposition_4_2 :
    ∀ {d : ℕ} {Γ : Set (Space d)} [CompactSpace Γ]
    (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]
    (hcenter : (∫ x, x ∂Z) = 0)
    (hcov : ∀ (L : StrongDual ℝ (Space d)) (v : Space d), covariance L (precisionForm K v) Z = L v)
    (W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)),
    (∀ V : ProbabilityMeasure Γ, mixtureEntropy K Z W ≤ mixtureEntropy K Z V) ↔
    (∀ r : Γ, mixtureEntropy K Z W ≤ expectedLog K (W : Measure Γ) Z (r : Space d)) := by
  exact @BoundaryReduction.Gaussian.proposition_4_2_iff

end

section
open BoundaryReduction BoundaryReduction.Gaussian

/-- Full source statement: proposition_4_2_gap. -/
theorem Verification.proposition_4_2_gap :
    ∀ {d : ℕ} {Γ : Set (Space d)} [CompactSpace Γ]
    (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]
    (hcenter : (∫ x, x ∂Z) = 0)
    (hcov : ∀ (L : StrongDual ℝ (Space d)) (v : Space d), covariance L (precisionForm K v) Z = L v)
    (hΓ : Γ.Nonempty) (V W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v))
    (hmin : ∀ U : ProbabilityMeasure Γ, mixtureEntropy K Z V ≤ mixtureEntropy K Z U),
    0 ≤ mixtureEntropy K Z W-mixtureEntropy K Z V ∧
      mixtureEntropy K Z W-mixtureEntropy K Z V ≤ mixtureEntropy K Z W-boundaryMinimum K Z W := by
  exact @BoundaryReduction.Gaussian.proposition_4_2_gap

end

section
open BoundaryReduction BoundaryReduction.Gaussian

/-- Full source statement: corollary_4_4_map. -/
theorem Verification.corollary_4_4_map :
    ∀ {d : ℕ} {Γ : Set (Space d)} [CompactSpace Γ]
    (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]
    (hcenter : (∫ x, x ∂Z) = 0)
    (hcov : ∀ (L : StrongDual ℝ (Space d)) (v : Space d), covariance L (precisionForm K v) Z = L v)
    (W : ProbabilityMeasure Γ) (T : Γ → Γ) (hT : Measurable T)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v))
    (hsym : ∀ u v : Space d, inner ℝ u (K v) = inner ℝ v (K u))
    (hmin : ∀ V : ProbabilityMeasure Γ, mixtureEntropy K Z W ≤ mixtureEntropy K Z V)
    {δ : ℝ} (hδ : 0 ≤ δ) (happrox : ∀ r : Γ, ‖(T r : Space d)-(r : Space d)‖ ≤ δ),
    0 ≤ mixtureEntropy K Z (CompactPrior.mapPrior W T hT)-mixtureEntropy K Z W ∧
    mixtureEntropy K Z (CompactPrior.mapPrior W T hT)-mixtureEntropy K Z W ≤
      ‖K‖*δ^2/2+(R:ℝ)*‖K‖*δ := by
  exact @BoundaryReduction.Gaussian.corollary_4_4_map

end

section
open BoundaryReduction BoundaryReduction.Gaussian

/-- Full source statement: corollary_4_4_family. -/
theorem Verification.corollary_4_4_family :
    ∀ {d : ℕ} {Γ : Set (Space d)} [CompactSpace Γ]
    (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]
    (hcenter : (∫ x, x ∂Z) = 0)
    (hcov : ∀ (L : StrongDual ℝ (Space d)) (v : Space d), covariance L (precisionForm K v) Z = L v)
    (W : ProbabilityMeasure Γ) (R : ℝ≥0)
    (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v))
    (hsym : ∀ u v : Space d, inner ℝ u (K v) = inner ℝ v (K u))
    (hmin : ∀ V : ProbabilityMeasure Γ, mixtureEntropy K Z W ≤ mixtureEntropy K Z V),
    ∃ V : ℝ → ProbabilityMeasure Γ,
      (∀ δ > 0, (V δ : Measure Γ).support.Finite ∧
        (V δ : Measure Γ).support ⊆ (W : Measure Γ).support ∧
        0 ≤ mixtureEntropy K Z (V δ)-mixtureEntropy K Z W ∧
        mixtureEntropy K Z (V δ)-mixtureEntropy K Z W =
          (klDiv (mixtureMeasure K Z (V δ)) (mixtureMeasure K Z W)).toReal ∧
        (klDiv (mixtureMeasure K Z (V δ)) (mixtureMeasure K Z W)).toReal ≤ ‖K‖*δ^2/2) ∧
      Filter.Tendsto V (nhdsWithin 0 (Ioi 0)) (nhds W) := by
  exact @BoundaryReduction.Gaussian.corollary_4_4_family

end

section
open BoundaryReduction BoundaryReduction.NinePoint

theorem Verification.nine_point_model :
    (∀ y : Fin 9, 0 < p0 y) ∧ (∑ y : Fin 9, p0 y) = 1 ∧ esMean p0 = 0 ∧
    (∀ θ : ℝ × ℝ, 0 < Z θ) ∧
    (∀ (a : MeanSpace) (b : ℝ), (∀ y : Fin 9, inner ℝ a (esTarget y) = b) → a = 0) ∧
    Function.Injective (fun θ : ℝ × ℝ => esMean (pt θ)) := by
  exact ⟨p0_pos,p0_sum,base_esMean,Z_pos,alphabet_minimal,mean_injective⟩

end

section
open BoundaryReduction BoundaryReduction.NinePoint

/-- All exact displays (A.5)–(A.12). -/
theorem Verification.appendix_closed_forms :
    ∀ t : ℝ,
    (∀ i : Fin 4, Z (t • axisNormal i) = Za t ∧ Z (t • diagNormal i) = Zd t) ∧
    Qt t 0 = q0 t ∧
    (∀ i : Fin 4, Qt t (axisTarget i) = qa t ∧ Qt t (diagTarget i) = qd t) ∧
    FinProb.klPos (mixtureProb t) baseProb =
      q0 t*log (q0 t/ε)+4*qa t*log (qa t/w)+4*qd t*log (qd t/w) ∧
    (0 ≤ t → ‖esMean (pt (t • axisNormal 0))‖ = w*(2*sinh t+4*ρ*sinh (ρ*t))/Za t ∧
      ‖esMean (pt (t • diagNormal 0))‖ = sqrt 2*w*(2*sinh t+2*ρ*sinh (2*ρ*t))/Zd t) := by
  intro t
  exact ⟨fun i => ⟨appendix_A5 t i,appendix_A6 t i⟩,appendix_A7 t,
    fun i => ⟨appendix_A8 t i,appendix_A9 t i⟩,appendix_A10 t,
    fun ht => ⟨appendix_A11 t ht,appendix_A12 t ht⟩⟩

end

open BoundaryReduction BoundaryReduction.Gaussian

/-- Full source statement: theorem_4_1_covariance. -/
theorem Verification.theorem_4_1_covariance :
    ∀ {d : ℕ}
    (SigmaOp : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]
    (hcenter : (∫ x, x ∂Z) = 0)
    (hsymSigmaOp : ∀ u v : Space d, inner ℝ u (SigmaOp v) = inner ℝ v (SigmaOp u))
    (hposSigmaOp : ∀ v : Space d, v ≠ 0 → 0 < inner ℝ v (SigmaOp v))
    (hcovSigmaOp : ∀ u v : Space d, covariance (innerSL ℝ u) (innerSL ℝ v) Z = inner ℝ u (SigmaOp v))
    (B : Set (Space d)) (hd : 1 ≤ d) (hB : IsOpen B) (h0 : (0 : Space d) ∈ B)
    (hbounded : Bornology.IsBounded B),
    ∃ K : Space d →L[ℝ] Space d, (∀ v, SigmaOp (K v) = v) ∧ (∀ v, K (SigmaOp v) = v) ∧ BoundaryConclusion K Z B := by
  exact @BoundaryReduction.Gaussian.theorem_4_1_covariance
