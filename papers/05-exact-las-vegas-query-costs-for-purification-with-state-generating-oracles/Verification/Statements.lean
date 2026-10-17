import ELV
import ELV.Basic
import ELV.CostIdentities
import ELV.Oracle
import ELV.Costs
import ELV.GramRealization
import ELV.LinePurifier
import ELV.BesselLower
import ELV.SignedGram
import ELV.Stabilize
import ELV.ReciprocalRescale

/-! Independently readable full source-result specifications for paper 05.
All operational values use actual fixed circuits and executed query norms. -/
noncomputable section

open ELV

namespace Verification.Specification

/-- Theorem 1.1 numerical form of (1.1)–(1.2). -/
def Theorem11_Numeric (gap : Gap) : Prop :=
  Cost.sgValue gap = 1 / (2 * gap.δ) ∧
  Cost.admValue gap = 1 / (1 - gap.mu) ∧
  Cost.admValue gap = (1 + gap.mu) / (4 * gap.δ ^ 2)

/-- Restricting support increases the actual operational minimax value. -/
def Costs_AccessMonotone (gap : Gap) (n : ℕ) [NeZero n] : Prop :=
  Costs.C_sg gap n ≤ Costs.C_adm gap n

/-- Lemma 2.1, finite-support synthesis isometry (partial: not the stabilized unitary). -/
def Lemma21_Partial : Prop :=
  ∀ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V)
    (ι : Type) (a b : ι → V),
    Gram.EqualGram a b →
      ∀ α : ι →₀ ℂ, ‖Gram.synth a α‖ = ‖Gram.synth b α‖

/-- Lemma 3.1 cost arithmetic of (3.5), (3.9)–(3.10). -/
def Lemma31_Cost : Prop :=
  (∀ p : ℝ, 0 < p → p < 1 / 2 →
      1 + 2 * (p / (1 - p) / (1 - p / (1 - p))) = 1 / (1 - 2 * p)) ∧
  (∀ p : ℝ, 1 / 2 < p → p < 1 →
      1 + 2 * ((p / (1 - p))⁻¹ / (1 - (p / (1 - p))⁻¹)) = 1 / (2 * p - 1)) ∧
  (∀ p : ℝ, |1 - 2 * p| = 2 * |p - 1 / 2|)

/-- Proposition 4.1 algebraic kernel identity + product-space C-S. -/
def Prop41_Algebra : Prop :=
  (∀ a b c d : ℂ, a * (1 - c) + d * (c - 1) = (1 - c) * (a - d)) ∧
  (∀ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (fm gm fp gp : K),
    ‖inner ℂ fm fp - inner ℂ gm gp‖ ^ 2
      ≤ (‖fm‖ ^ 2 + ‖gm‖ ^ 2) * (‖fp‖ ^ 2 + ‖gp‖ ^ 2))

/-- Section 4.2 uniform bound (4.8). -/
def Rescale_Bound : Prop :=
  ∀ μ t : ℝ, μ < 1 → t ≤ μ → 0 ≤ t → 1 / (1 - t) ≤ 1 / (1 - μ)

/-- Proposition 4.2 free-variable obstruction. -/
def Prop42_Unbounded : Prop :=
  ∀ C : ℝ, 0 < C → ∃ N : ℕ, Real.sqrt N / 2 > C

/-- Zero witness is infeasible on opposite labels. -/
def Zero_Infeasible : Prop :=
  ∀ z : ℂ, z ≠ 1 → ¬ ((1 : ℂ) = (1 - z) * 0)

/-- Full Lemma 2.1, including the exact Hilbert-basis cardinal and separability. -/
def Lemma21_Stabilized : Prop :=
  ∀ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (_ : CompleteSpace V)
    (X : Type) (a b : X → V), Gram.EqualGram a b →
    ∃ (I : Set V) (_bV : HilbertBasis I ℂ V)
      (U : Stabilize.HilbertPair V (Gram.StabilizingSpace I) ≃ₗᵢ[ℂ]
        Stabilize.HilbertPair V (Gram.StabilizingSpace I)),
      Cardinal.mk (Gram.StabilizingIndex I) = max Cardinal.aleph0 (Cardinal.mk I) ∧
      (TopologicalSpace.SeparableSpace V → TopologicalSpace.SeparableSpace (Gram.StabilizingSpace I)) ∧
      ∀ x, U (WithLp.toLp 2 (a x, (0 : Gram.StabilizingSpace I))) =
        WithLp.toLp 2 (b x, (0 : Gram.StabilizingSpace I))

/-- The actual circuit converse of (2.10) with catalyst and pointwise query cost. -/
def Adversary_Converse : Prop :=
  ∀ (H Q : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
    (_ : NormedAddCommGroup Q) (_ : InnerProductSpace ℂ Q) (_ : CompleteSpace Q)
    (X : Type) (O : X → Q ≃ₗᵢ[ℂ] Q) (ξ τ : X → H) (v : X → Q),
    Query.Witness O ξ τ v →
    ∃ (I : Set (Stabilize.HilbertPair H Q))
      (c : Query.Circuit (Stabilize.HilbertPair H (Query.CanonicalPrivate I H Q))
        (Stabilize.HilbertPair H (Gram.StabilizingSpace I)) Q)
      (w : X → Query.CanonicalPrivate I H Q),
      Query.Exact c O ξ τ w ∧ ∀ x,
        Query.cost (O x) c (WithLp.toLp 2 (ξ x, w x)) = ‖v x‖ ^ 2 ∧
        ‖w x‖ ^ 2 = ‖v x‖ ^ 2

/-- Equation (1.2) and its attained separable operational realization. -/
def Theorem11_Restricted (gap : Gap) (n : ℕ) [NeZero n] : Prop :=
  Costs.C_adm gap n = ENNReal.ofReal (1 / (1 - Real.sqrt (1 - 4 * gap.δ ^ 2))) ∧
  Costs.C_adm gap n = ENNReal.ofReal ((1 + gap.mu) / (4 * gap.δ ^ 2)) ∧
  ∃ T : Costs.Realization gap n, T.Admissible ∧ T.uniformCost = Costs.C_adm gap n ∧
    TopologicalSpace.SeparableSpace T.Private

/-- Full operational signed-Gram characterization on arbitrary Hilbert controls. -/
def Prop41_Operational (gap : Gap) (n : ℕ) [NeZero n] : Prop :=
  Costs.C_adm gap n = Costs.twoSpaceValue gap n

/-- The exact bilateral-shift counterexample in Remark 2.2. -/
def Remark22 : Prop :=
  ¬ ∃ (τ : ℂ) (w : Query.CounterLine), inner ℂ Query.counterOrigin w = 0 ∧
    Query.bilateralShift (Query.counterOrigin + w) = τ • Query.counterOrigin + w

/-- Full operational Proposition 4.2, on actual forward/inverse amplitudes. -/
def Prop42_Operational (gap : Gap) (n : ℕ) [NeZero n] : Prop :=
  (∀ T : Costs.Realization gap n, T.Admissible →
    (T.NoForward ∨ T.NoInverse) → T.uniformCost = ⊤) ∧
  Costs.oneDirectionValue gap n = ⊤

/-- Complete Lemma 3.1 on an explicitly fixed public/private query circuit,
including executed cost, actual catalyst norm, and zero-catalyst endpoints. -/
def Lemma31_Full : Prop :=
  ∀ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E) (_ : CompleteSpace E)
    (s : E) (hs : ‖s‖ = 1),
  (∀ (p : ℝ), 0 < p → p < 1 → p ≠ 1/2 →
    ∀ (t : E), ‖t‖ = 1 → inner ℂ s t = 0 → ∀ (R : E ≃ₗᵢ[ℂ] E),
    R s = (Line.matrixMean p : ℂ) • s + (Line.matrixOff p : ℂ) • t →
    R t = (Line.matrixOff p : ℂ) • s - (Line.matrixMean p : ℂ) • t →
    ∃ w : Line.Private s,
      Query.run (Query.lpCongr R) (Line.publicCircuit s hs) (WithLp.toLp 2 ((1 : ℂ),w)) =
        WithLp.toLp 2 (Line.phaseSign p,w) ∧
      Query.cost (Query.lpCongr R) (Line.publicCircuit s hs) (WithLp.toLp 2 ((1 : ℂ),w)) = 1/|1-2*p| ∧
      ‖w‖ ^ 2 = min p (1-p)/|1-2*p|) ∧
  (∀ (R : E ≃ₗᵢ[ℂ] E) (ζ : ℂ), ζ^2 = 1 → R s = ζ • s →
    Query.run (Query.lpCongr R) (Line.publicCircuit s hs) (WithLp.toLp 2 ((1 : ℂ),(0 : Line.Private s))) =
      WithLp.toLp 2 (ζ,(0 : Line.Private s)) ∧
    Query.cost (Query.lpCongr R) (Line.publicCircuit s hs) (WithLp.toLp 2 ((1 : ℂ),(0 : Line.Private s))) = 1)

/-- Full Theorem 1.1, including both actual minimax values and separable attainments. -/
def Theorem11_Full (gap : Gap) (n : ℕ) [NeZero n] : Prop :=
  Costs.C_sg gap n = ENNReal.ofReal (1/(2*gap.δ)) ∧
  Costs.C_adm gap n = ENNReal.ofReal (1/(1-Real.sqrt (1-4*gap.δ^2))) ∧
  Costs.C_adm gap n = ENNReal.ofReal ((1+gap.mu)/(4*gap.δ^2)) ∧
  (∃ T : Costs.Realization gap n, T.uniformCost=Costs.C_sg gap n ∧
    TopologicalSpace.SeparableSpace T.Private) ∧
  (∃ T : Costs.Realization gap n, T.Admissible ∧ T.uniformCost=Costs.C_adm gap n ∧
    TopologicalSpace.SeparableSpace T.Private)

/-- Original fixed four-query construction, actual catalyst norm, and uniform complexity bound. -/
def FourQuery_Full (n : ℕ) [NeZero n] : Prop :=
  Query.queryCount (FourQuery.circuit n)=4 ∧
  (∀ O : Model.Nonbalanced n,
    Query.run (Query.bidirectional ℕ O.val) (FourQuery.circuit n)
      (WithLp.toLp 2 (Costs.publicBasis 0,FourQuery.catalyst O)) =
      WithLp.toLp 2 (Costs.publicBasis O.val.r,FourQuery.catalyst O) ∧
    Query.cost (Query.bidirectional ℕ O.val) (FourQuery.circuit n)
      (WithLp.toLp 2 (Costs.publicBasis 0,FourQuery.catalyst O)) = 1/|1-2*O.val.p| ∧
    ‖FourQuery.catalyst O‖^2 = min O.val.p (1-O.val.p)/(2*|1-2*O.val.p|)) ∧
  (∀ gap : Gap,
    (FourQuery.realization gap n).uniformCost=Costs.C_sg gap n ∧
    TopologicalSpace.SeparableSpace (FourQuery.realization gap n).Private ∧
    ∀ O : Costs.promisedFamily n gap.δ,
      ‖FourQuery.catalyst (Unrestricted.promisedInstance gap O)‖^2 ≤ (1-2*gap.δ)/(8*gap.δ))

/-- Direct operational corollaries in introduction S1.p6 / S1.Ex1.
The explicit bound gives the stated O(delta^2) remainder as delta -> 0+. -/
def Introduction_Consequences : Prop :=
  (∀ (n : ℕ) [NeZero n],
    Costs.C_sg Costs.quarterGap n = ENNReal.ofReal 2 ∧
    Costs.C_adm Costs.quarterGap n = ENNReal.ofReal (4+2*Real.sqrt 3)) ∧
  (∀ (gap : Gap) (n : ℕ) [NeZero n],
    (Costs.C_adm gap n).toReal - (1/(2*gap.δ^2)-1/2) = -(2*gap.δ^2)/(1+gap.mu)^2 ∧
    |(Costs.C_adm gap n).toReal - (1/(2*gap.δ^2)-1/2)| ≤ 2*gap.δ^2) ∧
  (∀ (gap : Gap) (n m : ℕ) [NeZero n] [NeZero m],
    Costs.C_sg gap n=Costs.C_sg gap m ∧ Costs.C_adm gap n=Costs.C_adm gap m)

end Verification.Specification
