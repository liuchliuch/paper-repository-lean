import ELV.Basic
import ELV.CostIdentities
import ELV.Oracle
import ELV.Amplification
import Mathlib.Data.ENNReal.Basic

/-! Operational minimax values (2.8)--(2.9). The optimization ranges over
actual fixed finite circuits and their instance-dependent returned catalysts.
Private and control spaces may be infinite dimensional; costs lie in ENNReal,
so an unbounded family has value infinity rather than the real `sSup` default. -/
noncomputable section
open scoped ENNReal
namespace ELV.Costs
open ELV.Model ELV.Cost ELV.Stabilize

/-- The entire promised family, with no chosen unitary completions removed. -/
def promisedFamily (n : ℕ) [NeZero n] (δ : ℝ) : Type :=
  { O : Oracle n // O.Promised δ }

def genState {n : ℕ} [NeZero n] (δ : ℝ) (O : promisedFamily n δ) : Mspace n := O.val.phi

def label {n : ℕ} [NeZero n] (δ : ℝ) (O : promisedFamily n δ) : Fin 2 := O.val.r

abbrev Public := EuclideanSpace ℂ (Fin 2)
def publicBasis (b : Fin 2) : Public := (EuclideanSpace.basisFun (Fin 2) ℂ) b

/-- An actual query vector is ray-supported when each ancillary coordinate
is on the prescribed input and generated-state rays. -/
def RaySupported {n : ℕ} [NeZero n] {C : Type*} (O : Oracle n)
    (v : Query.OracleQuerySpace n C) : Prop :=
  ∃ f g : lp (fun _ : C => ℂ) 2, ∀ i,
    (v i).fst = f i • knownInput n ∧ (v i).snd = g i • O.phi

/-- Exact purifiers in the operational model. `exact` is the validity
condition on a circuit, not an existence assumption used in an upper bound. -/
structure Realization (gap : Gap) (n : ℕ) [NeZero n] where
  Control : Type
  Private : Type
  Nonquery : Type
  [privateNorm : NormedAddCommGroup Private]
  [privateInner : InnerProductSpace ℂ Private]
  [privateComplete : CompleteSpace Private]
  [nonqueryNorm : NormedAddCommGroup Nonquery]
  [nonqueryInner : InnerProductSpace ℂ Nonquery]
  [nonqueryComplete : CompleteSpace Nonquery]
  circuit : Query.Circuit (HilbertPair Public Private) Nonquery (Query.OracleQuerySpace n Control)
  catalyst : promisedFamily n gap.δ → Private
  exact : Query.Exact circuit (fun O => Query.bidirectional Control O.val)
    (fun _ => publicBasis 0) (fun O => publicBasis (label gap.δ O)) catalyst

attribute [instance] Realization.privateNorm Realization.privateInner Realization.privateComplete
  Realization.nonqueryNorm Realization.nonqueryInner Realization.nonqueryComplete

namespace Realization
variable {gap : Gap} {n : ℕ} [NeZero n]

/-- Executed Las Vegas cost (2.5), before the uniform supremum. -/
def pointwiseCost (T : Realization gap n) (O : promisedFamily n gap.δ) : ℝ≥0∞ :=
  ENNReal.ofReal (Query.cost (Query.bidirectional T.Control O.val) T.circuit
    (WithLp.toLp 2 (publicBasis 0, T.catalyst O)))

def uniformCost (T : Realization gap n) : ℝ≥0∞ := ⨆ O, T.pointwiseCost O

/-- Every actual query gate has the required two ray supports (2.6). -/
def Admissible (T : Realization gap n) : Prop :=
  ∀ O : promisedFamily n gap.δ, ∀ i : Fin T.circuit.length,
    RaySupported O.val (Query.trace (Query.bidirectional T.Control O.val) T.circuit
      (WithLp.toLp 2 (publicBasis 0, T.catalyst O)) i)

end Realization

/-- The unrestricted minimax value, on the full family of actual unitary oracles. -/
def C_sg (gap : Gap) (n : ℕ) [NeZero n] : ℝ≥0∞ :=
  sInf { c | ∃ T : Realization gap n, T.uniformCost = c }

/-- The admissible minimax value, defined by the same actual circuit cost. -/
def C_adm (gap : Gap) (n : ℕ) [NeZero n] : ℝ≥0∞ :=
  sInf { c | ∃ T : Realization gap n, T.Admissible ∧ T.uniformCost = c }

/-- Restricting query support can only increase the operational minimax cost. -/
theorem access_monotone (gap : Gap) (n : ℕ) [NeZero n] : C_sg gap n ≤ C_adm gap n := by
  apply sInf_le_sInf
  rintro c ⟨T, _, hc⟩
  exact ⟨T, hc⟩

/-- The signed-Gram feasibility condition (4.2) on arbitrary Hilbert control
spaces. Its operational equivalence is a theorem to prove, not a definition of C_adm. -/
def AdmissibleWitness {n : ℕ} [NeZero n] (δ : ℝ)
    {Kf Kg : Type*} [NormedAddCommGroup Kf] [InnerProductSpace ℂ Kf]
    [NormedAddCommGroup Kg] [InnerProductSpace ℂ Kg]
    (f : promisedFamily n δ → Kf) (g : promisedFamily n δ → Kg) : Prop :=
  ∀ O O',
    (if label δ O = label δ O' then (0 : ℂ) else 1) =
      (1 - inner ℂ (genState δ O) (genState δ O')) *
        (inner ℂ (f O) (f O') - inner ℂ (g O) (g O'))

/-- Witness optimization cost, allowing a genuinely infinite supremum. -/
def uniformWitnessCost {n : ℕ} [NeZero n] (δ : ℝ)
    {Kf Kg : Type*} [NormedAddCommGroup Kf] [NormedAddCommGroup Kg]
    (f : promisedFamily n δ → Kf) (g : promisedFamily n δ → Kg) : ℝ≥0∞ :=
  ⨆ O, ENNReal.ofReal (‖f O‖ ^ 2 + ‖g O‖ ^ 2)

/-- Numerical candidates are kept distinct from the operational values. -/
def target_sg (gap : Gap) : ℝ := sgValue gap
def target_adm (gap : Gap) : ℝ := admValue gap

lemma target_pos (gap : Gap) : 0 < target_sg gap ∧ 0 < target_adm gap :=
  ⟨sgValue_pos gap, admValue_pos gap⟩
lemma target_adm_eq (gap : Gap) : target_adm gap = admValueAlt gap := admValue_eq_alt gap
lemma adm_target_eq (gap : Gap) : target_adm gap = 1 / (1 - gap.mu) := admValue_eq gap
lemma phase_boundary (gap : Gap) (p : ℝ) (hp : |p - 1 / 2| = gap.δ) :
    1 / (2 * |p - 1 / 2|) = target_sg gap := by
  unfold target_sg sgValue
  rw [hp]

theorem zero_witness_infeasible (z : ℂ) (hne : z ≠ 1) :
    ¬ ((1 : ℂ) = (1 - z) * 0) := by simp

end ELV.Costs
