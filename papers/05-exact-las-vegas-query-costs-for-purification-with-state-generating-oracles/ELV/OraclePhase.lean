import ELV.OraclePlane

/-! One fixed phase-purifier circuit serves every nonbalanced state-generating
oracle, including endpoints and every arbitrary unitary completion. -/
noncomputable section
namespace ELV.Model
open ELV.Line ELV.Query
variable {n : ℕ} [NeZero n]

abbrev Nonbalanced (n : ℕ) [NeZero n] := {O : Oracle n // O.p ≠ 1/2}
abbrev PhasePrivate (n : ℕ) [NeZero n] := Line.Private (knownInput n)
def phaseCircuit (n : ℕ) [NeZero n] := Line.publicCircuit (knownInput n) (knownInput_norm n)

/-- Actual phase transduction, executed cost, and actual catalyst norm. -/
theorem oracle_phase (O : Oracle n) (hne : O.p ≠ 1/2) :
    ∃ w : PhasePrivate n,
      Query.run (lpCongr O.pulledReflection) (phaseCircuit n) (WithLp.toLp 2 ((1 : ℂ),w)) =
        WithLp.toLp 2 (Line.phaseSign O.p,w) ∧
      Query.cost (lpCongr O.pulledReflection) (phaseCircuit n) (WithLp.toLp 2 ((1 : ℂ),w)) =
        1/|1-2*O.p| ∧
      ‖w‖ ^ 2 = min O.p (1-O.p)/|1-2*O.p| := by
  by_cases h0 : O.p = 0
  · have he := line_purifier_public_endpoint (knownInput n) (knownInput_norm n)
      O.pulledReflection 1 (by norm_num) (by simpa using O.reflected_known_low_endpoint h0)
    refine ⟨0,?_,?_,?_⟩
    · simpa [Line.phaseSign,h0] using he.1
    · simpa [phaseCircuit,h0] using he.2
    · simp [h0]
  · by_cases h1 : O.p = 1
    · have he := line_purifier_public_endpoint (knownInput n) (knownInput_norm n)
        O.pulledReflection (-1) (by norm_num) (by simpa using O.reflected_known_high_endpoint h1)
      refine ⟨0,?_,?_,?_⟩
      · convert he.1 using 1 <;> norm_num [Line.phaseSign,h1,phaseCircuit]
      · convert he.2 using 1 <;> norm_num [phaseCircuit,h1]
      · simp [h1]
    · have hp0 : 0 < O.p := lt_of_le_of_ne O.p_nonneg (Ne.symm h0)
      have hp1 : O.p < 1 := lt_of_le_of_ne O.p_le_one h1
      exact line_purifier_public (knownInput n) (knownInput_norm n) O.p hp0 hp1 hne
        O.tangent (O.tangent_norm hp0 hp1) O.tangent_orthogonal O.pulledReflection
        (O.reflected_known_plane hp0 hp1) (O.reflected_tangent_plane hp0 hp1)

def phaseCatalyst (O : Nonbalanced n) : PhasePrivate n := (oracle_phase O.val O.property).choose

lemma phaseCatalyst_spec (O : Nonbalanced n) :
    Query.run (lpCongr O.val.pulledReflection) (phaseCircuit n)
      (WithLp.toLp 2 ((1 : ℂ),phaseCatalyst O)) = WithLp.toLp 2 (Line.phaseSign O.val.p,phaseCatalyst O) ∧
    Query.cost (lpCongr O.val.pulledReflection) (phaseCircuit n)
      (WithLp.toLp 2 ((1 : ℂ),phaseCatalyst O)) = 1/|1-2*O.val.p| ∧
    ‖phaseCatalyst O‖ ^ 2 = min O.val.p (1-O.val.p)/|1-2*O.val.p| :=
  (oracle_phase O.val O.property).choose_spec

theorem phase_exact :
    Query.Exact (phaseCircuit n) (fun O : Nonbalanced n => lpCongr O.val.pulledReflection)
      (fun _ => (1 : ℂ)) (fun O => Line.phaseSign O.val.p) phaseCatalyst :=
  fun O => (phaseCatalyst_spec O).1

end ELV.Model
