import ELV.UnrestrictedWitness

/-! Actual fixed full-oracle upper-bound circuit. Its work unitary is built
once on all nonbalanced oracles, so even the circuit is independent of delta. -/
noncomputable section
namespace ELV.Unrestricted
open ELV.Model ELV.Query ELV.Costs ELV.Stabilize

abbrev QuerySpace (n : ℕ) [NeZero n] := OracleQuerySpace n (Controls n)
abbrev Ambient (n : ℕ) [NeZero n] := HilbertPair Public (QuerySpace n)

def basisIndex (n : ℕ) [NeZero n] : Set (Ambient n) := (exists_hilbertBasis ℂ (Ambient n)).choose
def ambientBasis (n : ℕ) [NeZero n] : HilbertBasis (basisIndex n) ℂ (Ambient n) :=
  (exists_hilbertBasis ℂ (Ambient n)).choose_spec.choose

abbrev PrivateSpace (n : ℕ) [NeZero n] := CanonicalPrivate (basisIndex n) Public (QuerySpace n)
abbrev NonquerySpace (n : ℕ) [NeZero n] := HilbertPair Public (Gram.StabilizingSpace (basisIndex n))

/-- One fixed work/query circuit serves all nonbalanced oracle completions. -/
def circuit (n : ℕ) [NeZero n] :
    Circuit (HilbertPair Public (PrivateSpace n)) (NonquerySpace n) (QuerySpace n) :=
  canonicalCircuit (ambientBasis n) (feasible (n := n))

def catalyst {n : ℕ} [NeZero n] (O : Nonbalanced n) : PrivateSpace n := canonicalCatalyst witness O

lemma promised_nonbalanced {n : ℕ} [NeZero n] (gap : Gap) (O : Oracle n) (hp : O.Promised gap.δ) :
    O.p ≠ 1/2 := by
  intro he
  rcases hp with hl | hh
  · rw [he] at hl
    linarith [gap.δ_pos]
  · rw [he] at hh
    linarith [gap.δ_pos]

def promisedInstance {n : ℕ} [NeZero n] (gap : Gap) (O : promisedFamily n gap.δ) : Nonbalanced n :=
  ⟨O.val,promised_nonbalanced gap O.val O.property⟩

/-- Only the catalyst choice is restricted to a promised subfamily; the
private space, layouts and circuit themselves are independent of the gap. -/
def realization (gap : Gap) (n : ℕ) [NeZero n] : Realization gap n where
  Control := Controls n
  Private := PrivateSpace n
  Nonquery := NonquerySpace n
  circuit := circuit n
  catalyst := fun O => catalyst (promisedInstance gap O)
  exact := fun O => canonical_exact (ambientBasis n) (feasible (n := n)) (promisedInstance gap O)

/-- Pointwise executed cost, obtained from witness norm and actual canonical execution. -/
theorem pointwise_cost (gap : Gap) (n : ℕ) [NeZero n] (O : promisedFamily n gap.δ) :
    (realization gap n).pointwiseCost O = ENNReal.ofReal (1/|1-2*O.val.p|) := by
  change ENNReal.ofReal (Query.cost (bidirectional (Controls n) O.val)
    (canonicalCircuit (ambientBasis n) (feasible (n := n)))
    (WithLp.toLp 2 (publicBasis 0,canonicalCatalyst witness (promisedInstance gap O)))) = _
  exact congrArg ENNReal.ofReal
    ((canonical_cost (ambientBasis n) (feasible (n := n)) (promisedInstance gap O)).trans
      (witness_norm_sq (promisedInstance gap O)))

/-- The known gap is used only in bounding this fixed circuit's worst case. -/
lemma cost_le_gap {n : ℕ} [NeZero n] (gap : Gap) (O : promisedFamily n gap.δ) :
    1/|1-2*O.val.p| ≤ 1/(2*gap.δ) := by
  rcases O.property with hl | hh
  · rw [abs_of_nonneg (by linarith [gap.δ_pos] : 0 ≤ 1-2*O.val.p)]
    exact one_div_le_one_div_of_le (mul_pos (by norm_num) gap.δ_pos) (by linarith)
  · rw [abs_of_nonpos (by linarith [gap.δ_pos] : 1-2*O.val.p ≤ 0)]
    exact one_div_le_one_div_of_le (mul_pos (by norm_num) gap.δ_pos) (by linarith)

theorem uniform_cost_le (gap : Gap) (n : ℕ) [NeZero n] :
    (realization gap n).uniformCost ≤ ENNReal.ofReal (1/(2*gap.δ)) := by
  apply iSup_le
  intro O
  rw [pointwise_cost]
  exact ENNReal.ofReal_le_ofReal (cost_le_gap gap O)

/-- The constructed private space is separable, irrespective of family cardinality. -/
theorem private_separable (n : ℕ) [NeZero n] : TopologicalSpace.SeparableSpace (PrivateSpace n) := by
  letI : TopologicalSpace.SeparableSpace (QuerySpace n) := Query.lp_separable
  letI : Countable (basisIndex n) := Gram.hilbertBasis_countable (ambientBasis n)
  letI : TopologicalSpace.SeparableSpace (Gram.StabilizingSpace (basisIndex n)) :=
    Gram.stabilizingSpace_separable (basisIndex n)
  change TopologicalSpace.SeparableSpace (HilbertPair (QuerySpace n) (Gram.StabilizingSpace (basisIndex n)))
  infer_instance

/-- The unrestricted upper bound is on the actual operational C_sg. -/
theorem upper (gap : Gap) (n : ℕ) [NeZero n] : C_sg gap n ≤ ENNReal.ofReal (1/(2*gap.δ)) := by
  have hinf : C_sg gap n ≤ (realization gap n).uniformCost := sInf_le ⟨realization gap n,rfl⟩
  exact hinf.trans (uniform_cost_le gap n)

end ELV.Unrestricted
