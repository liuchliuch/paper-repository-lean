import Paper25.ClassicalDataCompilation

/-! A fixed classical parser for unary natural vectors. No quantum types or
paper-specific positions occur in this external data interface. -/
noncomputable section
namespace Paper25.OperationalModel.UniformCompilation

/-- A generic unary natural vector with one ambient-size header. -/
def natVectorInput (r : ℕ × List ℕ) : Input :=
  encodeNat r.1 ++ encodeNat r.2.length ++ (r.2.map encodeNat).flatten

def natVectorEntryInput (r : ℕ × (ℕ × List ℕ)) : Input :=
  encodeNat r.1 ++ natVectorInput r.2

/-- A fixed classical parser for an indexed unary natural vector. The index
and vector are literal input data; no quantum placement or circuit occurs. -/
structure NatVectorParsing : Prop where
  entry : LogspaceComputes natVectorEntryInput (fun r => encodeNat ((r.2.2[r.1]?).getD 0))

end Paper25.OperationalModel.UniformCompilation
