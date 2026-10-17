import Paper37.UniformQueryMachine

/-! The actual ordinary normalizer Z_L is a closed specialization of the
already compiled continuation query (H=L, word=[], remaining=L). No new
algorithmic AST or normalizer computability premise is introduced. -/
namespace Paper37.UniformNormalizerMachine
noncomputable section
open Paper37.BoundedLoop Paper37.BoundedLoopEncoding Paper37.BoundedLoopMachine
open Paper37.UniformQueryMachine Paper37.IntegerPredictorProgram

/-- The normalizer sums the completed-gap envelope over every length-L word. -/
def normalizerQuery (L : ℕ) : Query := ⟨L,[],L,by simp⟩
def normalizerInputs (L : ℕ) : List Value := queryInputs (normalizerQuery L)

def normalizerEncoding : Computability.FinEncoding ℕ where
  Γ := Bool
  encode L := inputEncoding.encode (normalizerInputs L)
  decode bs := (inputEncoding.decode bs).map (fun xs => (inputEnv xs 0).natVal)
  decode_encode L := by
    simp [inputEncoding.decode_encode,normalizerInputs,queryInputs_horizon,normalizerQuery,Value.natVal]
  ΓFin := inferInstance

lemma normalizerEncoding_length (L : ℕ) :
    L≤(normalizerEncoding.encode L).length ∧ (normalizerEncoding.encode L).length≤15*L+132 :=
  queryEncoding_length (normalizerQuery L)

lemma continuation_empty_eq_normalizer (L : ℕ) :
    Paper37.Prediction.continuationMass L []=Paper37.Prediction.ordinaryNormalizer L := by
  simp [Paper37.Prediction.continuationMass,Paper37.Prediction.ordinaryNormalizer]

def normalizerRun (L : ℕ) : Value := runProgram continuationProgram (normalizerInputs L)

lemma normalizerRun_denominator_pos (L : ℕ) :
    0<((normalizerRun L).arrayVal[1]?.getD (Value.nat 0)).natVal :=
  queryRun_denominator_pos (normalizerQuery L)

/-- The output is precisely Z_L, including L=0. It is not an observed-word
envelope value or a no-future-renewal term. -/
theorem normalizerRun_exact (L : ℕ) :
    (((normalizerRun L).arrayVal[0]?.getD (Value.nat 0)).natVal:ℚ) /
      ((normalizerRun L).arrayVal[1]?.getD (Value.nat 0)).natVal =
      Paper37.Prediction.ordinaryNormalizer L := by
  have h:=queryRun_exact (normalizerQuery L)
  simpa only [normalizerQuery,List.length_nil,zero_add,continuation_empty_eq_normalizer] using h

/-- Reuse the very same genuine finite continuation TM, merely restricting
its explicit input/output encoding to normalizer queries. -/
def normalizerTMPoly (simulation : BoundedLoopSimulationPrinciple) :
    Turing.TM2ComputableInPolyTime normalizerEncoding valueEncoding normalizerRun where
  toTM2ComputableAux := (queryTMPoly simulation).toTM2ComputableAux
  time := (queryTMPoly simulation).time
  outputsFun L := (queryTMPoly simulation).outputsFun (normalizerQuery L)

/-- A real finite polynomial-time TM computes the actual source Z_L with a
positive-denominator exact rational representation, on explicit padded input. -/
theorem actualNormalizer_polytime (simulation : BoundedLoopSimulationPrinciple) :
    ∃ M : Turing.TM2ComputableInPolyTime normalizerEncoding valueEncoding normalizerRun,
      (∀ k : M.tm.K, Finite (M.tm.Γ k)) ∧
      (∀ L : ℕ, 0<((normalizerRun L).arrayVal[1]?.getD (Value.nat 0)).natVal) ∧
      (∀ L : ℕ, (((normalizerRun L).arrayVal[0]?.getD (Value.nat 0)).natVal:ℚ) /
        ((normalizerRun L).arrayVal[1]?.getD (Value.nat 0)).natVal=Paper37.Prediction.ordinaryNormalizer L) :=
  ⟨normalizerTMPoly simulation,(queryMachine simulation).finiteAlphabets,
    normalizerRun_denominator_pos,normalizerRun_exact⟩

end
end Paper37.UniformNormalizerMachine
