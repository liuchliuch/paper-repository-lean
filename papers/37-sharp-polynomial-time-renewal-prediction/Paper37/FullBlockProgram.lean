import Paper37.UniformPredictionMachine
import Paper37.CachedQueries

/-! A fixed finite program for the source full-block probability Q_N(x).
The visible-tail likelihood and its ordinary normalizer are computed by two
actual continuation queries with the same integer denominator. That common
denominator cancels; neither normalization nor the first-renewal mixture is
omitted. The observed word is the sole varying machine input. -/
namespace Paper37.FullBlockProgram
noncomputable section
open Paper37.BoundedLoop Paper37.WordProgram Paper37.IntegerPredictorProgram
open Paper37.CachedOutput Paper37.Prediction Paper37.EnvelopeBridge Paper37.DP
open Paper37.IntegerQueryProgramPeak Paper37.IntegerOutputPeak
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
private abbrev v := Expr.var
private abbrev n := Expr.lit

/-- Both queries use the same cache horizon; the normalizer includes all
completions of the empty tail of length |z|. -/
def visiblePair (H N : ℕ) (z : List Bool) : ℕ × ℕ :=
  ((evaluatePair H z 0).1,(N+1)*(evaluatePair H [] z.length).1)

def blockPair (x : List Bool) : ℕ × ℕ :=
  match firstSuffix x with
  | none => (1,x.length+1)
  | some z => visiblePair (x.length+1) x.length z

lemma continuationMass_self (z : List Bool) :
    continuationMass z.length z=wordEnvelope z := by
  simp [continuationMass,Paper37.Renewal.words]

lemma normalizerNumerator_pos (H L : ℕ) (hL : L≤H) :
    0<(evaluatePair H [] L).1 := by
  have he:=evaluatePair_correct H [] L (by simpa using hL)
  rw [evaluatePair_eq H [] L (by simpa using hL)] at he ⊢
  simp only [List.length_nil,zero_add,continuationMass_nil] at he
  have hd : (0:ℚ)<commonDenominator H := by exact_mod_cast commonDenominator_pos H
  have hp : (0:ℚ)<(Paper37.IntegerOutput.numerator H [] L:ℚ)/commonDenominator H := by
    rw [he];exact ordinaryNormalizer_pos L
  exact_mod_cast ((div_pos_iff_of_pos_right hd).mp hp)

lemma visiblePair_denominator_pos (H N : ℕ) (z : List Bool) (hz : z.length≤H) :
    0<(visiblePair H N z).2 := by
  exact Nat.mul_pos (by omega) (normalizerNumerator_pos H z.length hz)

lemma visiblePair_exact (H N : ℕ) (z : List Bool) (hz : z.length≤H) :
    ((visiblePair H N z).1:ℚ)/(visiblePair H N z).2=
      wordEnvelope z/((N+1:ℚ)*ordinaryNormalizer z.length) := by
  have hp:=evaluatePair_correct H z 0 (by omega)
  have hq:=evaluatePair_correct H [] z.length (by simpa using hz)
  have ep:=evaluatePair_eq H z 0 (by omega)
  have eq:=evaluatePair_eq H [] z.length (by simpa using hz)
  simp only [Nat.add_zero,continuationMass_self] at hp
  simp only [List.length_nil,zero_add,continuationMass_nil] at hq
  rw [ep] at hp
  rw [eq] at hq
  have hd : (commonDenominator H:ℚ)≠0 := by exact_mod_cast (commonDenominator_pos H).ne'
  unfold visiblePair
  rw [ep,eq]
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  rw [← hp,← hq]
  field_simp

lemma blockPair_denominator_pos (x : List Bool) : 0<(blockPair x).2 := by
  unfold blockPair
  cases hs:firstSuffix x with
  | none => simp
  | some z =>
    obtain ⟨hl,hd⟩:=firstIndex_some x z hs
    exact visiblePair_denominator_pos _ _ _ (by omega)

lemma blockPair_exact (x : List Bool) :
    ((blockPair x).1:ℚ)/(blockPair x).2=blockAssignment x := by
  unfold blockPair blockAssignment
  cases hs:firstSuffix x with
  | none => simp
  | some z =>
    obtain ⟨hl,hd⟩:=firstIndex_some x z hs
    rw [visiblePair_exact _ _ _ (by omega)]
    simp [ordinaryAssignment,div_div,mul_comm]

/-- Final fixed arithmetic on the two actual query outputs. -/
def finalArray : Expr := .array [.get (v 70) (n 0),
  .mul (.add (v 49) (n 1)) (.get (v 71) (n 0))]

/-- Slot49 retains the full block length. Slot48 retains the visible-tail
length while the second query replaces word40 by the empty word. -/
def visibleProgram : Expr := .bind 48 (.length (v 40))
  (.bind 12 (n 0) (.bind 70 continuationProgram
    (.bind 40 (.array []) (.bind 12 (v 48) (.bind 71 continuationProgram finalArray)))))

def visibleBranch : Expr := .bind 44 (.add (v 47) (n 1))
  (.bind 40 dropProgram visibleProgram)

def zeroArray : Expr := .array [n 1,.add (v 49) (n 1)]

/-- One finite syntax term for every input length, including the empty word.
The harmless extra cache horizon guarantees positive horizon in every run. -/
def program : Expr := .bind 0 (.add (.length (v 40)) (n 1))
  (.bind 49 (.length (v 40)) (.bind 47 firstIndexProgram
    (.ifLT (v 47) (v 49) visibleBranch zeroArray)))

lemma visibleProgram_eval (ρ : Env) (H N : ℕ) (z : List Bool)
    (hH : ρ 0=.nat H) (hN : ρ 49=.nat N) (hw : ρ 40=wordValue z)
    (hz : z.length≤H) :
    visibleProgram.eval ρ=pairValue (visiblePair H N z) := by
  let ρL:=Function.update ρ 48 (.nat z.length)
  let ρR:=Function.update ρL 12 (.nat 0)
  have hp:=continuationProgram_eval ρR H z 0 (by simpa [ρR,ρL] using hH)
    (by simpa [ρR,ρL] using hw) (by simp [ρR]) (by omega)
  let ρp:=Function.update ρR 70 (pairValue (evaluatePair H z 0))
  let ρe:=Function.update ρp 40 (wordValue [])
  let ρT:=Function.update ρe 12 (.nat z.length)
  have hq:=continuationProgram_eval ρT H [] z.length (by simpa [ρT,ρe,ρp,ρR,ρL] using hH)
    (by simp [ρT,ρe]) (by simp [ρT]) (by simpa using hz)
  rw [visibleProgram,Expr.eval,show (Expr.length (v 40)).eval ρ=.nat z.length by
    simp [Expr.eval,hw]]
  change (Expr.bind 12 (n 0) _).eval ρL=_
  rw [Expr.eval,show (n 0).eval ρL=.nat 0 by simp [n,Expr.eval]]
  change (Expr.bind 70 continuationProgram _).eval ρR=_
  rw [Expr.eval,hp]
  change (Expr.bind 40 (.array []) _).eval ρp=_
  rw [Expr.eval,show (Expr.array []).eval ρp=wordValue [] by simp [Expr.eval,wordValue]]
  change (Expr.bind 12 (v 48) _).eval ρe=_
  rw [Expr.eval,show (v 48).eval ρe=.nat z.length by simp [Expr.eval,ρe,ρp,ρR,ρL]]
  change (Expr.bind 71 continuationProgram finalArray).eval ρT=_
  rw [Expr.eval,hq]
  simp [finalArray,Expr.eval,ρT,ρe,ρp,ρR,ρL,hN,pairValue,visiblePair,
    Value.arrayVal,Value.natVal]

lemma visibleBranch_eval (ρ : Env) (H : ℕ) (x z : List Bool)
    (hH : ρ 0=.nat H) (hN : ρ 49=.nat x.length) (hw : ρ 40=wordValue x)
    (hi : ρ 47=.nat (firstIndex x)) (hs : firstSuffix x=some z)
    (hz : z.length≤H) : visibleBranch.eval ρ=pairValue (visiblePair H x.length z) := by
  obtain ⟨hl,hd⟩:=firstIndex_some x z hs
  let ρd:=Function.update ρ 44 (.nat (firstIndex x+1))
  have he:=dropProgram_eval ρd x (firstIndex x+1) (by simpa [ρd] using hw) (by simp [ρd])
  rw [hd] at he
  simp only [visibleBranch,Expr.eval,hi,Value.natVal]
  change visibleProgram.eval (Function.update ρd 40 (dropProgram.eval ρd))=_
  rw [he]
  exact visibleProgram_eval _ H x.length z (by simpa [ρd] using hH)
    (by simpa [ρd] using hN) (by simp) hz

/-- Actual finite-program semantics on arbitrary unused environment slots. -/
theorem program_eval (ρ : Env) (x : List Bool) (hw : ρ 40=wordValue x) :
    program.eval ρ=pairValue (blockPair x) := by
  let ρH:=Function.update ρ 0 (.nat (x.length+1))
  let ρN:=Function.update ρH 49 (.nat x.length)
  have hi:=firstIndexProgram_eval ρN x (by simpa [ρN,ρH] using hw)
  let ρi:=Function.update ρN 47 (.nat (firstIndex x))
  rw [program,Expr.eval,show (Expr.add (.length (v 40)) (n 1)).eval ρ=.nat (x.length+1) by
    simp [Expr.eval,hw,Value.natVal]]
  change (Expr.bind 49 (.length (v 40)) _).eval ρH=_
  rw [Expr.eval,show (Expr.length (v 40)).eval ρH=.nat x.length by simp [Expr.eval,ρH,hw]]
  change (Expr.bind 47 firstIndexProgram _).eval ρN=_
  rw [Expr.eval,hi]
  change (Expr.ifLT (v 47) (v 49) visibleBranch zeroArray).eval ρi=_
  cases hs:firstSuffix x with
  | none =>
    have hh:=firstIndex_none x hs
    simp [Expr.eval,ρi,ρN,ρH,hh,zeroArray,blockPair,hs,pairValue,Value.natVal]
  | some z =>
    obtain ⟨hl,hd⟩:=firstIndex_some x z hs
    have hh:firstIndex x<x.length:=by omega
    rw [show (Expr.ifLT (v 47) (v 49) visibleBranch zeroArray).eval ρi=visibleBranch.eval ρi by
      simp [Expr.eval,ρi,ρN,hh,Value.natVal]]
    simpa [blockPair,hs] using visibleBranch_eval ρi (x.length+1) x z
      (by simp [ρi,ρN,ρH]) (by simp [ρi,ρN])
      (by simpa [ρi,ρN,ρH] using hw) (by simp [ρi]) hs (by omega)

end
end Paper37.FullBlockProgram
