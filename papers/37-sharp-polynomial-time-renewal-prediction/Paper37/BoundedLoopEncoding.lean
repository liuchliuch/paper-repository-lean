import Paper37.BoundedLoopSize
import Mathlib.Computability.Encoding
import Mathlib.Tactic.DeriveFintype

/-! A concrete binary-and-delimiter encoding of nested integer arrays. The
finite alphabet has five symbols; each therefore has constant bit cost. -/
namespace Paper37.BoundedLoopEncoding
open Paper37.BoundedLoop

inductive Symbol where
  | bit : Bool → Symbol
  | natEnd
  | arrayOpen
  | arrayClose
  deriving DecidableEq, Fintype

def decodeBits (bs : List Bool) : ℕ := bs.foldr Nat.bit 0

lemma decodeBits_bits (n : ℕ) : decodeBits n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => simp [decodeBits,Nat.bits]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    simpa only [decodeBits,List.foldr_cons] using congrArg (Nat.bit b) ih

def encodeValue : Value → List Symbol
  | .nat n => n.bits.map Symbol.bit ++ [.natEnd]
  | .array vs => .arrayOpen :: (vs.flatMap encodeValue ++ [.arrayClose])

abbrev DecoderState := List Bool × List (List Value)

def pushValue (v : Value) : List (List Value) → List (List Value)
  | [] => [[v]]
  | a::as => (v::a)::as

def decoderStep (s : DecoderState) : Symbol → DecoderState
  | .bit b => (b::s.1,s.2)
  | .natEnd => ([],pushValue (.nat (decodeBits s.1.reverse)) s.2)
  | .arrayOpen => ([],[]::s.2)
  | .arrayClose => ([],match s.2 with
      | a::as => pushValue (.array a.reverse) as
      | [] => [])

def runDecoder (cs : List Symbol) (s : DecoderState) := cs.foldl decoderStep s

lemma runDecoder_append (a b : List Symbol) (s : DecoderState) :
    runDecoder (a++b) s=runDecoder b (runDecoder a s) := List.foldl_append

lemma runDecoder_bits (bs acc : List Bool) (s : List (List Value)) :
    runDecoder (bs.map Symbol.bit) (acc,s)=(bs.reverse++acc,s) := by
  induction bs generalizing acc with
  | nil => simp [runDecoder]
  | cons b bs ih =>
    simpa [runDecoder,decoderStep,List.reverse_cons,List.append_assoc] using ih (b::acc)

lemma runDecoder_encode (v : Value) (a : List Value) (as : List (List Value)) :
    runDecoder (encodeValue v) ([],a::as)=([],(v::a)::as) := by
  induction v using Value.rec
    (motive_2:=fun vs => ∀a as, runDecoder (vs.flatMap encodeValue) ([],a::as)=
      ([],(vs.reverse++a)::as)) generalizing a as with
  | nat n =>
    rw [encodeValue,runDecoder_append,runDecoder_bits]
    simp [runDecoder,decoderStep,pushValue,decodeBits_bits]
  | array vs ih =>
    simp only [encodeValue,runDecoder,List.foldl_cons,decoderStep]
    change runDecoder (vs.flatMap encodeValue ++ [.arrayClose]) ([],[]::a::as)=_
    rw [runDecoder_append,ih]
    simp [runDecoder,decoderStep,pushValue]
  | nil => simp [runDecoder]
  | cons v vs hv hvs =>
    simp only [List.flatMap_cons,runDecoder_append]
    rw [hv,hvs]
    simp [List.reverse_cons,List.append_assoc]

def decodeValue (cs : List Symbol) : Option Value :=
  match runDecoder cs ([],[[]]) with
  | ([],[[v]]) => some v
  | _ => none

lemma decodeValue_encode (v : Value) : decodeValue (encodeValue v)=some v := by
  unfold decodeValue
  rw [runDecoder_encode]

lemma encodeValue_length (v : Value) : (encodeValue v).length=v.representationSize := by
  induction v using Value.rec
    (motive_2:=fun vs => (vs.flatMap encodeValue).length=(vs.map Value.representationSize).sum) with
  | nat n => simp [encodeValue,Value.representationSize,Nat.size_eq_bits_len]
  | array vs ih => simp only [encodeValue,List.length_cons,List.length_append,List.length_nil,Value.representationSize,ih]
  | nil => simp
  | cons v vs hv hvs => simp [hv,hvs]

/-- A concrete constant-length three-bit representation of the five symbols. -/
def symbolBits : Symbol → List Bool
  | .bit false => [true,false,false]
  | .bit true => [true,false,true]
  | .natEnd => [false,false,false]
  | .arrayOpen => [false,false,true]
  | .arrayClose => [false,true,false]

def encodeSymbols (cs : List Symbol) : List Bool := cs.flatMap symbolBits

def decodeSymbols : List Bool → Option (List Symbol)
  | [] => some []
  | true::false::false::bs => (decodeSymbols bs).map (.bit false :: ·)
  | true::false::true::bs => (decodeSymbols bs).map (.bit true :: ·)
  | false::false::false::bs => (decodeSymbols bs).map (.natEnd :: ·)
  | false::false::true::bs => (decodeSymbols bs).map (.arrayOpen :: ·)
  | false::true::false::bs => (decodeSymbols bs).map (.arrayClose :: ·)
  | _ => none

lemma decodeSymbols_encode (cs : List Symbol) : decodeSymbols (encodeSymbols cs)=some cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change decodeSymbols (cs.flatMap symbolBits)=some cs at ih
    cases c with
    | bit b => cases b <;> simp [encodeSymbols,symbolBits,decodeSymbols,ih]
    | natEnd => simp [encodeSymbols,symbolBits,decodeSymbols,ih]
    | arrayOpen => simp [encodeSymbols,symbolBits,decodeSymbols,ih]
    | arrayClose => simp [encodeSymbols,symbolBits,decodeSymbols,ih]

lemma encodeSymbols_length (cs : List Symbol) : (encodeSymbols cs).length=3*cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc : (symbolBits c).length=3 := by cases c with
      | bit b => cases b <;> rfl
      | natEnd | arrayOpen | arrayClose => rfl
    simp [encodeSymbols,List.length_flatMap,hc] at ih ⊢
    omega

def encodeBits (v : Value) : List Bool := encodeSymbols (encodeValue v)
def decodeValueBits (bs : List Bool) : Option Value := decodeSymbols bs >>= decodeValue

lemma decodeValueBits_encode (v : Value) : decodeValueBits (encodeBits v)=some v := by
  simp [decodeValueBits,encodeBits,decodeSymbols_encode,decodeValue_encode]

lemma encodeBits_length (v : Value) : (encodeBits v).length=3*v.representationSize := by
  rw [encodeBits,encodeSymbols_length,encodeValue_length]

/-- Fully specified bit encoding; the decoder above is an executable finite
stack parser rather than an unspecified inverse or Gödel numbering. -/
def valueEncoding : Computability.FinEncoding Value where
  Γ := Bool
  encode := encodeBits
  decode := decodeValueBits
  decode_encode := decodeValueBits_encode
  ΓFin := inferInstance

def inputEncoding : Computability.FinEncoding (List Value) where
  Γ := Bool
  encode vs := encodeBits (.array vs)
  decode bs := (decodeValueBits bs).bind (fun v => match v with | .array vs => some vs | .nat _ => none)
  decode_encode vs := by simp [decodeValueBits_encode]
  ΓFin := inferInstance

/-- A finite input list supplies slots 0,...,length-1. Unprovided variables
have the same safe zero default as array indexing in the language. -/
def inputEnv (vs : List Value) : Env := fun i => vs[i]?.getD (.nat 0)

def runProgram (e : Expr) (vs : List Value) : Value := e.eval (inputEnv vs)

lemma inputEncoding_length (vs : List Value) :
    (inputEncoding.encode vs).length=3*((vs.map Value.representationSize).sum+2) := by
  simpa only [inputEncoding,Value.representationSize] using encodeBits_length (.array vs)

@[simp] lemma inputEnv_nil : inputEnv []=fun _ => .nat 0 := by
  funext i
  simp [inputEnv]

@[simp] lemma inputEnv_cons_zero (v : Value) (vs : List Value) : inputEnv (v::vs) 0=v := rfl
@[simp] lemma inputEnv_cons_succ (v : Value) (vs : List Value) (i : ℕ) :
    inputEnv (v::vs) (i+1)=inputEnv vs i := rfl


end Paper37.BoundedLoopEncoding
