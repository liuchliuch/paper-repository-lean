import Paper25.ClassicalDataCompilation
import Paper25.SelectedPreparation

/-! Generic conversions between raw natural representations, binary words and
unary counters. The binary-to-unary query carries an explicit unary range
padding; no exponential output on an unpadded binary word is assumed. -/
noncomputable section
namespace Paper25.OperationalModel.UniformCompilation
open LocalCompilation SelectedFilter

def rawNatRep (n : ℕ) : RationalRep := ⟨(n : ℤ), 1, by decide⟩

lemma rawNatRep_ofRat (n : ℕ) : rawNatRep n = RationalRep.ofRat (n : ℚ) := by
  simp [rawNatRep, RationalRep.ofRat]

abbrev BinaryWord := Σ n : ℕ, Basis n

def binaryWordInput (r : BinaryWord) : Input :=
  encodeNat r.1 ++ encodeNat (2^r.1) ++ List.ofFn r.2

abbrev BinaryIndex := Σ n : ℕ, Fin (2^n)

def binaryIndexInput (r : BinaryIndex) : Input :=
  encodeNat r.1 ++ encodeNat (2^r.1) ++ encodeNat r.2.val

/-- Standard raw binary/unary representation conversions, on actual bytes. -/
structure BinaryDataDescription : Prop where
  rawNat : LogspaceComputes encodeNat (fun n => (rawNatRep n).encode)
  wordValue : LogspaceComputes binaryWordInput
    (fun r => encodeNat (bitsBinaryIndex r.1 r.2).val)
  indexWord : LogspaceComputes binaryIndexInput
    (fun r => List.ofFn ((bitsBinaryIndex r.1).symm r.2))

lemma rawNat_generated (classical : FLListClosure) (binary : BinaryDataDescription)
    {α : Type} (encode : α → Input) (n : α → ℕ)
    (hn : LogspaceComputes encode (fun a => encodeNat (n a))) :
    LogspaceComputes encode (fun a => (rawNatRep (n a)).encode) :=
  classical.strings.compose encode encodeNat n _ hn binary.rawNat

lemma word_value_generated (classical : FLListClosure) (binary : BinaryDataDescription)
    {α : Type} {m : α → ℕ} (encode : α → Input) (word : ∀ a, Basis (m a))
    (hm : LogspaceComputes encode (fun a => encodeNat (m a)))
    (hM : LogspaceComputes encode (fun a => encodeNat (2^(m a))))
    (hword : LogspaceComputes encode (fun a => List.ofFn (word a))) :
    LogspaceComputes encode (fun a => encodeNat (bitsBinaryIndex (m a) (word a)).val) := by
  have hr : LogspaceComputes encode (fun a => binaryWordInput (⟨m a,word a⟩ : BinaryWord)) :=
    classical.strings.concat encode _ _ (classical.strings.concat encode _ _ hm hM) hword
  exact classical.strings.compose encode binaryWordInput (fun a => ⟨m a,word a⟩) _ hr binary.wordValue

lemma word_rawNat_generated (classical : FLListClosure) (binary : BinaryDataDescription)
    {α : Type} {m : α → ℕ} (encode : α → Input) (word : ∀ a, Basis (m a))
    (hm : LogspaceComputes encode (fun a => encodeNat (m a)))
    (hM : LogspaceComputes encode (fun a => encodeNat (2^(m a))))
    (hword : LogspaceComputes encode (fun a => List.ofFn (word a))) :
    LogspaceComputes encode (fun a => (rawNatRep (bitsBinaryIndex (m a) (word a)).val).encode) :=
  rawNat_generated classical binary encode _ (word_value_generated classical binary encode word hm hM hword)

lemma index_word_generated (classical : FLListClosure) (binary : BinaryDataDescription)
    {α : Type} {m : α → ℕ} (encode : α → Input) (index : ∀ a, Fin (2^(m a)))
    (hm : LogspaceComputes encode (fun a => encodeNat (m a)))
    (hM : LogspaceComputes encode (fun a => encodeNat (2^(m a))))
    (hi : LogspaceComputes encode (fun a => encodeNat (index a).val)) :
    LogspaceComputes encode (fun a => List.ofFn ((bitsBinaryIndex (m a)).symm (index a))) := by
  have hr : LogspaceComputes encode (fun a => binaryIndexInput (⟨m a,index a⟩ : BinaryIndex)) :=
    classical.strings.concat encode _ _ (classical.strings.concat encode _ _ hm hM) hi
  exact classical.strings.compose encode binaryIndexInput (fun a => ⟨m a,index a⟩) _ hr binary.indexWord

end Paper25.OperationalModel.UniformCompilation
