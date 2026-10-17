import Paper25.UniformCompilation
import Mathlib.Data.Nat.Log

/-! Generic classical unary counters and explicit array printers. The external
inputs are fixed arithmetic/bit-access machines and polynomially bounded loops.
There is no source, P25 parameter, placement, matrix or circuit transformer in
these external interfaces. All later paper-specific combinations are derived
using the ordinary composition closure. -/
noncomputable section
namespace Paper25.OperationalModel.UniformCompilation
open LocalCompilation
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000

def natPairInput (p : ℕ × ℕ) : Input := encodeNat p.1 ++ encodeNat p.2

def unaryArray (n : ℕ) (f : Fin n → ℕ) : Input :=
  encodeNat n ++ (List.ofFn (fun i => encodeNat (f i))).flatten

abbrev BitQuery := Σ n : ℕ, Basis n × Fin n

def bitQueryInput (r : BitQuery) : Input :=
  encodeNat r.1 ++ List.ofFn r.2.1 ++ encodeNat r.2.2.val

/-- Fixed generic arithmetic and bit-reading programs. `powTwo` states the
standard bounded-output version: its polynomial bound is an explicit premise. -/
structure NatArithmeticDescription : Prop where
  add : LogspaceComputes natPairInput (fun p => encodeNat (p.1+p.2))
  sub : LogspaceComputes natPairInput (fun p => encodeNat (p.1-p.2))
  mul : LogspaceComputes natPairInput (fun p => encodeNat (p.1*p.2))
  div : LogspaceComputes natPairInput (fun p => encodeNat (p.1/p.2))
  mod : LogspaceComputes natPairInput (fun p => encodeNat (p.1%p.2))
  lt : LogspaceComputes natPairInput (fun p => encodeBool (decide (p.1<p.2)))
  le : LogspaceComputes natPairInput (fun p => encodeBool (decide (p.1≤p.2)))
  eq : LogspaceComputes natPairInput (fun p => encodeBool (decide (p.1=p.2)))
  logTwo : LogspaceComputes encodeNat (fun n => encodeNat (Nat.log2 n))
  clogTwo : LogspaceComputes encodeNat (fun n => encodeNat (Nat.clog 2 n))
  powTwo : ∀ {α : Type} (encode : α → Input) (exponent : α → ℕ),
    LogspaceComputes encode (fun a => encodeNat (exponent a)) →
    PolynomialBoundOn encode (fun a => 2^(exponent a)) →
    LogspaceComputes encode (fun a => encodeNat (2^(exponent a)))
  bitAt : LogspaceComputes bitQueryInput (fun r => [r.2.1 r.2.2])
  unaryArray : ∀ {α : Type} (encode : α → Input) (count : α → ℕ)
    (value : ∀ a, Fin (count a) → ℕ),
    LogspaceComputes encode (fun a => encodeNat (count a)) →
    PolynomialBoundOn encode count →
    LogspaceComputes (indexedInput encode count) (fun p => encodeNat (value p.1 p.2)) →
    LogspaceComputes encode (fun a => UniformCompilation.unaryArray (count a) (value a))
  bitArray : ∀ {α : Type} (encode : α → Input) (count : α → ℕ)
    (value : ∀ a, Fin (count a) → Bit),
    LogspaceComputes encode (fun a => encodeNat (count a)) →
    PolynomialBoundOn encode count →
    LogspaceComputes (indexedInput encode count) (fun p => [value p.1 p.2]) →
    LogspaceComputes encode (fun a => List.ofFn (value a))

lemma nat_const (classical : FLListClosure) {α : Type} (encode : α → Input) (n : ℕ) :
    LogspaceComputes encode (fun _ => encodeNat n) :=
  classical.strings.constant encode (encodeNat n)

lemma nat_pair (classical : FLListClosure) {α : Type} (encode : α → Input)
    (f g : α → ℕ) (hf : LogspaceComputes encode (fun a => encodeNat (f a)))
    (hg : LogspaceComputes encode (fun a => encodeNat (g a))) :
    LogspaceComputes encode (fun a => natPairInput (f a,g a)) :=
  classical.strings.concat encode _ _ hf hg

lemma nat_binary (classical : FLListClosure) {α : Type} (encode : α → Input)
    (op : ℕ × ℕ → ℕ) (f g : α → ℕ)
    (hop : LogspaceComputes natPairInput (fun p => encodeNat (op p)))
    (hf : LogspaceComputes encode (fun a => encodeNat (f a)))
    (hg : LogspaceComputes encode (fun a => encodeNat (g a))) :
    LogspaceComputes encode (fun a => encodeNat (op (f a,g a))) :=
  classical.strings.compose encode natPairInput (fun a => (f a,g a)) _
    (nat_pair classical encode f g hf hg) hop

lemma nat_add (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    {α : Type} (encode : α → Input) (f g : α → ℕ)
    (hf : LogspaceComputes encode (fun a => encodeNat (f a)))
    (hg : LogspaceComputes encode (fun a => encodeNat (g a))) :
    LogspaceComputes encode (fun a => encodeNat (f a+g a)) :=
  nat_binary classical encode (fun p => p.1+p.2) f g arithmetic.add hf hg

lemma nat_sub (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    {α : Type} (encode : α → Input) (f g : α → ℕ)
    (hf : LogspaceComputes encode (fun a => encodeNat (f a)))
    (hg : LogspaceComputes encode (fun a => encodeNat (g a))) :
    LogspaceComputes encode (fun a => encodeNat (f a-g a)) :=
  nat_binary classical encode (fun p => p.1-p.2) f g arithmetic.sub hf hg

lemma nat_mul (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    {α : Type} (encode : α → Input) (f g : α → ℕ)
    (hf : LogspaceComputes encode (fun a => encodeNat (f a)))
    (hg : LogspaceComputes encode (fun a => encodeNat (g a))) :
    LogspaceComputes encode (fun a => encodeNat (f a*g a)) :=
  nat_binary classical encode (fun p => p.1*p.2) f g arithmetic.mul hf hg

lemma nat_div (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    {α : Type} (encode : α → Input) (f g : α → ℕ)
    (hf : LogspaceComputes encode (fun a => encodeNat (f a)))
    (hg : LogspaceComputes encode (fun a => encodeNat (g a))) :
    LogspaceComputes encode (fun a => encodeNat (f a/g a)) :=
  nat_binary classical encode (fun p => p.1/p.2) f g arithmetic.div hf hg

lemma nat_mod (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    {α : Type} (encode : α → Input) (f g : α → ℕ)
    (hf : LogspaceComputes encode (fun a => encodeNat (f a)))
    (hg : LogspaceComputes encode (fun a => encodeNat (g a))) :
    LogspaceComputes encode (fun a => encodeNat (f a%g a)) :=
  nat_binary classical encode (fun p => p.1%p.2) f g arithmetic.mod hf hg

lemma nat_test (classical : FLListClosure) {α : Type} (encode : α → Input)
    (op : ℕ × ℕ → Bool) (f g : α → ℕ)
    (hop : LogspaceComputes natPairInput (fun p => encodeBool (op p)))
    (hf : LogspaceComputes encode (fun a => encodeNat (f a)))
    (hg : LogspaceComputes encode (fun a => encodeNat (g a))) :
    LogspaceComputes encode (fun a => encodeBool (op (f a,g a))) :=
  classical.strings.compose encode natPairInput (fun a => (f a,g a)) _
    (nat_pair classical encode f g hf hg) hop

lemma nat_lt (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    {α : Type} (encode : α → Input) (f g : α → ℕ)
    (hf : LogspaceComputes encode (fun a => encodeNat (f a)))
    (hg : LogspaceComputes encode (fun a => encodeNat (g a))) :
    LogspaceComputes encode (fun a => encodeBool (decide (f a<g a))) :=
  nat_test classical encode (fun p => decide (p.1<p.2)) f g arithmetic.lt hf hg

lemma nat_le (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    {α : Type} (encode : α → Input) (f g : α → ℕ)
    (hf : LogspaceComputes encode (fun a => encodeNat (f a)))
    (hg : LogspaceComputes encode (fun a => encodeNat (g a))) :
    LogspaceComputes encode (fun a => encodeBool (decide (f a≤g a))) :=
  nat_test classical encode (fun p => decide (p.1≤p.2)) f g arithmetic.le hf hg

lemma nat_eq (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    {α : Type} (encode : α → Input) (f g : α → ℕ)
    (hf : LogspaceComputes encode (fun a => encodeNat (f a)))
    (hg : LogspaceComputes encode (fun a => encodeNat (g a))) :
    LogspaceComputes encode (fun a => encodeBool (decide (f a=g a))) :=
  nat_test classical encode (fun p => decide (p.1=p.2)) f g arithmetic.eq hf hg

lemma nat_if (classical : FLListClosure) {α : Type} (encode : α → Input)
    (p : α → Bool) (f g : α → ℕ)
    (hp : LogspaceComputes encode (fun a => encodeBool (p a)))
    (hf : LogspaceComputes encode (fun a => encodeNat (f a)))
    (hg : LogspaceComputes encode (fun a => encodeNat (g a))) :
    LogspaceComputes encode (fun a => encodeNat (if p a then f a else g a)) := by
  simpa only [apply_ite] using classical.strings.conditional encode p _ _ hp hf hg

lemma nat_pow_const (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    {α : Type} (encode : α → Input) (f : α → ℕ) (n : ℕ)
    (hf : LogspaceComputes encode (fun a => encodeNat (f a))) :
    LogspaceComputes encode (fun a => encodeNat ((f a)^n)) := by
  induction n with
  | zero => simpa using nat_const classical encode 1
  | succ n ih =>
    simpa only [pow_succ] using nat_mul classical arithmetic encode (fun a => (f a)^n) f ih hf

lemma nat_log2 (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    {α : Type} (encode : α → Input) (f : α → ℕ)
    (hf : LogspaceComputes encode (fun a => encodeNat (f a))) :
    LogspaceComputes encode (fun a => encodeNat (Nat.log2 (f a))) :=
  classical.strings.compose encode encodeNat f _ hf arithmetic.logTwo

lemma nat_clog2 (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    {α : Type} (encode : α → Input) (f : α → ℕ)
    (hf : LogspaceComputes encode (fun a => encodeNat (f a))) :
    LogspaceComputes encode (fun a => encodeNat (Nat.clog 2 (f a))) :=
  classical.strings.compose encode encodeNat f _ hf arithmetic.clogTwo

lemma nat_two_pow (arithmetic : NatArithmeticDescription)
    {α : Type} (encode : α → Input) (f : α → ℕ)
    (hf : LogspaceComputes encode (fun a => encodeNat (f a)))
    (hpoly : PolynomialBoundOn encode (fun a => 2^(f a))) :
    LogspaceComputes encode (fun a => encodeNat (2^(f a))) := arithmetic.powTwo encode f hf hpoly

/-- Printed placement bytes are obtained from numeric width and active-position
queries. The arbitrary unused complement is never printed or queried. -/
lemma placement_generated (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    {α : Type} {q k : α → ℕ} (encode : α → Input) (p : ∀ a, Placement (q a) (k a))
    (hq : LogspaceComputes encode (fun a => encodeNat (q a)))
    (hk : LogspaceComputes encode (fun a => encodeNat (k a)))
    (hpoly : PolynomialBoundOn encode k)
    (hpositions : LogspaceComputes (indexedInput encode k)
      (fun r => encodeNat (active (p r.1) r.2).val)) :
    LogspaceComputes encode (fun a => (p a).encode) := by
  have harray := arithmetic.unaryArray encode k (fun a i => (active (p a) i).val) hk hpoly hpositions
  simpa only [unaryArray, Placement.encode, active, List.append_assoc] using
    classical.strings.concat encode _ _ hq harray

lemma word_bit_generated (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    {α : Type} {n : α → ℕ} (encode : α → Input) (word : ∀ a, Basis (n a))
    (i : ∀ a, Fin (n a))
    (hn : LogspaceComputes encode (fun a => encodeNat (n a)))
    (hw : LogspaceComputes encode (fun a => List.ofFn (word a)))
    (hi : LogspaceComputes encode (fun a => encodeNat (i a).val)) :
    LogspaceComputes encode (fun a => [word a (i a)]) := by
  have hrequest : LogspaceComputes encode (fun a =>
      bitQueryInput (⟨n a,word a,i a⟩ : BitQuery)) :=
    classical.strings.concat encode _ _ (classical.strings.concat encode _ _ hn hw) hi
  exact classical.strings.compose encode bitQueryInput
    (fun a => ⟨n a,word a,i a⟩) _ hrequest arithmetic.bitAt

end Paper25.OperationalModel.UniformCompilation
