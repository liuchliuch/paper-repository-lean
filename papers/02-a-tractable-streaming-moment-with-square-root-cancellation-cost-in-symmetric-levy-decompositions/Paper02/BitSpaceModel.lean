import Paper02.Streaming
import Paper02.StreamingSpace

/-! # Bit-space one-pass turnstile programs

The model separates persistent accumulators from actual update and decode
microregisters. A mathematical update function earns its implementation only
through `UpdateRefines`; arbitrary finite input/output functions are not free
workspace. Incoming signed binary updates are read by the fixed finite-field
Horner automaton in `StreamingSpace`, whose state is charged below.
-/
set_option synthInstance.maxSize 1024
noncomputable section

namespace Paper02.BitSpaceModel

open SparseRecovery Sampling StreamingSpace

/-- The specified program has finite seed, persistent state, and two actual
microprograms. Correctness, termination and the space bound are separate
properties to be proved of a construction, not algorithm certificate fields. -/
structure Program (d q out : ℕ) where
  Seed : Type
  seedFinite : Fintype Seed
  seedNonempty : Nonempty Seed
  Online : Type
  onlineFinite : Fintype Online
  UpdateWork : Type
  updateFinite : Fintype UpdateWork
  DecodeWork : Type
  decodeFinite : Fintype DecodeWork
  initial : Seed → Online
  next : Seed → Online → Fin d → ZMod q → Online
  updateInit : Seed → Online → Fin d → ZMod q → UpdateWork
  updateStep : Seed → Fin d → ZMod q → UpdateWork → UpdateWork
  updateDone : UpdateWork → Bool
  updateResult : UpdateWork → Online
  decodeInit : Seed → Online → DecodeWork
  decodeStep : Seed → Online → DecodeWork → DecodeWork
  decodeDone : DecodeWork → Bool
  decodeResult : DecodeWork → Fin (out + 1)

attribute [instance] Program.seedFinite Program.seedNonempty Program.onlineFinite
  Program.updateFinite Program.decodeFinite

variable {d q out : ℕ}

/-- Every specified online transition is implemented by the given actual
bounded microprogram on the reduced incoming increment. -/
def UpdateRefines (p : Program d q out) : Prop :=
  ∀ seed state i Δ, ∃ finish,
    Relation.ReflTransGen (fun a b => p.updateStep seed i Δ a = b)
      (p.updateInit seed state i Δ) finish ∧
    p.updateDone finish = true ∧ p.updateResult finish = p.next seed state i Δ

/-- The decoder always halts, including on summaries of vectors outside the
final frequency promise. Its accuracy is required only under that promise. -/
def DecodeTotal (p : Program d q out) : Prop :=
  ∀ seed state, ∃ finish,
    Relation.ReflTransGen (fun a b => p.decodeStep seed state a = b)
      (p.decodeInit seed state) finish ∧ p.decodeDone finish = true

/-- Every mutable register, random seed, output buffer and incoming-update
reader register is counted, including both microprogram control tags.
The current coordinate and reduced increment remain charged while either
microprogram runs. -/
def Fits (p : Program d q out) [NeZero q] (bits : ℕ) : Prop :=
  Fintype.card (Fin (d + 1) × ZMod q × (p.Seed × p.Online ×
    ((Bool × ZMod q) ⊕ p.UpdateWork ⊕ p.DecodeWork))) ≤ 2 ^ bits

/-- The stream is fixed before the finite uniform seed is chosen. -/
def run (p : Program d q out) (seed : p.Seed) (stream : List (Update d)) : p.Online :=
  stream.foldl (fun state u => p.next seed state u.1 (u.2 : ZMod q)) (p.initial seed)

/-- Failure means an actual halting execution returned an inaccurate answer. -/
def Failure (p : Program d q out) (seed : p.Seed) (stream : List (Update d))
    (target : ℝ) (ε : ℝ) : Prop :=
  ∃ finish,
    Relation.ReflTransGen (fun a b => p.decodeStep seed (run p seed stream) a = b)
      (p.decodeInit seed (run p seed stream)) finish ∧ p.decodeDone finish = true ∧
      ε * target < |((p.decodeResult finish).val : ℝ) - target|

def accuracyParameters (d U : ℕ) (ε δ : ℝ) : ℝ :=
  ε⁻¹ + Real.log (2 * (d : ℝ)) + Real.log (2 * (U : ℝ)) + Real.log (1 / δ) + 1

/-- The exact bit-space meaning of the paper's real-even tractability class.
Only the final integer vector is bounded; increments and intermediate vectors
are unrestricted. The polynomial bound is uniform in all four parameters. -/
def IsTEvenPlus (w : ℤ → ℝ) : Prop :=
  (∀ k, 0 ≤ w k) ∧ (∀ k, w (-k) = w k) ∧ w 0 = 0 ∧
  ∃ (C : ℝ) (a : ℕ), 0 ≤ C ∧
    ∀ (d U : ℕ), 1 ≤ d → 1 ≤ U →
    ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 / 3 →
    ∃ (q out bits : ℕ) (_ : Fact q.Prime) (p : Program d q out),
      UpdateRefines p ∧ DecodeTotal p ∧ Fits p bits ∧
      (bits : ℝ) ≤ C * accuracyParameters d U ε δ ^ a ∧
      ∀ stream : List (Update d),
        (∀ i, -(U : ℤ) ≤ finalVector stream i ∧ finalVector stream i ≤ U) →
        (FiniteLaw.uniform p.Seed).prob
          {seed | Failure p seed stream (Streaming.moment w (finalVector stream)) ε} ≤ δ

/-- The finite update-reader theorem applies to every integer increment,
independently of its bit length. -/
theorem arbitrary_increment_reader (q : ℕ) (Δ : ℤ) :
    ∃ sign bits, signedBinaryValue sign bits = Δ ∧
      reduceSignedBits q sign bits = (Δ : ZMod q) :=
  arbitrary_update_reduction q Δ


lemma finiteLaw_ext {Ω : Type*} [Fintype Ω] {μ ν : FiniteLaw Ω}
    (h : μ.mass = ν.mass) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl

/-- Independent uniform copies use exactly the uniform law on the whole finite
seed array, so its cardinality charges the entire random seed. -/
lemma iid_uniform_eq (Ω I : Type*) [Fintype Ω] [Nonempty Ω] [Fintype I] [DecidableEq I] :
    (FiniteLaw.uniform Ω).iid I = FiniteLaw.uniform (I → Ω) := by
  apply finiteLaw_ext
  funext seed
  simp [FiniteLaw.iid, FiniteLaw.uniform, Fintype.card_fun, one_div]

end Paper02.BitSpaceModel
