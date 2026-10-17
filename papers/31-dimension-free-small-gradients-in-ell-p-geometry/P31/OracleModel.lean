import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs

/-! Definition 1.1 as a deterministic exact-transcript protocol. Parameters
are captured when the `Protocol` is constructed. Only `run` calls the oracle;
all transcript-dependent actions, including an arbitrary output, are uncharged. -/
namespace P31.OracleModel

universe u v

/-- Returning a point does not require that it occurred in the transcript. -/
inductive Action (E : Type u) where
  | output : E → Action E
  | query : E → Action E

abbrev Transcript (E : Type u) (G : Type v) := List (E × G)

structure Protocol (E : Type u) (G : Type v) where
  next : Transcript E G → Action E

structure RunResult (E : Type u) (G : Type v) where
  output : Option E
  transcript : Transcript E G
  calls : Nat

/-- A fuel bound is only an execution bound; reaching `output` makes no query.
Each `query` adds one oracle invocation, including at a repeated point. -/
def run {E : Type u} {G : Type v} (P : Protocol E G) (oracle : E → G) :
    Nat → Transcript E G → RunResult E G
  | 0, tr => ⟨none, tr, 0⟩
  | fuel + 1, tr => match P.next tr with
    | .output x => ⟨some x, tr, 0⟩
    | .query x =>
      let r := run P oracle fuel (tr ++ [(x, oracle x)])
      ⟨r.output, r.transcript, r.calls + 1⟩

/-- Exact accounting: calls count newly appended query-response pairs. -/
theorem transcript_length {E : Type u} {G : Type v}
    (P : Protocol E G) (oracle : E → G) (fuel : Nat) (tr : Transcript E G) :
    (run P oracle fuel tr).transcript.length = tr.length + (run P oracle fuel tr).calls := by
  induction fuel generalizing tr with
  | zero => simp [run]
  | succ n ih =>
    simp only [run]
    split
    · simp
    · rename_i x h
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (tr ++ [(x, oracle x)])

/-- A bounded execution invokes the oracle at most once per step. -/
theorem calls_le_fuel {E : Type u} {G : Type v}
    (P : Protocol E G) (oracle : E → G) (fuel : Nat) (tr : Transcript E G) :
    (run P oracle fuel tr).calls ≤ fuel := by
  induction fuel generalizing tr with
  | zero => simp [run]
  | succ n ih =>
    simp only [run]
    split
    · simp
    · exact Nat.add_le_add_right (ih _) 1

/-- The output-only protocol models the zero-query branch exactly. -/
def returnPoint {E : Type u} {G : Type v} (x : E) : Protocol E G :=
  ⟨fun _ => .output x⟩

theorem returnPoint_run {E : Type u} {G : Type v}
    (x : E) (oracle : E → G) (fuel : Nat) (tr : Transcript E G) :
    run (returnPoint x) oracle (fuel + 1) tr = ⟨some x, tr, 0⟩ := rfl

end P31.OracleModel
