import Mathlib.Data.Finset.Range
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Basic

/-! Finite adaptive exact-oracle programs. Constructors depend only on known
parameters and observed oracle answers. `bind` performs uncharged internal work;
only `query` incurs a call. This query-tree presentation is a deterministic
transcript protocol in Definition1.1, with arbitrary output points. -/
open scoped BigOperators

namespace P31.QueryProgram
universe u v w z

inductive Program (E : Type u) (G : Type v) (A : Type w) where
  | pure : A → Program E G A
  | query : E → (G → Program E G A) → Program E G A

structure Execution (E : Type u) (A : Type w) where
  value : A
  queries : List E
  calls : Nat
  deriving Repr

namespace Program
variable {E : Type u} {G : Type v} {A : Type w} {B : Type z}

def run : Program E G A → (E → G) → Execution E A
  | .pure a, _ => ⟨a, [], 0⟩
  | .query x next, oracle =>
      let r := run (next (oracle x)) oracle
      ⟨r.value, x :: r.queries, r.calls + 1⟩

def bind : Program E G A → (A → Program E G B) → Program E G B
  | .pure a, k => k a
  | .query x next, k => .query x (fun g => bind (next g) k)

def map (p : Program E G A) (f : A → B) : Program E G B := p.bind (fun a => .pure (f a))

@[simp] theorem run_pure (a : A) (o : E → G) : run (.pure a) o = ⟨a, [], 0⟩ := rfl
@[simp] theorem run_query (x : E) (next : G → Program E G A) (o : E → G) :
    run (.query x next) o = ⟨(run (next (o x)) o).value,
      x :: (run (next (o x)) o).queries, (run (next (o x)) o).calls + 1⟩ := rfl

/-- Query invocation accounting includes repeated points. -/
theorem calls_eq_length (p : Program E G A) (o : E → G) :
    (p.run o).calls = (p.run o).queries.length := by
  induction p with
  | pure a => rfl
  | query x next ih => simp [run, ih]

/-- Exact adaptive composition, including query count and query order. -/
theorem run_bind (p : Program E G A) (k : A → Program E G B) (o : E → G) :
    (p.bind k).run o =
      ⟨((k (p.run o).value).run o).value,
       (p.run o).queries ++ ((k (p.run o).value).run o).queries,
       (p.run o).calls + ((k (p.run o).value).run o).calls⟩ := by
  induction p with
  | pure a => simp [bind, run]
  | query x next ih => simp [bind, run, ih, Nat.add_assoc, Nat.add_comm]

@[simp] theorem value_bind (p : Program E G A) (k : A → Program E G B) (o : E → G) :
    ((p.bind k).run o).value = ((k (p.run o).value).run o).value := by rw [run_bind]
@[simp] theorem calls_bind (p : Program E G A) (k : A → Program E G B) (o : E → G) :
    ((p.bind k).run o).calls = (p.run o).calls + ((k (p.run o).value).run o).calls := by rw [run_bind]
@[simp] theorem queries_bind (p : Program E G A) (k : A → Program E G B) (o : E → G) :
    ((p.bind k).run o).queries = (p.run o).queries ++ ((k (p.run o).value).run o).queries := by rw [run_bind]

/-- Append one query at an arbitrary output, as required by Assumption6.1. -/
def appendOutputQuery (p : Program E G E) : Program E G E :=
  p.bind (fun x => .query x (fun _ => .pure x))

@[simp] theorem appendOutputQuery_value (p : Program E G E) (o : E → G) :
    (p.appendOutputQuery.run o).value = (p.run o).value := by simp [appendOutputQuery]
@[simp] theorem appendOutputQuery_calls (p : Program E G E) (o : E → G) :
    (p.appendOutputQuery.run o).calls = (p.run o).calls + 1 := by simp [appendOutputQuery]
@[simp] theorem appendOutputQuery_queries (p : Program E G E) (o : E → G) :
    (p.appendOutputQuery.run o).queries = (p.run o).queries ++ [(p.run o).value] := by
  simp [appendOutputQuery]

theorem output_mem_appended_queries (p : Program E G E) (o : E → G) :
    (p.appendOutputQuery.run o).value ∈ (p.appendOutputQuery.run o).queries := by simp

/-- Exact one-for-one oracle simulation. `forward` transforms query points and
`reply` computes the simulated answer from the actual response and known data. -/
def simulate {E' : Type*} {G' : Type*} (forward : E' → E) (reply : E' → G → G') :
    Program E' G' A → Program E G A
  | .pure a => .pure a
  | .query x next => .query (forward x) (fun g => simulate forward reply (next (reply x g)))

theorem run_simulate {E' : Type*} {G' : Type*} (forward : E' → E) (reply : E' → G → G')
    (p : Program E' G' A) (o : E → G) :
    (simulate forward reply p).run o =
      ⟨(p.run (fun x => reply x (o (forward x)))).value,
       (p.run (fun x => reply x (o (forward x)))).queries.map forward,
       (p.run (fun x => reply x (o (forward x)))).calls⟩ := by
  induction p with
  | pure a => rfl
  | query x next ih => simp [simulate, run, ih]

@[simp] theorem run_map (p : Program E G A) (f : A → B) (o : E → G) :
    (p.map f).run o = ⟨f (p.run o).value, (p.run o).queries, (p.run o).calls⟩ := by
  simp [map, run_bind]

/-- Generic accumulated history. The next stage sees only the already
computed history; no unknown function or minimizer is an algorithmic input. -/
def accumulate (stage : ℕ → List A → Program E G A) (initial : A) :
    ℕ → Program E G (List A)
  | 0 => .pure [initial]
  | n+1 => (accumulate stage initial n).bind
      (fun history => (stage n history).map (fun next => history ++ [next]))

@[simp] theorem accumulate_zero (stage : ℕ → List A → Program E G A) (initial : A)
    (o : E → G) : (accumulate stage initial 0).run o = ⟨[initial], [], 0⟩ := rfl

/-- Exact history and call recurrence shared by vector and matrix methods. -/
theorem accumulate_succ (stage : ℕ → List A → Program E G A) (initial : A)
    (n : ℕ) (o : E → G) :
    (accumulate stage initial (n+1)).run o =
      let previous := (accumulate stage initial n).run o
      let next := (stage n previous.value).run o
      ⟨previous.value ++ [next.value], previous.queries ++ next.queries,
        previous.calls + next.calls⟩ := by
  simp [accumulate, run_bind]

theorem accumulate_length (stage : ℕ → List A → Program E G A) (initial : A)
    (n : ℕ) (o : E → G) : ((accumulate stage initial n).run o).value.length = n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [accumulate_succ, ih, Nat.add_assoc]

/-- The call count through checkpoint n is the sum of the actually executed
stage calls; each stage is selected from its own observed prefix. -/
theorem accumulate_calls (stage : ℕ → List A → Program E G A) (initial : A)
    (n : ℕ) (o : E → G) :
    ((accumulate stage initial n).run o).calls =
      ∑ k ∈ Finset.range n, ((stage k ((accumulate stage initial k).run o).value).run o).calls := by
  induction n with
  | zero => simp [accumulate]
  | succ n ih => simp [accumulate_succ, ih, Finset.sum_range_succ]

end Program
end P31.QueryProgram
