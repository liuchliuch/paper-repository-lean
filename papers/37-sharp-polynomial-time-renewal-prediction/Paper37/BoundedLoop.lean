import Mathlib.Data.List.Range
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Function.Basic

/-! A finite, first-order bounded-loop integer language. Loop bodies are syntax,
not arbitrary functions. Arrays are finite lists, and every data-dependent
iteration is bounded by an evaluated natural or a finite input array. -/
namespace Paper37.BoundedLoop

inductive Value where
  | nat : ℕ → Value
  | array : List Value → Value
  deriving Inhabited

def Value.natVal : Value → ℕ
  | .nat n => n
  | .array _ => 0

def Value.arrayVal : Value → List Value
  | .nat _ => []
  | .array a => a

abbrev Env := ℕ → Value

inductive Expr where
  | lit : ℕ → Expr
  | var : ℕ → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | div : Expr → Expr → Expr
  | min : Expr → Expr → Expr
  | ifLT : Expr → Expr → Expr → Expr → Expr
  | array : List Expr → Expr
  | get : Expr → Expr → Expr
  | length : Expr → Expr
  | bind : ℕ → Expr → Expr → Expr
  | tabulate : ℕ → Expr → Expr → Expr
  | fold : ℕ → ℕ → Expr → Expr → Expr → Expr
  | foldArray : ℕ → ℕ → Expr → Expr → Expr → Expr
  deriving Inhabited

def Expr.eval (ρ : Env) : Expr → Value
  | .lit n => .nat n
  | .var x => ρ x
  | .add a b => .nat ((a.eval ρ).natVal+(b.eval ρ).natVal)
  | .sub a b => .nat ((a.eval ρ).natVal-(b.eval ρ).natVal)
  | .mul a b => .nat ((a.eval ρ).natVal*(b.eval ρ).natVal)
  | .div a b => .nat ((a.eval ρ).natVal/(b.eval ρ).natVal)
  | .min a b => .nat (Nat.min (a.eval ρ).natVal (b.eval ρ).natVal)
  | .ifLT a b t e => if (a.eval ρ).natVal<(b.eval ρ).natVal then t.eval ρ else e.eval ρ
  | .array es => .array (es.map (fun e => e.eval ρ))
  | .get a i => (a.eval ρ).arrayVal[(i.eval ρ).natVal]?.getD (.nat 0)
  | .length a => .nat (a.eval ρ).arrayVal.length
  | .bind x a b => b.eval (Function.update ρ x (a.eval ρ))
  | .tabulate x n b => .array ((List.range (n.eval ρ).natVal).map
      (fun i => b.eval (Function.update ρ x (.nat i))))
  | .fold x s n a b => ((List.range (n.eval ρ).natVal).foldl
      (fun v i => b.eval (Function.update (Function.update ρ x (.nat i)) s v)) (a.eval ρ))
  | .foldArray x s a z b => ((a.eval ρ).arrayVal.foldl
      (fun v i => b.eval (Function.update (Function.update ρ x i) s v)) (z.eval ρ))

/-- The charge follows the same evaluator. Arithmetic, comparison, array
read/write, variable access and loop control are explicit unit RAM operations.
The generic machine simulation must additionally account for representation
and bit costs; this language does not assume a unit-cost bit machine. -/
def Expr.work (ρ : Env) : Expr → ℕ
  | .lit _ | .var _ => 1
  | .add a b | .sub a b | .mul a b | .div a b | .min a b => a.work ρ+b.work ρ+1
  | .ifLT a b t e => a.work ρ+b.work ρ+1+
      (if (a.eval ρ).natVal<(b.eval ρ).natVal then t.work ρ else e.work ρ)
  | .array es => (es.map (fun e => e.work ρ+1)).sum+1
  | .get a i => a.work ρ+i.work ρ+1
  | .length a => a.work ρ+1
  | .bind x a b => a.work ρ+1+b.work (Function.update ρ x (a.eval ρ))
  | .tabulate x n b => n.work ρ+1+((List.range (n.eval ρ).natVal).map
      (fun i => b.work (Function.update ρ x (.nat i))+3)).sum
  | .fold x s n a b => n.work ρ+a.work ρ+1+
      (((List.range (n.eval ρ).natVal).foldl
        (fun vw i => let ρ' := Function.update (Function.update ρ x (.nat i)) s vw.1
          (b.eval ρ',vw.2+b.work ρ'+4)) (a.eval ρ,0)).2)
  | .foldArray x s a z b => a.work ρ+z.work ρ+1+
      (((a.eval ρ).arrayVal.foldl
        (fun vw i => let ρ' := Function.update (Function.update ρ x i) s vw.1
          (b.eval ρ',vw.2+b.work ρ'+4)) (z.eval ρ,0)).2)

/-- Coupled execution exposes the actual output together with the charge of
that very syntax term. There is no freely supplied cost annotation. -/
def Expr.execute (ρ : Env) (e : Expr) : Value×ℕ := (e.eval ρ,e.work ρ)

def Value.payload : Value → ℕ
  | .nat n => n.size
  | .array a => (a.map Value.payload).sum

/-- A universal compiler theorem for this language can quantify over this
predicate. It must realize `Expr.eval` on encoded input environments and bound
machine execution using the evaluator's own charge and intermediate payloads.
No predictor-specific computability premise occurs here. -/
def ClosedOn (e : Expr) (inputs : List ℕ) : Prop :=
  ∀ρ σ, (∀x∈inputs,ρ x=σ x) → e.eval ρ=e.eval σ

end Paper37.BoundedLoop
