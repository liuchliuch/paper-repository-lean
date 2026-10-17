import SemidegreeExt.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
open Filter
namespace SemidegreeExt

/-- Equation (1.3): minimum over all feasible loopless digraphs. -/
noncomputable def qMin (n d : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ G : Digraph (Fin n), Loopless G ∧ (∀ v, d ≤ outDeg G v) ∧ q G = k}

/-- Equation (1.6), extended to all natural orders; results use the feasible tail. -/
noncomputable def h (n : ℕ) (α : ℝ) : ℝ := (qMin n (Nat.ceil (α*n)) : ℝ)/n

/-- The original liminf definition in Equation (1.6). -/
noncomputable def hAlpha (α : ℝ) : ℝ := Filter.liminf (fun n : ℕ => h n α) atTop

/-- Weak directed degeneracy in the strict-inequality convention of Section 4. -/
def WeaklyDegenerate {V : Type*} [Fintype V] (G : Digraph V) (k : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty → ∃ v ∈ S, outDegOn G S v < k ∨ inDegOn G S v < k
end SemidegreeExt
