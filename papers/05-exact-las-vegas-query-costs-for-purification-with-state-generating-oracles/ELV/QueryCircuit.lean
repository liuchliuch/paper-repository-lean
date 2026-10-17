import ELV.StabilizedGram

/-! Finite fixed query circuits, their actual queried components, and the
cross-instance telescoping identity (2.10). Work gates and query layouts are
independent of the oracle. Query cost is charged along the executed trajectory. -/
noncomputable section
namespace ELV.Query
open ELV.Stabilize

inductive Gate (E N Q : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup N] [InnerProductSpace ℂ N]
    [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] where
  | work (U : E ≃ₗᵢ[ℂ] E)
  | query (layout : E ≃ₗᵢ[ℂ] HilbertPair N Q)

variable {E N Q : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N]
  [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]

/-- The queried component immediately before this gate; work gates contribute zero. -/
def Gate.queried : Gate E N Q → E → Q
  | .work _, _ => 0
  | .query layout, z => (layout z).snd

/-- Controlled oracle, with an untouched non-query branch. -/
def Gate.unitary (O : Q ≃ₗᵢ[ℂ] Q) : Gate E N Q → E ≃ₗᵢ[ℂ] E
  | .work U => U
  | .query layout => layout.trans
      ((pairCongr (LinearIsometryEquiv.refl ℂ N) O).trans layout.symm)

lemma Gate.inner_change (g : Gate E N Q) (Ox Oy : Q ≃ₗᵢ[ℂ] Q) (z w : E) :
    inner ℂ z w - inner ℂ (g.unitary Ox z) (g.unitary Oy w) =
      inner ℂ (g.queried z) (g.queried w) -
        inner ℂ (Ox (g.queried z)) (Oy (g.queried w)) := by
  cases g with
  | work U => simp [Gate.unitary, Gate.queried]
  | query layout =>
    rw [← layout.inner_map_map z w,
      ← layout.inner_map_map ((Gate.query layout).unitary Ox z) ((Gate.query layout).unitary Oy w)]
    simp [Gate.unitary, Gate.queried, WithLp.prod_inner_apply,
      pairCongr, LinearIsometryEquiv.trans_apply]
    have hi : inner ℂ z w = inner ℂ (layout z).fst (layout w).fst +
        inner ℂ (layout z).snd (layout w).snd := (layout.inner_map_map z w).symm
    rw [hi]
    ring

abbrev Circuit (E N Q : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup N] [InnerProductSpace ℂ N]
    [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] := List (Gate E N Q)

/-- Execute a finite circuit in chronological order. -/
def run (O : Q ≃ₗᵢ[ℂ] Q) : Circuit E N Q → E → E
  | [], z => z
  | g :: c, z => run O c (g.unitary O z)

/-- Stack the actual pre-query components, including zero slots for work gates. -/
def trace (O : Q ≃ₗᵢ[ℂ] Q) : (c : Circuit E N Q) → E → Fin c.length → Q
  | [], _, i => Fin.elim0 i
  | g :: c, z, i => @Fin.cons c.length (fun _ => Q) (g.queried z) (trace O c (g.unitary O z)) i

/-- Las Vegas cost (2.5), derived from the trajectory. -/
def cost (O : Q ≃ₗᵢ[ℂ] Q) (c : Circuit E N Q) (z : E) : ℝ :=
  ∑ i : Fin c.length, ‖trace O c z i‖ ^ 2

@[simp] theorem cost_nil (O : Q ≃ₗᵢ[ℂ] Q) (z : E) : cost O ([] : Circuit E N Q) z = 0 := by
  simp [cost]

theorem cost_cons (O : Q ≃ₗᵢ[ℂ] Q) (g : Gate E N Q) (c : Circuit E N Q) (z : E) :
    cost O (g :: c) z = ‖g.queried z‖ ^ 2 + cost O c (g.unitary O z) := by
  simp only [cost,List.length_cons,Fin.sum_univ_succ,trace,Fin.cons_zero,Fin.cons_succ]

/-- The query-time direct sum. -/
def queryVector (O : Q ≃ₗᵢ[ℂ] Q) (c : Circuit E N Q) (z : E) :
    PiLp 2 (fun _ : Fin c.length => Q) := WithLp.toLp 2 (trace O c z)

theorem queryVector_norm_sq (O : Q ≃ₗᵢ[ℂ] Q) (c : Circuit E N Q) (z : E) :
    ‖queryVector O c z‖ ^ 2 = cost O c z := by
  exact PiLp.norm_sq_eq_of_L2 _ _

/-- The finite telescoping identity, before cancelling a returned catalyst. -/
theorem telescope (c : Circuit E N Q) (Ox Oy : Q ≃ₗᵢ[ℂ] Q) (z w : E) :
    inner ℂ z w - inner ℂ (run Ox c z) (run Oy c w) =
      ∑ i : Fin c.length,
        (inner ℂ (trace Ox c z i) (trace Oy c w i) -
          inner ℂ (Ox (trace Ox c z i)) (Oy (trace Oy c w i))) := by
  induction c generalizing z w with
  | nil => simp [run]
  | cons g c ih =>
    simp only [run, List.length_cons, Fin.sum_univ_succ, trace, Fin.cons_zero, Fin.cons_succ]
    rw [← ih]
    rw [← Gate.inner_change]
    ring

section Exact
variable {H L : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L]
variable {X : Type*}

/-- Exact transduction includes an actual circuit and the catalysts which it returns. -/
def Exact (c : Circuit (HilbertPair H L) N Q) (O : X → Q ≃ₗᵢ[ℂ] Q)
    (ξ τ : X → H) (w : X → L) : Prop :=
  ∀ x, run (O x) c (WithLp.toLp 2 (ξ x, w x)) = WithLp.toLp 2 (τ x, w x)

/-- Equation (2.10): the catalyst cancels because the circuit actually returns it. -/
theorem adversary_identity (c : Circuit (HilbertPair H L) N Q)
    (O : X → Q ≃ₗᵢ[ℂ] Q) (ξ τ : X → H) (w : X → L) (hex : Exact c O ξ τ w)
    (x y : X) :
    inner ℂ (ξ x) (ξ y) - inner ℂ (τ x) (τ y) =
      ∑ i : Fin c.length,
        (inner ℂ (trace (O x) c (WithLp.toLp 2 (ξ x, w x)) i)
          (trace (O y) c (WithLp.toLp 2 (ξ y, w y)) i) -
         inner ℂ (O x (trace (O x) c (WithLp.toLp 2 (ξ x, w x)) i))
          (O y (trace (O y) c (WithLp.toLp 2 (ξ y, w y)) i))) := by
  have ht := telescope c (O x) (O y) (WithLp.toLp 2 (ξ x, w x)) (WithLp.toLp 2 (ξ y, w y))
  rw [hex x, hex y] at ht
  simpa [WithLp.prod_inner_apply] using ht

end Exact
end ELV.Query
