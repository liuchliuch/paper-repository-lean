import Paper19.OrbitSyntax

namespace Paper19.Infinitary
open Paper19

/-- Finite recursive notation for the infinitary syntax used in this paper.
The rank instruction is a well-founded recursive scheme, with a total
computable relation as its program and an accessibility proof ensuring that
its expansion is well-founded. It is expanded into actual finite-language
syntax, never interpreted as an extra atomic predicate. -/
inductive EffectiveSyntax where
  | top : EffectiveSyntax
  | eq : Term → Term → EffectiveSyntax
  | index : Term → EffectiveSyntax
  | rel : Term → Term → Term → EffectiveSyntax
  | neg : EffectiveSyntax → EffectiveSyntax
  | and : EffectiveSyntax → EffectiveSyntax → EffectiveSyntax
  | ex : ℕ → EffectiveSyntax → EffectiveSyntax
  | finiteAll : (n : ℕ) → (Fin n → EffectiveSyntax) → EffectiveSyntax
  | rank : RecursiveOrdinal (Option Node) → ℕ → EffectiveSyntax

noncomputable def EffectiveSyntax.expand : EffectiveSyntax → Formula
  | .top => .top
  | .eq a b => .eq a b
  | .index a => .index a
  | .rel a b c => .rel a b c
  | .neg a => .neg a.expand
  | .and a b => .and a.expand b.expand
  | .ex v a => .ex v a.expand
  | .finiteAll n f => .all (fun i => if hi : i < n then (f ⟨i, hi⟩).expand else .top)
  | .rank a v => by
    letI : DecidableRel a.rel := fun x y => a.recursive.choose (x, y)
    exact rankFormula a.rel a.root a.accessible v

/-- Explicitly presented computable infinitary formulas, with the recursive
rank schema expanded as in rankFormula_eq. This grammar has no arbitrary
countable conjunction constructor. -/
def ComputablyPresented (φ : Formula) : Prop := ∃ c : EffectiveSyntax, c.expand = φ

def rootCode (tag : Bool) (N v : ℕ) : EffectiveSyntax :=
  if tag then .rel (Term.numeral (encIndex 0 {[]})) .named (Term.lower N 0 (.var v))
  else .eq (Term.lower N 0 (.var v)) .named

def coordinateCode {T : Tree} (N v i : ℕ) (a : Carrier T) : EffectiveSyntax :=
  match a.val with
  | .idx k => .eq (.var i) (Term.numeral k)
  | .vec n F => .rel (Term.numeral (encIndex n F)) (Term.lower N n (.var v)) (.var i)

def orbitCode {T : Tree} (hT : ComputablePred T.mem) (tag : Bool)
    {m : ℕ} (N : ℕ) (a : Fin m → Carrier T) : EffectiveSyntax :=
  .ex m (.and (.neg (.index (.var m)))
    (.and (.eq (.level (.var m)) (Term.numeral N))
      (.and (.rank (levelOrdinal T hT N) m)
        (.and (rootCode tag N m) (.finiteAll m (fun i => coordinateCode N m i (a i)))))))

theorem rootCode_expand (tag : Bool) (N v : ℕ) :
    (rootCode tag N v).expand = rootClause tag N v := by
  cases tag <;> rfl

theorem coordinateCode_expand {T : Tree} (N v i : ℕ) (a : Carrier T) :
    (coordinateCode N v i a).expand = coordinateClause N v i a := by
  cases h : a.val <;> simp [coordinateCode, coordinateClause, h, EffectiveSyntax.expand]

theorem orbitCode_expand {T : Tree} (hT : ComputablePred T.mem) (tag : Bool)
    {m : ℕ} (N : ℕ) (a : Fin m → Carrier T) :
    (orbitCode hT tag N a).expand = orbitFormula hT tag N a := by
  simp only [orbitCode, EffectiveSyntax.expand, rootCode_expand, coordinateCode_expand]
  rfl

theorem orbitFormula_computablyPresented {T : Tree} (hT : ComputablePred T.mem)
    (tag : Bool) {m : ℕ} (N : ℕ) (a : Fin m → Carrier T) :
    ComputablyPresented (orbitFormula hT tag N a) :=
  ⟨orbitCode hT tag N a, orbitCode_expand hT tag N a⟩

/-- Every finite tuple orbit in either structure has an explicit recursive
infinitary formula. The notation and its complexity are chosen separately
for each tuple, in accordance with the source's nonuniform convention. -/
theorem all_tuple_orbits {T : Tree} (hT : ComputablePred T.mem) (tag : Bool)
    (m : ℕ) (a : Fin m → Carrier T) :
    ∃ φ : Formula, ComputablyPresented φ ∧ ∀ b : Fin m → Carrier T,
      φ.Realize tag (tupleEnv b) ↔ ActualTupleOrbit T tag a b := by
  let N := Finset.univ.sup (fun i : Fin m => vectorLevel (a i))
  have hN : ∀ i, vectorLevel (a i) ≤ N := fun i => Finset.le_sup (f := fun i : Fin m => vectorLevel (a i)) (Finset.mem_univ i)
  exact ⟨orbitFormula hT tag N a, orbitFormula_computablyPresented hT tag N a,
    fun b => (orbitFormula_realize hT tag a b hN).trans
      (actual_tuple_orbit_formula tag a b hN).symm⟩

end Paper19.Infinitary
