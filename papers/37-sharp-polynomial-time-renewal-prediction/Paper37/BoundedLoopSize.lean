import Paper37.BoundedLoop

/-! Exact structural representation length and dynamic intermediate-value peak
for the first-order bounded-loop evaluator. Array delimiters and empty values
are charged, so arrays of zero-size naturals do not have zero representation. -/
namespace Paper37.BoundedLoop

/-- Binary natural literals have one terminator. Arrays have opening and closing
delimiters; each element recursively carries its own complete representation. -/
def Value.representationSize : Value → ℕ
  | .nat n => n.size+1
  | .array a => (a.map Value.representationSize).sum+2

/-- Maximum operation-result representation along the actual dynamic execution.
The syntax is fixed: the number of registers and pending subexpressions is a
program-dependent constant. Input storage is charged separately by its literal
encoding length. Every assigned/read value and loop bound occurs among these
operation results; no uninspected infinite environment is charged. -/
def Expr.peak (ρ : Env) (e : Expr) : ℕ :=
  max (e.eval ρ).representationSize (match e with
  | .lit _ | .var _ => 0
  | .add a b | .sub a b | .mul a b | .div a b | .min a b => max (a.peak ρ) (b.peak ρ)
  | .ifLT a b t e => max (a.peak ρ) (max (b.peak ρ)
      (if (a.eval ρ).natVal<(b.eval ρ).natVal then t.peak ρ else e.peak ρ))
  | .array es => (es.map (fun e => e.peak ρ)).foldl max 0
  | .get a i => max (a.peak ρ) (i.peak ρ)
  | .length a => a.peak ρ
  | .bind x a b => max (a.peak ρ) (b.peak (Function.update ρ x (a.eval ρ)))
  | .tabulate x n b => max (n.peak ρ)
      (((List.range (n.eval ρ).natVal).map (fun i => b.peak (Function.update ρ x (.nat i)))).foldl max 0)
  | .fold x s n a b => max (n.peak ρ) (max (a.peak ρ)
      (((List.range (n.eval ρ).natVal).foldl
        (fun vp i => let ρ' := Function.update (Function.update ρ x (.nat i)) s vp.1
          (b.eval ρ',max vp.2 (b.peak ρ'))) (a.eval ρ,0)).2))
  | .foldArray x s a z b => max (a.peak ρ) (max (z.peak ρ)
      (((a.eval ρ).arrayVal.foldl
        (fun vp i => let ρ' := Function.update (Function.update ρ x i) s vp.1
          (b.eval ρ',max vp.2 (b.peak ρ'))) (z.eval ρ,0)).2)))

lemma representationSize_le_peak (e : Expr) (ρ : Env) :
    (e.eval ρ).representationSize ≤ e.peak ρ := by
  cases e <;> rw [Expr.peak] <;> exact Nat.le_max_left _ _

lemma representationSize_pos (v : Value) : 0 < v.representationSize := by
  cases v <;> simp only [Value.representationSize] <;> omega

lemma list_foldl_max_le (xs : List ℕ) (a B : ℕ) (ha : a≤B) (hxs : ∀x∈xs,x≤B) :
    xs.foldl max a≤B := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    apply ih
    · exact max_le ha (hxs x (by simp))
    · intro y hy;exact hxs y (by simp [hy])

/-- A general invariant for the exact dynamic fold peak; the invariant must
hold on the true running accumulator, not on an arbitrary supplied trace. -/
lemma foldl_peak_le {α : Type*} (xs : List α) (step : Value → α → Value)
    (cost : Value → α → ℕ) (I : Value → Prop) (B : ℕ)
    (hstep : ∀ v, I v → ∀ i∈xs, I (step v i))
    (hcost : ∀ v, I v → ∀ i∈xs, cost v i≤B)
    (v : Value) (hv : I v) (p : ℕ) (hp : p≤B) :
    (xs.foldl (fun vp i => (step vp.1 i,max vp.2 (cost vp.1 i))) (v,p)).2≤B := by
  induction xs generalizing v p with
  | nil => exact hp
  | cons i xs ih =>
    apply ih
    · intro u hu j hj;exact hstep u hu j (by simp [hj])
    · intro u hu j hj;exact hcost u hu j (by simp [hj])
    · exact hstep v hv i (by simp)
    · exact max_le hp (hcost v hv i (by simp))

end Paper37.BoundedLoop
