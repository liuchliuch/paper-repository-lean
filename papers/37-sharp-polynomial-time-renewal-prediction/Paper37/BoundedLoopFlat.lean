import Paper37.BoundedLoopSize
import Paper37.IntegerOutput

/-! Compositional bounds for actual intermediate values of loop-free integer
and array expressions. These are applied to the fixed summand syntax inside
the bounded loops, with genuine invariants on their running accumulators. -/
namespace Paper37.BoundedLoop
open Paper37.IntegerOutput

lemma list_member_size_le (xs : List Value) (v : Value) (hv : v∈xs) :
    v.representationSize≤(xs.map Value.representationSize).sum := by
  induction xs with
  | nil => simp at hv
  | cons x xs ih =>
    simp only [List.mem_cons] at hv
    simp only [List.map_cons,List.sum_cons]
    rcases hv with rfl|hv
    · omega
    · have hh := ih hv;omega

lemma list_length_le_size (xs : List Value) : xs.length≤(xs.map Value.representationSize).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := representationSize_pos x
    simp only [List.length_cons,List.map_cons,List.sum_cons]
    omega

lemma natVal_size_le (v : Value) : v.natVal.size≤v.representationSize := by
  cases v <;> simp [Value.natVal,Value.representationSize]

lemma get_size_le (v : Value) (i : ℕ) :
    (v.arrayVal[i]?.getD (.nat 0)).representationSize≤v.representationSize+1 := by
  cases v with
  | nat a => simp [Value.arrayVal,Value.representationSize]
  | array xs =>
    simp only [Value.arrayVal,Value.representationSize]
    cases hget : xs[i]? with
    | none => simp [Value.representationSize]
    | some x =>
      have hm : x∈xs := List.mem_of_getElem? hget
      have hh := list_member_size_le xs x hm
      simpa only [Option.getD_some] using (show x.representationSize≤(xs.map Value.representationSize).sum+2+1 by omega)

lemma length_size_le (v : Value) :
    (Value.nat v.arrayVal.length).representationSize≤v.representationSize+1 := by
  cases v with
  | nat a => simp [Value.arrayVal,Value.representationSize]
  | array xs =>
    have hh := list_length_le_size xs
    have hs := Paper37.DP.binarySize_le_self xs.length
    simp only [Value.arrayVal,Value.representationSize]
    omega

inductive Op where | add | sub | mul | div | min

def Op.expr : Op → Expr → Expr → Expr
  | .add => Expr.add
  | .sub => Expr.sub
  | .mul => Expr.mul
  | .div => Expr.div
  | .min => Expr.min

lemma binary_peak_le (op : Op) (a b : Expr) (ρ : Env) (A B : ℕ)
    (ha : a.peak ρ≤A) (hb : b.peak ρ≤B) :
    (op.expr a b).peak ρ≤2*(A+B+2) := by
  have hra := (representationSize_le_peak a ρ).trans ha
  have hrb := (representationSize_le_peak b ρ).trans hb
  have hsa := (natVal_size_le (a.eval ρ)).trans hra
  have hsb := (natVal_size_le (b.eval ρ)).trans hrb
  cases op <;> simp only [Op.expr,Expr.peak,Expr.eval,Value.representationSize]
  · have hh := size_add_le (a.eval ρ).natVal (b.eval ρ).natVal
    apply max_le _ (max_le (by omega) (by omega))
    omega
  · have hh := Nat.size_le_size (Nat.sub_le (a.eval ρ).natVal (b.eval ρ).natVal)
    apply max_le _ (max_le (by omega) (by omega))
    omega
  · have hh := size_mul_le (a.eval ρ).natVal (b.eval ρ).natVal
    apply max_le _ (max_le (by omega) (by omega))
    omega
  · have hh := Nat.size_le_size (Nat.div_le_self (a.eval ρ).natVal (b.eval ρ).natVal)
    apply max_le _ (max_le (by omega) (by omega))
    omega
  · have hh := Nat.size_le_size (min_le_left (a.eval ρ).natVal (b.eval ρ).natVal)
    change (Nat.min (a.eval ρ).natVal (b.eval ρ).natVal).size≤(a.eval ρ).natVal.size at hh
    apply max_le _ (max_le (by omega) (by omega))
    omega

lemma get_peak_le (a i : Expr) (ρ : Env) (A I : ℕ)
    (ha : a.peak ρ≤A) (hi : i.peak ρ≤I) : (Expr.get a i).peak ρ≤A+I+1 := by
  have hh := get_size_le (a.eval ρ) (i.eval ρ).natVal
  have hr := (representationSize_le_peak a ρ).trans ha
  simp only [Expr.peak,Expr.eval]
  exact max_le (by omega) (max_le (by omega) (by omega))

lemma length_peak_le (a : Expr) (ρ : Env) (A : ℕ) (ha : a.peak ρ≤A) :
    (Expr.length a).peak ρ≤A+1 := by
  have hh := length_size_le (a.eval ρ)
  have hr := (representationSize_le_peak a ρ).trans ha
  simp only [Expr.peak,Expr.eval]
  exact max_le (by omega) (by omega)

lemma if_peak_le (a b t e : Expr) (ρ : Env) (A B T E : ℕ)
    (ha : a.peak ρ≤A) (hb : b.peak ρ≤B) (ht : t.peak ρ≤T) (he : e.peak ρ≤E) :
    (Expr.ifLT a b t e).peak ρ≤max A (max B (max T E)) := by
  have hrt := (representationSize_le_peak t ρ).trans ht
  have hre := (representationSize_le_peak e ρ).trans he
  simp only [Expr.peak,Expr.eval]
  split_ifs <;> simp_all only [max_le_iff] <;> omega

lemma list_sum_compare {α : Type*} (xs : List α) (f g : α → ℕ)
    (h : ∀x∈xs,f x≤g x) : (xs.map f).sum≤(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (by intro y hy; exact h y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons]
    omega

lemma list_member_le_sum {α : Type*} (xs : List α) (f : α → ℕ) (x : α) (hx : x∈xs) :
    f x≤(xs.map f).sum := by
  induction xs with
  | nil => simp at hx
  | cons y xs ih =>
    simp only [List.mem_cons] at hx
    simp only [List.map_cons,List.sum_cons]
    rcases hx with rfl|hx
    · omega
    · have hh := ih hx;omega

lemma array_peak_le (es : List Expr) (ρ : Env) (f : Expr → ℕ)
    (h : ∀e∈es,e.peak ρ≤f e) :
    (Expr.array es).peak ρ≤(es.map f).sum+2 := by
  rw [Expr.peak,Expr.eval,Value.representationSize]
  apply max_le
  · rw [List.map_map]
    have hh := list_sum_compare es (fun e => (e.eval ρ).representationSize) f
      (by intro e he; exact (representationSize_le_peak e ρ).trans (h e he))
    exact Nat.add_le_add_right hh 2
  · apply list_foldl_max_le _ _ _ (by omega)
    intro p hp
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
    exact (h e he).trans ((list_member_le_sum es f e he).trans (by omega))

/-- Only variable occurrences of this finite expression are constrained.
Unrelated slots in an enclosing lexical environment remain arbitrary. -/
def Expr.varsBound (ρ : Env) (B : ℕ) : Expr → Prop
  | .lit _ => True
  | .var x => (ρ x).representationSize≤B
  | .add a b | .sub a b | .mul a b | .div a b | .min a b | .get a b =>
      a.varsBound ρ B ∧ b.varsBound ρ B
  | .ifLT a b t e => a.varsBound ρ B ∧ b.varsBound ρ B ∧ t.varsBound ρ B ∧ e.varsBound ρ B
  | .array es => ∀e∈es,e.varsBound ρ B
  | .length a => a.varsBound ρ B
  | .bind _ _ _ | .tabulate _ _ _ | .fold _ _ _ _ _ | .foldArray _ _ _ _ _ => False

def Expr.flatBudget (B : ℕ) : Expr → ℕ
  | .lit n => n.size+1
  | .var _ => B
  | .add a b | .sub a b | .mul a b | .div a b | .min a b => 2*(a.flatBudget B+b.flatBudget B+2)
  | .get a i => a.flatBudget B+i.flatBudget B+1
  | .length a => a.flatBudget B+1
  | .ifLT a b t e => max (a.flatBudget B) (max (b.flatBudget B) (max (t.flatBudget B) (e.flatBudget B)))
  | .array es => (es.map (fun e => e.flatBudget B)).sum+2
  | .bind _ _ _ | .tabulate _ _ _ | .fold _ _ _ _ _ | .foldArray _ _ _ _ _ => 0

inductive Flat : Expr → Prop
  | lit (n : ℕ) : Flat (.lit n)
  | var (x : ℕ) : Flat (.var x)
  | binary (op : Op) (a b : Expr) (ha : Flat a) (hb : Flat b) : Flat (op.expr a b)
  | get (a i : Expr) (ha : Flat a) (hi : Flat i) : Flat (.get a i)
  | length (a : Expr) (ha : Flat a) : Flat (.length a)
  | ifLT (a b t e : Expr) (ha : Flat a) (hb : Flat b) (ht : Flat t) (he : Flat e) : Flat (.ifLT a b t e)
  | array (es : List Expr) (h : ∀e∈es,Flat e) : Flat (.array es)

/-- The budget is calculated from syntax. It is a constant affine expression
in the bound on the finitely many variable values read by the expression. -/
theorem flat_peak_le {e : Expr} (he : Flat e) (ρ : Env) (B : ℕ)
    (hv : e.varsBound ρ B) : e.peak ρ≤e.flatBudget B := by
  induction he with
  | lit n => simp [Expr.peak,Expr.eval,Expr.flatBudget,Value.representationSize]
  | var x => simpa [Expr.peak,Expr.eval,Expr.flatBudget,Expr.varsBound] using hv
  | binary op a b ha hb iha ihb =>
    have hv' : a.varsBound ρ B ∧ b.varsBound ρ B := by
      cases op <;> simpa [Op.expr,Expr.varsBound] using hv
    have hh := binary_peak_le op a b ρ _ _ (iha hv'.1) (ihb hv'.2)
    cases op <;> simpa [Op.expr,Expr.flatBudget] using hh
  | get a i ha hi iha ihi =>
    have hv' : a.varsBound ρ B ∧ i.varsBound ρ B := by simpa [Expr.varsBound] using hv
    simpa [Expr.flatBudget] using get_peak_le a i ρ _ _ (iha hv'.1) (ihi hv'.2)
  | length a ha iha =>
    have hv' : a.varsBound ρ B := by simpa [Expr.varsBound] using hv
    simpa [Expr.flatBudget] using length_peak_le a ρ _ (iha hv')
  | ifLT a b t e ha hb ht he iha ihb iht ihe =>
    have hv' : a.varsBound ρ B ∧ b.varsBound ρ B ∧ t.varsBound ρ B ∧ e.varsBound ρ B := by
      simpa [Expr.varsBound] using hv
    simpa [Expr.flatBudget] using if_peak_le a b t e ρ _ _ _ _
      (iha hv'.1) (ihb hv'.2.1) (iht hv'.2.2.1) (ihe hv'.2.2.2)
  | array es hs ih =>
    have hv' : ∀e∈es,e.varsBound ρ B := by simpa [Expr.varsBound] using hv
    simpa [Expr.flatBudget] using array_peak_le es ρ (fun e => e.flatBudget B)
      (by intro e he;exact ih e he (hv' e he))

end Paper37.BoundedLoop
