import Paper37.CachedOperations

/-! Structural operation counters attached to the actual cache builders and
prefix parsing. Value projections are proved equal to the production code. -/
namespace Paper37.CountedCacheBuilders
open Paper37.CachedDP Paper37.Envelope

/-- Parse with explicit branch/age-or-cons charges, one pair per source symbol. -/
def parseMeasured (a : ℕ) : List Bool → List ℕ × ℕ
  | [] => ([],0)
  | false::x => let r := parseMeasured (a+1) x; (r.1,r.2+2)
  | true::x => let r := parseMeasured 0 x; (a::r.1,r.2+2)

lemma parseMeasured_value (a : ℕ) (x : List Bool) : (parseMeasured a x).1 = parseGaps a x := by
  induction x generalizing a with
  | nil => rfl
  | cons b x ih => cases b <;> simp [parseMeasured,parseGaps,ih]

lemma parseMeasured_work (a : ℕ) (x : List Bool) : (parseMeasured a x).2 = 2*x.length := by
  induction x generalizing a with
  | nil => rfl
  | cons b x ih => cases b <;> simp [parseMeasured,ih,Nat.mul_add]

/-- One equality test, optional increment and list-control charge per item. -/
def countMeasured (d : ℕ) : List ℕ → ℕ × ℕ
  | [] => (0,0)
  | e::g => let r := countMeasured d g; ((if d=e then 1 else 0)+r.1,r.2+3)

lemma countMeasured_value (d : ℕ) (g : List ℕ) : (countMeasured d g).1 = g.count d := by
  induction g with
  | nil => rfl
  | cons e g ih =>
    by_cases he : d=e
    · subst e
      simp [countMeasured,ih,Nat.add_comm]
    · simp [countMeasured,ih,he,eq_comm]

lemma countMeasured_work (d : ℕ) (g : List ℕ) : (countMeasured d g).2 = 3*g.length := by
  induction g with
  | nil => rfl
  | cons e g ih => simp [countMeasured,ih,Nat.mul_add]

/-- Cache self-power construction, charging multiplication and loop control. -/
def powerMeasured (c : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1,0)
  | m+1 => let r := powerMeasured c m; (c*r.1,r.2+3)

lemma powerMeasured_value (c m : ℕ) : (powerMeasured c m).1 = linearPower c m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [powerMeasured,linearPower,ih]

lemma powerMeasured_work (c m : ℕ) : (powerMeasured c m).2 = 3*m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [powerMeasured,ih,Nat.mul_add]

/-- The Pascal-row program with a six-primitive upper charge for each updated
cell (two reads, addition, index subtraction, test and write). -/
def pascalMeasured (N : ℕ) : ℕ → Vector ℕ (N+1) × ℕ
  | 0 => (Vector.ofFn (fun b => if b.val=0 then 1 else 0),2*(N+1))
  | k+1 =>
    let r := pascalMeasured N k
    (Vector.ofFn (fun b => r.1[b.val]+if hb : 0<b.val then r.1[b.val-1]'(by omega) else 0),
      r.2+6*(N+1))

lemma pascalMeasured_value (N k : ℕ) : (pascalMeasured N k).1 = pascalRow N k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [pascalMeasured,pascalRow,ih]

lemma pascalMeasured_work (N k : ℕ) :
    (pascalMeasured N k).2 = 2*(N+1)+6*pascalAdds N k := by
  induction k with
  | zero => simp [pascalMeasured,pascalAdds]
  | succ k ih => simp only [pascalMeasured,pascalAdds,ih]; ring

/-- The parsed histogram's actual source scan charges equal the term used in
preprocessingWork, including one stored count per coordinate. -/
def histogramMeasuredWork (N : ℕ) (z : List Bool) : ℕ :=
  ∑ d : Fin (N+1), ((countMeasured d.val ((parseMeasured 0 z).1.map Nat.succ)).2+1)

lemma histogramMeasuredWork_eq (N : ℕ) (z : List Bool) :
    histogramMeasuredWork N z = 3*observedCacheComparisons N z+(N+1) := by
  simp [histogramMeasuredWork,countMeasured_work,parseMeasured_value,observedCacheComparisons]
  ring

def ageMeasured (a : ℕ) : List Bool → ℕ×ℕ
  | [] => (a,0)
  | false::x => let r := ageMeasured (a+1) x; (r.1,r.2+2)
  | true::x => let r := ageMeasured 0 x; (r.1,r.2+2)

lemma ageMeasured_value (a : ℕ) (x : List Bool) : (ageMeasured a x).1 = parseAge a x := by
  induction x generalizing a with
  | nil => rfl
  | cons b x ih => cases b <;> simp [ageMeasured,parseAge,ih]

lemma ageMeasured_work (a : ℕ) (x : List Bool) : (ageMeasured a x).2 = 2*x.length := by
  induction x generalizing a with
  | nil => rfl
  | cons b x ih => cases b <;> simp [ageMeasured,ih,Nat.mul_add]

def succMapMeasured : List ℕ → List ℕ×ℕ
  | [] => ([],0)
  | d::g => let r := succMapMeasured g; ((d+1)::r.1,r.2+2)

lemma succMapMeasured_value (g : List ℕ) : (succMapMeasured g).1 = g.map Nat.succ := by
  induction g with
  | nil => rfl
  | cons d g ih => simp [succMapMeasured,ih]

lemma succMapMeasured_work (g : List ℕ) : (succMapMeasured g).2 = 2*g.length := by
  induction g with
  | nil => rfl
  | cons d g ih => simp [succMapMeasured,ih,Nat.mul_add]

/-- The actual finite prefix traversals performed around the cached core fit
inside its charged linear preprocessing allowance. -/
lemma prefix_traversals_le (z : List Bool) :
    2*(parseMeasured 0 z).2+(ageMeasured 0 z).2+
      (succMapMeasured (parseMeasured 0 z).1).2+(parseGaps 0 z).length ≤ 12*z.length := by
  rw [parseMeasured_work,ageMeasured_work,succMapMeasured_work,parseMeasured_value]
  have hh := Paper37.CachedDP.parseGaps_length_le 0 z
  omega

end Paper37.CountedCacheBuilders
