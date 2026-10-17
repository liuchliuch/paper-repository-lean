import Paper29.FinitePolicyCode

noncomputable section
open scoped Classical ENNReal
namespace Paper29.QueryModel

def encodeAlphabetHistory {n : ℕ} {R : Type} (h : List (Fin n × R)) (hlen : h.length ≤ n) : AlphabetHistory n R :=
  ⟨⟨h.length,by omega⟩,fun i => h.get i⟩

theorem encodeAlphabetHistory_toHistory {n : ℕ} {R : Type} (label : R → ℝ)
    (h : List (Fin n × R)) (hlen : h.length ≤ n) :
    (encodeAlphabetHistory h hlen).toHistory label = h.map (fun a => (a.1,label a.2)) := by
  simp [encodeAlphabetHistory,AlphabetHistory.toHistory]

/-- Finite decision-table execution on an actual response alphabet. -/
def executeCode {n r : ℕ} {R : Type} (code : PolicyCode n r R) (b : Fin n → R) :
    ℕ → List (Fin n × R) → Option (RateDistortion.Cube r × List (Fin n × R))
  | 0,_ => none
  | k+1,h => if hlen : h.length ≤ n then
      match code (encodeAlphabetHistory h hlen) with
      | .inl word => some (word,h)
      | .inr (.inl i) => executeCode code b k (h++[(i,b i)])
      | .inr (.inr _) => none
    else none

/-- Relates true exact-real outputs to their finite decoder and trace. -/
def CodeResultMatches {n d r : ℕ} {R : Type} (hrd : r ≤ d) (label : R → ℝ) :
    Option (RateDistortion.Cube r × List (Fin n × R)) →
      Option ((Fin d → ℝ) × History n) → Prop
  | none,none => True
  | some (word,h),some (x,g) =>
      word=(fun j => HardDistribution.decode (x (Fin.castLE hrd j))) ∧
        g=h.map (fun a => (a.1,label a.2))
  | _,_ => False

theorem compilePolicy_execution_matches {Ω R : Type} {n d r : ℕ} (hrd : r ≤ d)
    (label : R → ℝ) (p : Policy Ω n d) (hfresh : Fresh p) (ω : Ω) (b : Fin n → R)
    (k : ℕ) (h : List (Fin n × R)) (hnodup : (h.map Prod.fst).Nodup) :
    CodeResultMatches hrd label
      (executeCode (compilePolicy hrd label p ω) b k h)
      (execute p ω (fun i => label (b i)) k (h.map (fun a => (a.1,label a.2)))) := by
  induction k generalizing h with
  | zero => trivial
  | succ k ih =>
    have hlen : h.length ≤ n := by
      have hh := hnodup.length_le_card
      simpa using hh
    simp only [executeCode,dif_pos hlen,compilePolicy,encodeAlphabetHistory_toHistory]
    cases ha : p ω (h.map (fun a => (a.1,label a.2))) with
    | output x =>
      simp only [ha,codeDecision,execute,CodeResultMatches]
      constructor <;> trivial
    | diverge => simp only [ha,codeDecision,execute,CodeResultMatches]
    | query i =>
      have hi : i ∉ h.map Prod.fst := by
        have hh := hfresh ω (h.map (fun a => (a.1,label a.2))) i ha
        simpa only [List.map_map,Function.comp_def] using hh
      have hn' : ((h++[(i,b i)]).map Prod.fst).Nodup := by
        simpa only [List.map_append,List.map_cons,List.map_nil,List.concat_eq_append] using hnodup.concat hi
      have hh := ih (h++[(i,b i)]) hn'
      simpa only [ha,codeDecision,execute,List.map_append,List.map_cons,List.map_nil] using hh

/-- On a returned run, the finite table has the same decoded answer and query
history. Exact-real outputs need never be placed in the compressed seed. -/
theorem compilePolicy_run_returned {Ω R : Type} {n d r : ℕ} (hrd : r ≤ d)
    (label : R → ℝ) (p : Policy Ω n d) (hfresh : Fresh p) (ω : Ω) (b : Fin n → R)
    (x : Fin d → ℝ) (h : History n) (hrun : run p ω (fun i => label (b i))=some (x,h)) :
    ∃ g : List (Fin n × R), executeCode (compilePolicy hrd label p ω) b (n+1) [] =
      some ((fun j => HardDistribution.decode (x (Fin.castLE hrd j))),g) ∧
        h=g.map (fun a => (a.1,label a.2)) := by
  have hh := compilePolicy_execution_matches hrd label p hfresh ω b (n+1) [] (by simp)
  change CodeResultMatches hrd label _ (run p ω (fun i => label (b i))) at hh
  rw [hrun] at hh
  cases hc : executeCode (compilePolicy hrd label p ω) b (n+1) [] with
  | none => rw [hc] at hh; exact False.elim hh
  | some out =>
    rw [hc] at hh
    rcases out with ⟨word,g⟩
    change word=_ ∧ h=_ at hh
    exact ⟨g,by simpa only [hh.1] using hc,hh.2⟩

/-- Actual distinct-query cost of the finite decision-table execution. -/
def codeQueryCount {n r : ℕ} {R : Type} (code : PolicyCode n r R) (b : Fin n → R) : ℝ≥0∞ :=
  match executeCode code b (n+1) [] with
  | none => ⊤
  | some (_,h) => (h.map Prod.fst).toFinset.card

def codeDecoder {n r : ℕ} {R : Type} (code : PolicyCode n r R) (b : Fin n → R) : RateDistortion.Cube r :=
  match executeCode code b (n+1) [] with
  | none => fun _ => false
  | some (word,_) => word

theorem compilePolicy_queryCount {Ω R : Type} {n d r : ℕ} (hrd : r ≤ d) (label : R → ℝ)
    (p : Policy Ω n d) (hfresh : Fresh p) (ω : Ω) (b : Fin n → R) :
    codeQueryCount (compilePolicy hrd label p ω) b = queryCount p ω (fun i => label (b i)) := by
  have hh := compilePolicy_execution_matches hrd label p hfresh ω b (n+1) [] (by simp)
  change CodeResultMatches hrd label _ (run p ω (fun i => label (b i))) at hh
  unfold codeQueryCount queryCount
  cases hc : executeCode (compilePolicy hrd label p ω) b (n+1) [] with
  | none =>
    rw [hc] at hh
    cases hr : run p ω (fun i => label (b i)) with
    | none => rfl
    | some out => rw [hr] at hh; exact False.elim hh
  | some out =>
    rw [hc] at hh
    cases hr : run p ω (fun i => label (b i)) with
    | none => rw [hr] at hh; exact False.elim hh
    | some out' =>
      rw [hr] at hh
      rcases out with ⟨word,h⟩
      rcases out' with ⟨x,g⟩
      change word=_ ∧ g=_ at hh
      rw [hh.2]
      simp only [List.map_map,Function.comp_def]

theorem compilePolicy_return_decoder {Ω R : Type} {n d r : ℕ} (hrd : r ≤ d) (label : R → ℝ)
    (p : Policy Ω n d) (hfresh : Fresh p) (ω : Ω) (b : Fin n → R)
    (x : Fin d → ℝ) (h : History n) (hrun : run p ω (fun i => label (b i))=some (x,h)) :
    codeDecoder (compilePolicy hrd label p ω) b = (fun j => HardDistribution.decode (x (Fin.castLE hrd j))) := by
  obtain ⟨g,hg,_⟩ := compilePolicy_run_returned hrd label p hfresh ω b x h hrun
  rw [codeDecoder,hg]

end Paper29.QueryModel
