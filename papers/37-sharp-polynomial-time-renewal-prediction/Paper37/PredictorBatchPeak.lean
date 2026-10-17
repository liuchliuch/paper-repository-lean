import Paper37.PredictorBatchProgram
import Paper37.IntegerOutputPeak
import Paper37.WordProgramPeak

/-! Actual dynamic peak of the suffix batch, with an invariant on its real
running unreduced rational pair. Query and word-drop syntax are instantiated
by independently proved source program bounds in the final standard module. -/
namespace Paper37.PredictorBatchPeak
open Paper37.BoundedLoop Paper37.PredictorBatchProgram Paper37.WordProgram
open Paper37.IntegerPredictor Paper37.IntegerOutputPeak
open Paper37.IntegerOutput (pairSize pairAdd pairAdd_size pairSum pairSum_binarySize)
set_option maxRecDepth 3000

lemma pairValue_size (p : ℕ×ℕ) : (pairValue p).representationSize≤2*pairSize p+4 := by
  have h1 : p.1.size≤pairSize p := le_max_left _ _
  have h2 : p.2.size≤pairSize p := le_max_right _ _
  simp only [pairValue,Value.representationSize,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

lemma bind_peak_le (ρ : Env) (x : ℕ) (a b : Expr) :
    (Expr.bind x a b).peak ρ≤max (a.peak ρ) (b.peak (Function.update ρ x (a.eval ρ))) := by
  rw [Expr.peak]
  apply max_le
  · rw [Expr.eval]
    exact (representationSize_le_peak b _).trans (le_max_right _ _)
  · exact le_refl _

lemma pairAddProgram_flat : Flat pairAddProgram := by
  unfold pairAddProgram
  apply Flat.array
  intro e he
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at he
  rcases he with rfl|rfl
  all_goals repeat first | exact Flat.lit _ | exact Flat.var _ | apply Flat.get |
    apply Flat.binary .add | apply Flat.binary .mul

lemma pairAddProgram_peak (ρ : Env) (P Q : ℕ)
    (hp : (ρ 53).representationSize≤P) (hq : (ρ 54).representationSize≤Q) :
    pairAddProgram.peak ρ≤128*(P+Q+1) := by
  have hp' := hp.trans (Nat.le_add_right P Q)
  have hq' := hq.trans (Nat.le_add_left Q P)
  have hv : pairAddProgram.varsBound ρ (P+Q) := by
    simp [pairAddProgram,Expr.varsBound,hp',hq']
  apply (flat_peak_le pairAddProgram_flat ρ (P+Q) hv).trans
  simp [pairAddProgram,Expr.flatBudget]
  omega

def suffixIndex : Expr := .sub (.var 51) (.add (.var 52) (.lit 1))

lemma suffixIndex_flat : Flat suffixIndex :=
  Flat.binary .sub _ _ (Flat.var _) (Flat.binary .add _ _ (Flat.var _) (Flat.lit _))

lemma suffixIndex_peak (ρ : Env) (n t : ℕ) (ht : t<n)
    (h51 : ρ 51=.nat n) (h52 : ρ 52=.nat t) : suffixIndex.peak ρ≤32*(n+2) := by
  have hn := Paper37.DP.binarySize_le_self n
  have ht' := Paper37.DP.binarySize_le_self t
  have hv : suffixIndex.varsBound ρ (n+1) := by
    simp only [suffixIndex,Expr.varsBound,h51,h52,Value.representationSize]
    exact ⟨by omega,by omega,trivial⟩
  apply (flat_peak_le suffixIndex_flat ρ (n+1) hv).trans
  simp [suffixIndex,Expr.flatBudget]
  omega

/-- A semantic specification for a finite query syntax term. It is never a
run-time function call or oracle; q remains fixed first-order syntax. -/
def PairQueryCorrect (q : Expr) (N : ℕ) (f : List Bool → ℕ×ℕ) : Prop :=
  ∀ (ρ : Env) (y : List Bool), ρ 0=.nat N → ρ 40=wordValue y → y.length<N →
    q.eval ρ=pairValue (f y)

lemma bodyProgram_pair_eval (q : Expr) (n : ℕ) (f : List Bool → ℕ×ℕ)
    (hq : PairQueryCorrect q (n+1) f) (ρ : Env) (x : List Bool) (hx : x.length=n)
    (t : ℕ) (ht : t<n) (p : ℕ×ℕ) (h0 : ρ 0=.nat (n+1))
    (h50 : ρ 50=wordValue x) (h51 : ρ 51=.nat n) (h52 : ρ 52=.nat t) (h53 : ρ 53=pairValue p) :
    (bodyProgram q).eval ρ=pairValue (pairAdd p (f (x.drop (n-(t+1))))) := by
  let ρ₁:=Function.update ρ 40 (wordValue x)
  let ρ₂:=Function.update ρ₁ 44 (.nat (n-(t+1)))
  let ρ₃:=Function.update ρ₂ 40 (wordValue (x.drop (n-(t+1))))
  have hd := dropProgram_eval ρ₂ x (n-(t+1)) (by simp [ρ₂,ρ₁]) (by simp [ρ₂])
  have hy : (x.drop (n-(t+1))).length<n+1 := by simp only [List.length_drop,hx];omega
  have hquery := hq ρ₃ _ (by simpa [ρ₃,ρ₂,ρ₁] using h0) (by simp [ρ₃]) hy
  simp only [bodyProgram,Expr.eval,h50]
  simp only [Function.update_of_ne (by decide : (51:ℕ)≠40),
    Function.update_of_ne (by decide : (52:ℕ)≠40),h51,h52,Value.natVal]
  change pairAddProgram.eval
    (Function.update (Function.update ρ₂ 40 (dropProgram.eval ρ₂)) 54
      (q.eval (Function.update ρ₂ 40 (dropProgram.eval ρ₂))))=_
  rw [hd]
  change pairAddProgram.eval (Function.update ρ₃ 54 (q.eval ρ₃))=_
  rw [hquery]
  exact pairAddProgram_eval _ _ _ (by simpa [ρ₃,ρ₂,ρ₁] using h53) (by simp)

def QueryPeak (q : Expr) (N Q : ℕ) : Prop := ∀ (ρ : Env) (y : List Bool),
  ρ 0=.nat N → ρ 40=wordValue y → y.length<N → q.peak ρ≤Q

def DropPeak (N D : ℕ) : Prop := ∀ (ρ : Env) (x : List Bool) (t : ℕ),
  ρ 40=wordValue x → ρ 44=.nat t → x.length≤N → t≤N → dropProgram.peak ρ≤D

/-- Every intermediate read, suffix construction, query, and cross-multiplying
pair addition in the actual batch body is bounded along its true state. -/
lemma bodyProgram_peak (q : Expr) (n Q D P : ℕ) (f : List Bool → ℕ×ℕ) (hq : PairQueryCorrect q (n+1) f)
    (hQ : QueryPeak q (n+1) Q) (hD : DropPeak n D)
    (ρ : Env) (x : List Bool) (hx : x.length=n) (t : ℕ) (ht : t<n) (p : ℕ×ℕ)
    (hp : pairSize p≤P) (h0 : ρ 0=.nat (n+1)) (h50 : ρ 50=wordValue x)
    (h51 : ρ 51=.nat n) (h52 : ρ 52=.nat t) (h53 : ρ 53=pairValue p) :
    (bodyProgram q).peak ρ≤1000*(D+Q+P+n+3) := by
  let j:=n-(t+1)
  let y:=x.drop j
  let ρ₁:=Function.update ρ 40 (wordValue x)
  let ρ₂:=Function.update ρ₁ 44 (.nat j)
  let ρ₃:=Function.update ρ₂ 40 (wordValue y)
  let out:=f y
  let ρ₄:=Function.update ρ₃ 54 (pairValue out)
  have hy : y.length<n+1 := by dsimp [y];simp only [List.length_drop,hx];omega
  have hindex : suffixIndex.eval ρ₁=.nat j := by simp [suffixIndex,Expr.eval,ρ₁,h51,h52,j,Value.natVal]
  have hdrop := dropProgram_eval ρ₂ x j (by simp [ρ₂,ρ₁]) (by simp [ρ₂])
  have hquery := hq ρ₃ y (by simpa [ρ₃,ρ₂,ρ₁] using h0) (by simp [ρ₃]) hy
  have hword : (Expr.var 50).peak ρ≤2*n+2 := by
    simpa [Expr.peak,Expr.eval,h50,hx] using Paper37.WordProgram.wordValue_size x
  have hind := suffixIndex_peak ρ₁ n t ht (by simpa [ρ₁] using h51) (by simpa [ρ₁] using h52)
  have hd := hD ρ₂ x j (by simp [ρ₂,ρ₁]) (by simp [ρ₂]) hx.le (by dsimp [j];omega)
  have hqueryPeak := hQ ρ₃ y (by simpa [ρ₃,ρ₂,ρ₁] using h0) (by simp [ρ₃]) hy
  have hpv : (ρ₄ 53).representationSize≤2*P+4 := by
    simp only [ρ₄,ρ₃,ρ₂,ρ₁,Function.update_of_ne (by decide : (53:ℕ)≠54),
      Function.update_of_ne (by decide : (53:ℕ)≠40),Function.update_of_ne (by decide : (53:ℕ)≠44),h53]
    exact (pairValue_size p).trans (by omega)
  have hqv : (ρ₄ 54).representationSize≤Q := by
    simp only [ρ₄,Function.update_self]
    rw [← hquery]
    exact (representationSize_le_peak q ρ₃).trans hqueryPeak
  have hadd := pairAddProgram_peak ρ₄ (2*P+4) Q hpv hqv
  unfold bodyProgram
  apply (bind_peak_le ρ 40 (.var 50) _).trans
  apply max_le (by omega)
  simp only [Expr.eval,h50]
  change (Expr.bind 44 suffixIndex (Expr.bind 40 dropProgram (Expr.bind 54 q pairAddProgram))).peak ρ₁≤_
  apply (bind_peak_le ρ₁ 44 suffixIndex _).trans
  rw [hindex]
  apply max_le (by omega)
  change (Expr.bind 40 dropProgram (Expr.bind 54 q pairAddProgram)).peak ρ₂≤_
  apply (bind_peak_le ρ₂ 40 dropProgram _).trans
  rw [hdrop]
  apply max_le (by omega)
  change (Expr.bind 54 q pairAddProgram).peak ρ₃≤_
  apply (bind_peak_le ρ₃ 54 q pairAddProgram).trans
  rw [hquery]
  change max (q.peak ρ₃) (pairAddProgram.peak ρ₄)≤_
  exact max_le (by omega) (by omega)

lemma coupled_fst {α : Type*} (xs : List α) (step : Value → α → Value)
    (cost : Value → α → ℕ) (v : Value) (p : ℕ) :
    (xs.foldl (fun vp i => (step vp.1 i,max vp.2 (cost vp.1 i))) (v,p)).1=xs.foldl step v := by
  induction xs generalizing v p with
  | nil => rfl
  | cons x xs ih => exact ih (step v x) (max p (cost v x))

def batchFold (q : Expr) : Expr := .fold 52 53 (.var 51) (.array [.lit 0,.lit 1]) (bodyProgram q)

/-- The running pair bound is indexed by the genuine range index. This bounds
every visited accumulator, rather than just the final sum of all fractions. -/
lemma batchFold_peak (q : Expr) (n Q D B : ℕ) (f : List Bool → ℕ×ℕ)
    (hq : PairQueryCorrect q (n+1) f) (hQ : QueryPeak q (n+1) Q) (hD : DropPeak n D)
    (hB : ∀ y : List Bool, y.length<n+1 → pairSize (f y)≤B)
    (ρ : Env) (x : List Bool) (hx : x.length=n)
    (h0 : ρ 0=.nat (n+1)) (h50 : ρ 50=wordValue x) (h51 : ρ 51=.nat n) :
    let P:=n*(B+4)+1
    (batchFold q).peak ρ≤1000*(D+Q+P+n+3) ∧
      ∃ p : ℕ×ℕ, (batchFold q).eval ρ=pairValue p ∧ pairSize p≤P := by
  let P:=n*(B+4)+1
  let F:=1000*(D+Q+P+n+3)
  let I : ℕ → Value → Prop := fun j v => ∃ p : ℕ×ℕ, v=pairValue p ∧ pairSize p≤j*(B+4)+1
  let step : Value → ℕ → Value := fun v j => (bodyProgram q).eval
    (Function.update (Function.update ρ 52 (.nat j)) 53 v)
  let cost : Value → ℕ → ℕ := fun v j => (bodyProgram q).peak
    (Function.update (Function.update ρ 52 (.nat j)) 53 v)
  have hs : ∀j<n,∀v,I j v → I (j+1) (step v j) := by
    intro j hj v hv
    obtain ⟨p,rfl,hp⟩ := hv
    let σ:=Function.update (Function.update ρ 52 (.nat j)) 53 (pairValue p)
    have he := bodyProgram_pair_eval q n f hq σ x hx j hj p
      (by simpa [σ] using h0) (by simpa [σ] using h50) (by simpa [σ] using h51)
      (by simp [σ]) (by simp [σ])
    have hy : (x.drop (n-(j+1))).length<n+1 := by simp only [List.length_drop,hx];omega
    have hb:=hB _ hy
    have ha:=pairAdd_size p (f (x.drop (n-(j+1))))
    refine ⟨pairAdd p (f (x.drop (n-(j+1)))),he,?_⟩
    nlinarith
  have hc : ∀j<n,∀v,I j v → cost v j≤F := by
    intro j hj v hv
    obtain ⟨p,rfl,hp⟩ := hv
    have hmul:=Nat.mul_le_mul_right (B+4) hj.le
    have hpP : pairSize p≤P := by dsimp [P];omega
    exact bodyProgram_peak q n Q D P f hq hQ hD _ x hx j hj p hpP
      (by simpa using h0) (by simpa using h50) (by simpa using h51) (by simp) (by simp)
  have hi : I 0 (pairValue (0,1)) := by
    refine ⟨(0,1),rfl,?_⟩
    simp [pairSize]
  have hh := range_foldl_peak_le n step cost I F hs hc (pairValue (0,1)) hi 0 (by omega)
  obtain ⟨p,hp,hps⟩ := hh.1
  have heval : (batchFold q).eval ρ=pairValue p := by
    rw [batchFold,Expr.eval]
    simp only [Expr.eval,h51,Value.natVal,List.map_cons,List.map_nil]
    change (List.range n).foldl step (pairValue (0,1))=pairValue p
    exact (coupled_fst (List.range n) step cost (pairValue (0,1)) 0).symm.trans hp
  refine ⟨?_,p,heval,hps⟩
  rw [batchFold,Expr.peak]
  apply max_le
  · change ((batchFold q).eval ρ).representationSize≤_
    rw [heval]
    have hrepr := pairValue_size p
    dsimp [P,F] at *
    omega
  · apply max_le
    · have hn := Paper37.DP.binarySize_le_self n
      simp only [Expr.peak,Expr.eval,h51,Value.representationSize]
      omega
    · apply max_le
      · simp [Expr.peak,Expr.eval,Value.representationSize]
        omega
      · simp only [Expr.eval,h51,Value.natVal,List.map_cons,List.map_nil]
        exact hh.2

def batchOutput : Expr := .array [.get (.var 57) (.lit 0),.mul (.get (.var 57) (.lit 1)) (.var 51)]

lemma batchOutput_flat : Flat batchOutput := by
  unfold batchOutput
  apply Flat.array
  intro e he
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at he
  rcases he with rfl|rfl
  all_goals repeat first | exact Flat.lit _ | exact Flat.var _ | apply Flat.get | apply Flat.binary .mul

lemma batchOutput_peak (ρ : Env) (A L : ℕ)
    (ha : (ρ 57).representationSize≤A) (hl : (ρ 51).representationSize≤L) :
    batchOutput.peak ρ≤128*(A+L+1) := by
  have ha':=(ha.trans (Nat.le_add_right A L))
  have hl':=(hl.trans (Nat.le_add_left L A))
  have hv : batchOutput.varsBound ρ (A+L) := by simp [batchOutput,Expr.varsBound,ha',hl']
  apply (flat_peak_le batchOutput_flat ρ (A+L) hv).trans
  simp [batchOutput,Expr.flatBudget]
  omega

/-- Generic finite-query batch peak. Query semantics, query peak, and each
query pair's bit bound are proof specifications about fixed syntax; none is
a primitive run-time oracle. Both standard and adaptive source queries use it. -/
theorem batchProgram_peak (q : Expr) (n Q D B : ℕ) (f : List Bool → ℕ×ℕ)
    (hq : PairQueryCorrect q (n+1) f) (hQ : QueryPeak q (n+1) Q) (hD : DropPeak n D)
    (hB : ∀ y : List Bool, y.length<n+1 → pairSize (f y)≤B)
    (ρ : Env) (x : List Bool) (hx : x.length=n)
    (h0 : ρ 0=.nat (n+1)) (hword : ρ 40=wordValue x) :
    (batchProgram q).peak ρ≤100000*(D+Q+n*(B+4)+n+10) := by
  let P:=n*(B+4)+1
  let ρ₁:=Function.update ρ 50 (wordValue x)
  let ρ₂:=Function.update ρ₁ 51 (.nat n)
  have hh := batchFold_peak q n Q D B f hq hQ hD hB ρ₂ x hx
    (by simpa [ρ₂,ρ₁] using h0) (by simp [ρ₂,ρ₁]) (by simp [ρ₂])
  obtain ⟨p,heval,hps⟩ := hh.2
  let ρ₃:=Function.update ρ₂ 57 (pairValue p)
  have ha : (ρ₃ 57).representationSize≤2*P+4 := by
    simp only [ρ₃,Function.update_self]
    exact (pairValue_size p).trans (by dsimp [P];omega)
  have hl : (ρ₃ 51).representationSize≤n+1 := by
    simp only [ρ₃,ρ₂,Function.update_of_ne (by decide : (51:ℕ)≠57),Function.update_self,Value.representationSize]
    exact Nat.add_le_add_right (Paper37.DP.binarySize_le_self n) 1
  have hout:=batchOutput_peak ρ₃ (2*P+4) (n+1) ha hl
  have hwordPeak : (Expr.var 40).peak ρ≤2*n+2 := by
    simpa [Expr.peak,Expr.eval,hword,hx] using wordValue_size x
  have hlengthPeak : (Expr.length (.var 50)).peak ρ₁≤2*n+3 := by
    apply (length_peak_le _ _ _ ?_).trans (le_refl _)
    simpa [Expr.peak,Expr.eval,ρ₁,hx] using wordValue_size x
  unfold batchProgram
  apply (bind_peak_le ρ 50 (.var 40) _).trans
  apply max_le (by omega)
  simp only [Expr.eval,hword]
  change (Expr.bind 51 (.length (.var 50)) (.bind 57 (batchFold q) batchOutput)).peak ρ₁≤_
  apply (bind_peak_le ρ₁ 51 (.length (.var 50)) _).trans
  apply max_le (by omega)
  simp only [Expr.eval,ρ₁,Function.update_self,wordValue_length,hx]
  change (Expr.bind 57 (batchFold q) batchOutput).peak ρ₂≤_
  apply (bind_peak_le ρ₂ 57 (batchFold q) batchOutput).trans
  rw [heval]
  change max ((batchFold q).peak ρ₂) (batchOutput.peak ρ₃)≤_
  dsimp [P] at hout
  exact max_le (by have h:=hh.1;omega) (by omega)

/-- Closed polynomial bit bound for each standard continuation query pair. -/
lemma standard_queryBitBound_le (H : ℕ) : queryBitBound H≤100*(H+2)^4 := by
  have h1:=Paper37.DP.binarySize_le_self (H+1)
  have h2:=Paper37.DP.binarySize_le_self (2*H)
  have h3:=Paper37.DP.binarySize_le_self H
  have hm:=Nat.mul_le_mul (Nat.div_le_self (H*(H+1)) 2) h3
  have hp:=Nat.mul_le_mul_left (4*H+1) h2
  unfold queryBitBound outputBitBound
  nlinarith [Nat.zero_le (H^3),Nat.zero_le (H^4)]

end Paper37.PredictorBatchPeak
