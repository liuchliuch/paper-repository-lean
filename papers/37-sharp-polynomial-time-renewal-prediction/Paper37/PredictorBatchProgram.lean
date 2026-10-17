import Paper37.WordProgram
import Paper37.IntegerPredictor

/-! A uniform first-order suffix batch and unreduced integer pair summation.
The query is a finite syntax term, substituted once at compile time. -/
namespace Paper37.PredictorBatchProgram
open Paper37.BoundedLoop Paper37.WordProgram Paper37.IntegerPredictor
open Paper37.IntegerOutput (pairAdd pairSum)
set_option linter.unusedSimpArgs false
private abbrev v := Expr.var
private abbrev n := Expr.lit

def pairAddProgram : Expr := .array
  [.add (.mul (.get (v 53) (n 0)) (.get (v 54) (n 1)))
    (.mul (.get (v 54) (n 0)) (.get (v 53) (n 1))),
   .mul (.get (v 53) (n 1)) (.get (v 54) (n 1))]

lemma pairAddProgram_eval (ρ : Env) (p q : ℕ×ℕ)
    (hp : ρ 53=pairValue p) (hq : ρ 54=pairValue q) :
    pairAddProgram.eval ρ=pairValue (pairAdd p q) := by
  simp [pairAddProgram,Expr.eval,hp,hq,pairValue,pairAdd,Value.arrayVal,Value.natVal]

lemma pairAdd_assoc (a b c : ℕ×ℕ) : pairAdd (pairAdd a b) c=pairAdd a (pairAdd b c) := by
  apply Prod.ext <;> simp [pairAdd] <;> ring

lemma pairAdd_zero (a : ℕ×ℕ) : pairAdd (0,1) a=a := by
  apply Prod.ext <;> simp [pairAdd]

lemma foldl_pairAdd (xs : List (ℕ×ℕ)) (a : ℕ×ℕ) :
    xs.foldl pairAdd a=pairAdd a (pairSum xs) := by
  induction xs generalizing a with
  | nil => apply Prod.ext <;> simp [pairSum,pairAdd]
  | cons b xs ih => rw [List.foldl_cons,ih,pairSum,pairAdd_assoc]

/-- 50=full input,51=length,52=suffix index,53=accumulator.
The query reads its suffix through word40. Every suffix is constructed by
`dropProgram`; 54 holds the returned integer pair. -/
def bodyProgram (query : Expr) : Expr := .bind 40 (v 50)
  (.bind 44 (.sub (v 51) (.add (v 52) (n 1)))
    (.bind 40 dropProgram (.bind 54 query pairAddProgram)))

def batchProgram (query : Expr) : Expr := .bind 50 (v 40)
  (.bind 51 (.length (v 50))
    (.bind 57 (.fold 52 53 (v 51) (.array [n 0,n 1]) (bodyProgram query))
      (.array [.get (v 57) (n 0),.mul (.get (v 57) (n 1)) (v 51)])))

/-- The premise concerns a finite syntax term's independently established
semantics, not a run-time function or oracle instruction. The final concrete
query is substituted in `IntegerPredictorProgram`. -/
def QueryCorrect (query : Expr) (N : ℕ) : Prop :=
  ∀ (ρ : Env) (y : List Bool), ρ 0=.nat N → ρ 40=wordValue y → y.length<N →
    query.eval ρ=pairValue (conditionalPair N y)

lemma bodyProgram_eval (query : Expr) (n : ℕ) (hq : QueryCorrect query (n+1))
    (ρ : Env) (x : List Bool) (hx : x.length=n) (t : ℕ) (ht : t<n) (p : ℕ×ℕ)
    (hN : ρ 0=.nat (n+1)) (h50 : ρ 50=wordValue x)
    (h51 : ρ 51=.nat n) (h52 : ρ 52=.nat t) (h53 : ρ 53=pairValue p) :
    (bodyProgram query).eval ρ=
      pairValue (pairAdd p (conditionalPair (n+1) (x.drop (n-(t+1))))) := by
  let ρ₁ := Function.update ρ 40 (wordValue x)
  let ρ₂ := Function.update ρ₁ 44 (.nat (n-(t+1)))
  have hdrop := dropProgram_eval ρ₂ x (n-(t+1)) (by simp [ρ₂,ρ₁]) (by simp [ρ₂])
  let ρ₃ := Function.update ρ₂ 40 (wordValue (x.drop (n-(t+1))))
  have hy : (x.drop (n-(t+1))).length<n+1 := by simp only [List.length_drop,hx]; omega
  have hquery := hq ρ₃ (x.drop (n-(t+1))) (by simpa [ρ₃,ρ₂,ρ₁] using hN)
    (by simp [ρ₃]) hy
  change (bodyProgram query).eval ρ=_
  simp only [bodyProgram,Expr.eval,h50]
  simp only [Function.update_of_ne (by omega : (51:ℕ)≠40),
    Function.update_of_ne (by omega : (52:ℕ)≠40),h51,h52,Value.natVal]
  change pairAddProgram.eval
    (Function.update (Function.update ρ₂ 40 (dropProgram.eval ρ₂)) 54
      (query.eval (Function.update ρ₂ 40 (dropProgram.eval ρ₂))))=_
  rw [hdrop]
  change pairAddProgram.eval (Function.update ρ₃ 54 (query.eval ρ₃))=_
  rw [hquery]
  apply pairAddProgram_eval
  · simpa [ρ₃,ρ₂,ρ₁] using h53
  · simp

lemma fold_bodyProgram (query : Expr) (n : ℕ) (hq : QueryCorrect query (n+1))
    (ρ : Env) (x : List Bool) (hx : x.length=n) (is : List ℕ)
    (his : ∀t∈is,t<n) (p : ℕ×ℕ)
    (hN : ρ 0=.nat (n+1)) (h50 : ρ 50=wordValue x) (h51 : ρ 51=.nat n) :
    is.foldl (fun val t => (bodyProgram query).eval
      (Function.update (Function.update ρ 52 (.nat t)) 53 val)) (pairValue p)=
      pairValue ((is.map fun t => conditionalPair (n+1) (x.drop (n-(t+1)))).foldl pairAdd p) := by
  induction is generalizing p with
  | nil => rfl
  | cons t is ih =>
    simp only [List.foldl_cons,List.map_cons]
    rw [bodyProgram_eval query n hq _ x hx t (his t (by simp)) p
      (by simpa using hN) (by simpa using h50) (by simpa using h51) (by simp) (by simp)]
    exact ih (fun j hj => his j (by simp [hj])) _

lemma suffixPairs_eq_range (n : ℕ) (x : List Bool) :
    (List.range n).map (fun t => conditionalPair (n+1) (x.drop (n-(t+1))))=suffixPairs n x := by
  apply List.ext_getElem (by simp [suffixPairs])
  intro i hi hj
  simp [suffixPairs]

/-- The whole suffix-average loop, including all pair additions and division
by the sample size, computes exactly the source integer predictor pair. -/
theorem batchProgram_eval (query : Expr) (n : ℕ) (hq : QueryCorrect query (n+1))
    (ρ : Env) (x : List Bool) (hx : x.length=n)
    (hN : ρ 0=.nat (n+1)) (hword : ρ 40=wordValue x) :
    (batchProgram query).eval ρ=pairValue (predictorPair n x) := by
  let ρ₁ := Function.update ρ 50 (wordValue x)
  let ρ₂ := Function.update ρ₁ 51 (.nat n)
  have hf := fold_bodyProgram query n hq ρ₂ x hx (List.range n)
    (fun _ ht => List.mem_range.mp ht) (0,1) (by simpa [ρ₂,ρ₁] using hN)
    (by simp [ρ₂,ρ₁]) (by simp [ρ₂])
  rw [suffixPairs_eq_range,foldl_pairAdd,pairAdd_zero] at hf
  simp only [batchProgram,Expr.eval,hword]
  simp only [Function.update_self,wordValue_length,hx,Value.natVal]
  simp only [List.map_cons,List.map_nil,Expr.eval]
  dsimp only [ρ₂,ρ₁,pairValue] at hf
  rw [hf]
  simp [Expr.eval,ρ₂,ρ₁,pairValue,predictorPair,Value.arrayVal,Value.natVal]

end Paper37.PredictorBatchProgram
