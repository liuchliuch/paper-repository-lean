import Paper37.PredictorBatchProgram
import Paper37.WordProgramWork

namespace Paper37.PredictorBatchProgram
open Paper37.BoundedLoop Paper37.WordProgram Paper37.CachedCoreProgram
set_option linter.unusedSimpArgs false
private abbrev v := Expr.var

/-- An actual evaluator-work property of a finite syntax term. -/
def QueryWork (query : Expr) (N B : ℕ) : Prop :=
  ∀(ρ : Env)(y : List Bool),ρ 0=.nat N → ρ 40=wordValue y → y.length<N → query.work ρ≤B

lemma pairAddProgram_work (ρ : Env) : pairAddProgram.work ρ≤50 := by
  simp [pairAddProgram,Expr.work]

lemma bodyProgram_work (query : Expr) (n B : ℕ) (hq : QueryWork query (n+1) B)
    (ρ : Env) (x : List Bool) (hx : x.length=n) (t : ℕ) (ht : t<n)
    (hN : ρ 0=.nat (n+1)) (h50 : ρ 50=wordValue x)
    (h51 : ρ 51=.nat n) (h52 : ρ 52=.nat t) :
    (bodyProgram query).work ρ≤B+20*(n+1)+100 := by
  let ρ₁:=Function.update ρ 40 (wordValue x)
  let ρ₂:=Function.update ρ₁ 44 (.nat (n-(t+1)))
  have hdrop:=dropProgram_eval ρ₂ x (n-(t+1)) (by simp [ρ₂,ρ₁]) (by simp [ρ₂])
  have hwDrop:=dropProgram_work ρ₂ x (n-(t+1)) (by simp [ρ₂,ρ₁]) (by simp [ρ₂])
  let ρ₃:=Function.update ρ₂ 40 (wordValue (x.drop (n-(t+1))))
  have hy : (x.drop (n-(t+1))).length<n+1 := by simp only [List.length_drop,hx];omega
  have hwQuery:=hq ρ₃ (x.drop (n-(t+1))) (by simpa [ρ₃,ρ₂,ρ₁] using hN)
    (by simp [ρ₃]) hy
  have hwPair:=pairAddProgram_work (Function.update ρ₃ 54 (query.eval ρ₃))
  simp only [bodyProgram,Expr.work,Expr.eval,h50]
  simp only [Function.update_of_ne (by omega : (51:ℕ)≠40),
    Function.update_of_ne (by omega : (52:ℕ)≠40),h51,h52,Value.natVal]
  change 1+1+(1+(1+1+1)+1+1+(dropProgram.work ρ₂+1+
    (query.work (Function.update ρ₂ 40 (dropProgram.eval ρ₂))+1+
      pairAddProgram.work (Function.update (Function.update ρ₂ 40 (dropProgram.eval ρ₂)) 54
        (query.eval (Function.update ρ₂ 40 (dropProgram.eval ρ₂)))))))≤_
  rw [hdrop]
  change 1+1+(1+(1+1+1)+1+1+(dropProgram.work ρ₂+1+
    (query.work ρ₃+1+pairAddProgram.work (Function.update ρ₃ 54 (query.eval ρ₃)))))≤_
  rw [hx] at hwDrop
  omega

/-- The batch AST performs precisely a linear number of requested queries;
its charge includes suffix construction, pair arithmetic and loop control. -/
theorem batchProgram_work (query : Expr) (n B : ℕ) (hq : QueryWork query (n+1) B)
    (ρ : Env) (x : List Bool) (hx : x.length=n) (hword : ρ 40=wordValue x)
    (hN : ρ 0=.nat (n+1)) :
    (batchProgram query).work ρ≤n*(B+20*(n+1)+104)+40 := by
  let ρ₁:=Function.update ρ 50 (wordValue x)
  let ρ₂:=Function.update ρ₁ 51 (.nat n)
  have hf:=foldl_charge_bound (List.range n)
    (fun val t => (bodyProgram query).eval (Function.update (Function.update ρ₂ 52 (.nat t)) 53 val))
    (fun val t => (bodyProgram query).work (Function.update (Function.update ρ₂ 52 (.nat t)) 53 val))
    (B+20*(n+1)+100) (by
      intro val t ht
      exact bodyProgram_work query n B hq _ x hx t (List.mem_range.mp ht)
        (by simpa [ρ₂,ρ₁] using hN) (by simp [ρ₂,ρ₁]) (by simp [ρ₂]) (by simp))
    (pairValue (0,1)) 0
  simp only [List.length_range,zero_add] at hf
  have hout (σ : Env) : (Expr.array [.get (v 57) (.lit 0),
    .mul (.get (v 57) (.lit 1)) (v 51)]).work σ≤20 := by simp [Expr.work]
  simp only [batchProgram,Expr.work,Expr.eval,hword]
  simp only [Function.update_self,wordValue_length,hx,Value.natVal]
  simp only [Expr.work,Expr.eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Value.natVal]
  dsimp only [ρ₂,ρ₁,pairValue] at hf
  have he : B+20*(n+1)+100+4=B+20*(n+1)+104 := by omega
  rw [he] at hf
  omega

end Paper37.PredictorBatchProgram
