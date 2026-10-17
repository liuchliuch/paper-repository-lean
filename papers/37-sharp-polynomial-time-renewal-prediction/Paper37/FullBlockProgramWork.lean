import Paper37.FullBlockProgram

/-! Actual arithmetic/address/control work of the full-block source AST. -/
namespace Paper37.FullBlockProgram
open Paper37.BoundedLoop Paper37.WordProgram Paper37.IntegerPredictorProgram
open Paper37.CachedOutput Paper37.Prediction
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

lemma visibleProgram_work (ρ : Env) (H N : ℕ) (z : List Bool)
    (hH : ρ 0=.nat H) (hN : ρ 49=.nat N) (hw : ρ 40=wordValue z)
    (hz : z.length≤H) : visibleProgram.work ρ≤2200*(H+1)^4 := by
  let ρL:=Function.update ρ 48 (.nat z.length)
  let ρR:=Function.update ρL 12 (.nat 0)
  have hp:=continuationProgram_eval ρR H z 0 (by simpa [ρR,ρL] using hH)
    (by simpa [ρR,ρL] using hw) (by simp [ρR]) (by omega)
  have hwp:=continuationProgram_work ρR H z 0 (by simpa [ρR,ρL] using hH)
    (by simpa [ρR,ρL] using hw) (by simp [ρR]) (by omega)
  let ρp:=Function.update ρR 70 (pairValue (evaluatePair H z 0))
  let ρe:=Function.update ρp 40 (wordValue [])
  let ρT:=Function.update ρe 12 (.nat z.length)
  have hwq:=continuationProgram_work ρT H [] z.length (by simpa [ρT,ρe,ρp,ρR,ρL] using hH)
    (by simp [ρT,ρe]) (by simp [ρT]) (by simpa using hz)
  have harray (σ : Env) : finalArray.work σ=13 := by simp [finalArray,Expr.work]
  have hL : (Expr.length (.var 40)).eval ρ=.nat z.length := by simp [Expr.eval,hw]
  have hzero : (Expr.lit 0).eval ρL=.nat 0 := by simp [Expr.eval]
  have he : (Expr.array []).eval ρp=wordValue [] := by simp [Expr.eval,wordValue]
  have hlen : (Expr.var 48).eval ρe=.nat z.length := by simp [Expr.eval,ρe,ρp,ρR,ρL]
  have hpow : 1≤(H+1)^4 := one_le_pow₀ (by omega)
  rw [visibleProgram,Expr.work,hL,
    show (Expr.length (.var 40)).work ρ=2 by simp [Expr.work]]
  change 3+(Expr.bind 12 (.lit 0) _).work ρL≤_
  rw [Expr.work,hzero,show (Expr.lit 0).work ρL=1 by simp [Expr.work]]
  change 3+(2+(Expr.bind 70 continuationProgram _).work ρR)≤_
  rw [Expr.work,hp]
  change 3+(2+(continuationProgram.work ρR+1+(Expr.bind 40 (.array []) _).work ρp))≤_
  rw [Expr.work,he,show (Expr.array []).work ρp=1 by simp [Expr.work]]
  change 3+(2+(continuationProgram.work ρR+1+(2+(Expr.bind 12 (.var 48) _).work ρe)))≤_
  rw [Expr.work,hlen,show (Expr.var 48).work ρe=1 by simp [Expr.work]]
  change 3+(2+(continuationProgram.work ρR+1+(2+(2+
    (Expr.bind 71 continuationProgram finalArray).work ρT))))≤_
  rw [Expr.work,harray]
  omega

lemma visibleBranch_work (ρ : Env) (H : ℕ) (x z : List Bool)
    (hH : ρ 0=.nat H) (hN : ρ 49=.nat x.length) (hw : ρ 40=wordValue x)
    (hi : ρ 47=.nat (firstIndex x)) (hs : firstSuffix x=some z)
    (hx : x.length≤H) : visibleBranch.work ρ≤2400*(H+1)^4 := by
  obtain ⟨hl,hd⟩:=firstIndex_some x z hs
  let ρd:=Function.update ρ 44 (.nat (firstIndex x+1))
  have he:=dropProgram_eval ρd x (firstIndex x+1) (by simpa [ρd] using hw) (by simp [ρd])
  rw [hd] at he
  have hwd:=dropProgram_work ρd x (firstIndex x+1) (by simpa [ρd] using hw) (by simp [ρd])
  let ρz:=Function.update ρd 40 (wordValue z)
  have hwv:=visibleProgram_work ρz H x.length z (by simpa [ρz,ρd] using hH)
    (by simpa [ρz,ρd] using hN) (by simp [ρz]) (by omega)
  have hidx : (Expr.add (.var 47) (.lit 1)).eval ρ=.nat (firstIndex x+1) := by
    simp [Expr.eval,hi,Value.natVal]
  have hpow : x.length+1≤(H+1)^4 := by
    have hh : H+1≤(H+1)^4 := le_self_pow₀ (by omega) (by decide)
    omega
  rw [visibleBranch,Expr.work,hidx,
    show (Expr.add (.var 47) (.lit 1)).work ρ=3 by simp [Expr.work]]
  change 3+1+(Expr.bind 40 dropProgram visibleProgram).work ρd≤_
  rw [Expr.work,he]
  change 3+1+(dropProgram.work ρd+1+visibleProgram.work ρz)≤_
  omega

/-- Both actual continuation runs, source-word parsing and final integer
normalization use uniformly quartic native arithmetic work. -/
theorem program_work (ρ : Env) (x : List Bool) (hw : ρ 40=wordValue x) :
    program.work ρ≤3000*(x.length+2)^4 := by
  let ρH:=Function.update ρ 0 (.nat (x.length+1))
  let ρN:=Function.update ρH 49 (.nat x.length)
  have hi:=firstIndexProgram_eval ρN x (by simpa [ρN,ρH] using hw)
  have hwi:=firstIndexProgram_work ρN x (by simpa [ρN,ρH] using hw)
  let ρi:=Function.update ρN 47 (.nat (firstIndex x))
  have hH : (Expr.add (.length (.var 40)) (.lit 1)).eval ρ=.nat (x.length+1) := by
    simp [Expr.eval,hw,Value.natVal]
  have hN : (Expr.length (.var 40)).eval ρH=.nat x.length := by simp [Expr.eval,ρH,hw]
  have hp : x.length+1≤(x.length+2)^4 := by
    have hh : x.length+2≤(x.length+2)^4 := le_self_pow₀ (by omega) (by decide)
    omega
  rw [program,Expr.work,hH,
    show (Expr.add (.length (.var 40)) (.lit 1)).work ρ=4 by simp [Expr.work]]
  change 5+(Expr.bind 49 (.length (.var 40)) _).work ρH≤_
  rw [Expr.work,hN,show (Expr.length (.var 40)).work ρH=2 by simp [Expr.work]]
  change 5+(3+(Expr.bind 47 firstIndexProgram _).work ρN)≤_
  rw [Expr.work,hi]
  change 5+(3+(firstIndexProgram.work ρN+1+
    (Expr.ifLT (.var 47) (.var 49) visibleBranch zeroArray).work ρi))≤_
  cases hs:firstSuffix x with
  | none =>
    have hh:=firstIndex_none x hs
    have hzero : (Expr.ifLT (.var 47) (.var 49) visibleBranch zeroArray).work ρi=10 := by
      simp [Expr.work,Expr.eval,ρi,ρN,hh,zeroArray,Value.natVal]
    rw [hzero]
    omega
  | some z =>
    obtain ⟨hl,hd⟩:=firstIndex_some x z hs
    have hh:firstIndex x<x.length:=by omega
    have hbranch := visibleBranch_work ρi (x.length+1) x z
      (by simp [ρi,ρN,ρH]) (by simp [ρi,ρN]) (by simpa [ρi,ρN,ρH] using hw)
      (by simp [ρi]) hs (by omega)
    have hif : (Expr.ifLT (.var 47) (.var 49) visibleBranch zeroArray).work ρi=
        3+visibleBranch.work ρi := by
      simp [Expr.work,Expr.eval,ρi,ρN,hh,Value.natVal]
    rw [hif]
    simp only [show x.length+1+1=x.length+2 by omega] at hbranch
    omega

end Paper37.FullBlockProgram
