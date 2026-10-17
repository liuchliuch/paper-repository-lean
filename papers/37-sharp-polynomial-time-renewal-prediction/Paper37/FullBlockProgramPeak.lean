import Paper37.FullBlockProgram
import Paper37.IntegerQueryProgramPeak

namespace Paper37.FullBlockProgram
open Paper37.BoundedLoop Paper37.WordProgram Paper37.IntegerPredictorProgram
open Paper37.IntegerQueryProgramPeak Paper37.IntegerOutputPeak Paper37.CachedOutput
set_option maxRecDepth 16000
set_option linter.unusedSimpArgs false

lemma finalArray_flat : Flat finalArray := by
  unfold finalArray
  apply Flat.array
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl
  all_goals
    repeat first | exact Flat.lit _ | exact Flat.var _ | apply Flat.get |
      apply Flat.binary .add | apply Flat.binary .mul

lemma finalArray_peak_bound (ρ : Env) (B : ℕ)
    (h49 : (ρ 49).representationSize≤B) (h70 : (ρ 70).representationSize≤B)
    (h71 : (ρ 71).representationSize≤B) : finalArray.peak ρ≤32*(B+4) := by
  have hzero : (Expr.lit 0).peak ρ≤1 := by norm_num [Expr.peak,Expr.eval,Value.representationSize]
  have hone : (Expr.lit 1).peak ρ≤2 := by norm_num [Expr.peak,Expr.eval,Value.representationSize]
  have hp := get_peak_le (.var 70) (.lit 0) ρ B 1 (var_peak_of_rep ρ 70 B h70) hzero
  have hq := get_peak_le (.var 71) (.lit 0) ρ B 1 (var_peak_of_rep ρ 71 B h71) hzero
  have hn := binary_peak_le .add (.var 49) (.lit 1) ρ B 2 (var_peak_of_rep ρ 49 B h49) hone
  have hm := binary_peak_le .mul (.add (.var 49) (.lit 1)) (.get (.var 71) (.lit 0)) ρ
    (2*(B+2+2)) (B+1+1) hn hq
  have hh := array_peak_le [.get (.var 70) (.lit 0),
    .mul (.add (.var 49) (.lit 1)) (.get (.var 71) (.lit 0))] ρ (fun _ => 8*(B+4)) (by
      intro e he
      simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl
      · dsimp only
        exact hp.trans (by omega)
      · dsimp only
        exact hm.trans (by omega))
  change (Expr.array [.get (.var 70) (.lit 0),
    .mul (.add (.var 49) (.lit 1)) (.get (.var 71) (.lit 0))]).peak ρ≤32*(B+4)
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hh
  omega

lemma finalArray_peak (ρ : Env) (H N : ℕ) (p q : ℕ×ℕ) (hN : N≤H)
    (h49 : ρ 49=.nat N) (h70 : ρ 70=pairValue p) (h71 : ρ 71=pairValue q)
    (hp : (pairValue p).representationSize≤200000000*(H+1)^4)
    (hq : (pairValue q).representationSize≤200000000*(H+1)^4) :
    finalArray.peak ρ≤queryPeakBound H := by
  let B := 200000000*(H+2)^4
  have hPow : (H+1)^4≤(H+2)^4 := Nat.pow_le_pow_left (by omega) _
  have hp' : (pairValue p).representationSize≤B := hp.trans (Nat.mul_le_mul_left _ hPow)
  have hq' : (pairValue q).representationSize≤B := hq.trans (Nat.mul_le_mul_left _ hPow)
  have h49' : (Value.nat N).representationSize≤B := by
    have hh := nat_representation N H hN
    have hl : H+2≤(H+2)^4 := le_self_pow₀ (by omega) (by decide)
    dsimp [B]
    omega
  have hf := finalArray_peak_bound ρ B (by simpa [h49] using h49')
    (by simpa [h70] using hp') (by simpa [h71] using hq')
  have hb : 32*(B+4)≤10000000000*(H+2)^4 := by
    dsimp [B]
    have hh : 1≤(H+2)^4 := by
      have hp : 0<(H+2)^4 := by positivity
      omega
    omega
  exact hf.trans (hb.trans (poly2_le_query H 10000000000 4 (by norm_num) (by norm_num)))

lemma visibleProgram_peak (ρ : Env) (H N : ℕ) (z : List Bool) (hpos : 0<H)
    (hH : ρ 0=.nat H) (hN : ρ 49=.nat N) (hNH : N≤H) (hw : ρ 40=wordValue z)
    (hz : z.length≤H) : visibleProgram.peak ρ≤queryPeakBound H := by
  let ρL := Function.update ρ 48 (.nat z.length)
  let ρR := Function.update ρL 12 (.nat 0)
  let p := evaluatePair H z 0
  let ρp := Function.update ρR 70 (pairValue p)
  let ρe := Function.update ρp 40 (wordValue [])
  let ρT := Function.update ρe 12 (.nat z.length)
  let q := evaluatePair H [] z.length
  let ρq := Function.update ρT 71 (pairValue q)
  have hlen : (Expr.length (.var 40)).peak ρ≤queryPeakBound H := by
    have hh := length_peak_le (.var 40) ρ (2*z.length+2)
      (by simpa [Expr.peak,Expr.eval,hw] using wordValue_size z)
    have hp := poly2_le_query H 1000 1 (by norm_num) (by norm_num)
    exact hh.trans (by nlinarith)
  have hp := continuationProgram_eval ρR H z 0 (by simpa [ρR,ρL] using hH)
    (by simpa [ρR,ρL] using hw) (by simp [ρR]) (by omega)
  have hpp := continuationProgram_peak ρR H z 0 hpos (by simpa [ρR,ρL] using hH)
    (by simpa [ρR,ρL] using hw) (by simp [ρR]) (by omega)
  have hq := continuationProgram_eval ρT H [] z.length (by simpa [ρT,ρe,ρp,ρR,ρL] using hH)
    (by simp [ρT,ρe]) (by simp [ρT]) (by simpa using hz)
  have hqp := continuationProgram_peak ρT H [] z.length hpos
    (by simpa [ρT,ρe,ρp,ρR,ρL] using hH) (by simp [ρT,ρe]) (by simp [ρT]) (by simpa using hz)
  have hfinal := finalArray_peak ρq H N p q hNH
    (by simpa [ρq,ρT,ρe,ρp,ρR,ρL] using hN)
    (by simp [ρq,ρT,ρe,ρp]) (by simp [ρq])
    (pairValue_evaluatePair_size H z 0 hpos (by omega))
    (pairValue_evaluatePair_size H [] z.length hpos (by simpa using hz))
  rw [visibleProgram]
  apply bind_peak_bound
  · exact hlen
  · rw [show (Expr.length (.var 40)).eval ρ=.nat z.length by simp [Expr.eval,hw,wordValue_length]]
    change (Expr.bind 12 (.lit 0) _).peak ρL≤_
    apply bind_peak_bound
    · exact lit_peak_query ρL H 0 (by omega)
    · rw [show (Expr.lit 0).eval ρL=.nat 0 by simp [Expr.eval]]
      change (Expr.bind 70 continuationProgram _).peak ρR≤_
      apply bind_peak_bound
      · exact hpp
      · rw [hp]
        change (Expr.bind 40 (.array []) _).peak ρp≤_
        apply bind_peak_bound
        · have hp := poly2_le_query H 10 0 (by norm_num) (by norm_num)
          norm_num only [pow_zero,Nat.mul_one] at hp
          norm_num [Expr.peak,Expr.eval,Value.representationSize]
          omega
        · rw [show (Expr.array []).eval ρp=wordValue [] by simp [Expr.eval,wordValue]]
          change (Expr.bind 12 (.var 48) _).peak ρe≤_
          apply bind_peak_bound
          · apply var_peak_of_rep
            simp only [ρe,ρp,ρR,ρL,Function.update_of_ne (by decide : (48:ℕ)≠40),
              Function.update_of_ne (by decide : (48:ℕ)≠70),Function.update_of_ne (by decide : (48:ℕ)≠12),Function.update_self]
            exact nat_rep_query z.length H (by omega)
          · rw [show (Expr.var 48).eval ρe=.nat z.length by simp [Expr.eval,ρe,ρp,ρR,ρL]]
            change (Expr.bind 71 continuationProgram finalArray).peak ρT≤_
            apply bind_peak_bound
            · exact hqp
            · rw [hq]
              exact hfinal

lemma visibleBranch_peak (ρ : Env) (H : ℕ) (x z : List Bool) (hpos : 0<H)
    (hH : ρ 0=.nat H) (hN : ρ 49=.nat x.length) (hw : ρ 40=wordValue x)
    (hi : ρ 47=.nat (firstIndex x)) (hs : Paper37.Prediction.firstSuffix x=some z)
    (hx : x.length≤H) : visibleBranch.peak ρ≤queryPeakBound H := by
  obtain ⟨hlen,hdrop⟩ := firstIndex_some x z hs
  let ρd := Function.update ρ 44 (.nat (firstIndex x+1))
  have hd := dropProgram_eval ρd x (firstIndex x+1) (by simpa [ρd] using hw) (by simp [ρd])
  rw [hdrop] at hd
  have hdp := dropProgram_peak ρd H x (firstIndex x+1) (by simpa [ρd] using hw)
    (by simp [ρd]) hx (by omega)
  have hvis := visibleProgram_peak (Function.update ρd 40 (wordValue z)) H x.length z hpos
    (by simpa [ρd] using hH) (by simpa [ρd] using hN) hx (by simp) (by omega)
  have hind : (Expr.add (.var 47) (.lit 1)).eval ρ=.nat (firstIndex x+1) := by
    simp [Expr.eval,hi,Value.natVal]
  have hip : (Expr.add (.var 47) (.lit 1)).peak ρ≤queryPeakBound H := by
    have hv := var_peak_of_rep ρ 47 (H+1) (by rw [hi];exact nat_representation _ H (by omega))
    have hl : (Expr.lit 1).peak ρ≤2 := by norm_num [Expr.peak,Expr.eval,Value.representationSize]
    have hh := binary_peak_le .add (.var 47) (.lit 1) ρ _ _ hv hl
    exact hh.trans (by have hp := poly2_le_query H 1000 1 (by norm_num) (by norm_num);nlinarith)
  rw [visibleBranch]
  apply bind_peak_bound _ _ _ _ _ hip
  rw [hind]
  change (Expr.bind 40 dropProgram visibleProgram).peak ρd≤_
  apply bind_peak_bound
  · exact hdp.trans (poly2_le_query H 100000 3 (by norm_num) (by norm_num))
  · rw [hd]
    exact hvis

lemma zeroArray_peak (ρ : Env) (H N : ℕ) (h49 : ρ 49=.nat N) (hN : N≤H) :
    zeroArray.peak ρ≤queryPeakBound H := by
  have hflat : Flat zeroArray := by
    unfold zeroArray
    apply Flat.array
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl
    · exact Flat.lit _
    · exact Flat.binary .add _ _ (Flat.var _) (Flat.lit _)
  have hval := nat_representation N H hN
  have hv : zeroArray.varsBound ρ (H+1) := by simp [zeroArray,Expr.varsBound,h49,hval]
  have hh := flat_peak_le hflat ρ (H+1) hv
  have hp := poly2_le_query H 1000 1 (by norm_num) (by norm_num)
  apply hh.trans
  simp [zeroArray,Expr.flatBudget]
  nlinarith

/-- Peak of the full normalized Q_N block-assignment program on its actual
word input, including both exact continuation queries and final division pair. -/
theorem program_peak (ρ : Env) (x : List Bool) (hw : ρ 40=wordValue x) :
    program.peak ρ≤1000000000000000*(x.length+3)^12 := by
  let H := x.length+1
  let ρH := Function.update ρ 0 (.nat H)
  let ρN := Function.update ρH 49 (.nat x.length)
  let ρi := Function.update ρN 47 (.nat (firstIndex x))
  have hpos : 0<H := by dsimp [H];omega
  have hlen : (Expr.length (.var 40)).peak ρ≤queryPeakBound H := by
    have hh := length_peak_le (.var 40) ρ (2*x.length+2)
      (by simpa [Expr.peak,Expr.eval,hw] using wordValue_size x)
    exact hh.trans (by have hp := poly2_le_query H 1000 1 (by norm_num) (by norm_num);dsimp [H] at hp ⊢;nlinarith)
  have hstart : (Expr.add (.length (.var 40)) (.lit 1)).peak ρ≤queryPeakBound H := by
    have hword := wordValue_size x
    have hl := length_peak_le (.var 40) ρ (2*x.length+2)
      (by simpa [Expr.peak,Expr.eval,hw] using hword)
    have hc : (Expr.lit 1).peak ρ≤2 := by norm_num [Expr.peak,Expr.eval,Value.representationSize]
    have hh := binary_peak_le .add (.length (.var 40)) (.lit 1) ρ _ _ hl hc
    exact hh.trans (by have hp := poly2_le_query H 1000 1 (by norm_num) (by norm_num);dsimp [H] at hp ⊢;nlinarith)
  have hi := firstIndexProgram_eval ρN x (by simpa [ρN,ρH] using hw)
  have hip := firstIndexProgram_peak ρN H x (by simpa [ρN,ρH] using hw) (by dsimp [H];omega)
  have h47 : (Expr.var 47).peak ρi≤queryPeakBound H := by
    apply var_peak_of_rep
    simp only [ρi,Function.update_self]
    exact nat_rep_query _ H (by have hh := firstIndex_le_length x;dsimp [H];omega)
  have h49 : (Expr.var 49).peak ρi≤queryPeakBound H := by
    apply var_peak_of_rep
    simp [ρi,ρN]
    exact nat_rep_query _ H (by dsimp [H];omega)
  have hbranch : (Expr.ifLT (.var 47) (.var 49) visibleBranch zeroArray).peak ρi≤queryPeakBound H := by
    cases hs : Paper37.Prediction.firstSuffix x with
    | none =>
      have hidx := firstIndex_none x hs
      apply if_false_peak
      · simp [Expr.eval,ρi,ρN,hidx,Value.natVal]
      · exact h47
      · exact h49
      · apply zeroArray_peak ρi H x.length (by simp [ρi,ρN])
        dsimp [H];omega
    | some z =>
      obtain ⟨hlen,hdrop⟩ := firstIndex_some x z hs
      apply if_true_peak
      · simp [Expr.eval,ρi,ρN,Value.natVal]
        omega
      · exact h47
      · exact h49
      · exact visibleBranch_peak ρi H x z hpos (by simp [ρi,ρN,ρH]) (by simp [ρi,ρN])
          (by simpa [ρi,ρN,ρH] using hw) (by simp [ρi]) hs (by dsimp [H];omega)
  have hp : program.peak ρ≤queryPeakBound H := by
    rw [program]
    apply bind_peak_bound _ _ _ _ _ hstart
    rw [show (Expr.add (.length (.var 40)) (.lit 1)).eval ρ=.nat H by simp [Expr.eval,hw,H,Value.natVal]]
    change (Expr.bind 49 (.length (.var 40)) _).peak ρH≤_
    apply bind_peak_bound
    · have hh := length_peak_le (.var 40) ρH (2*x.length+2)
        (by simpa [Expr.peak,Expr.eval,ρH,hw] using wordValue_size x)
      exact hh.trans (by have hp := poly2_le_query H 1000 1 (by norm_num) (by norm_num);dsimp [H] at hp ⊢;nlinarith)
    · rw [show (Expr.length (.var 40)).eval ρH=.nat x.length by simp [Expr.eval,ρH,hw]]
      change (Expr.bind 47 firstIndexProgram _).peak ρN≤_
      apply bind_peak_bound
      · exact hip.trans (poly2_le_query H 100000 3 (by norm_num) (by norm_num))
      · rw [hi]
        exact hbranch
  unfold queryPeakBound at hp
  dsimp [H] at hp
  simp only [Nat.add_assoc,Nat.reduceAdd] at hp
  omega

end Paper37.FullBlockProgram
