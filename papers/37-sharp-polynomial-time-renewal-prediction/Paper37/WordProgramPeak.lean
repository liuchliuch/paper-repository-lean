import Paper37.WordProgram
import Paper37.BoundedLoopFlat
import Paper37.CachedCoreWork

namespace Paper37.WordProgram
open Paper37.BoundedLoop Paper37.CachedCoreProgram
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
private abbrev v := Expr.var
private abbrev n := Expr.lit

lemma nat_representation_le {a H : ℕ} (h : a≤H) :
    (Value.nat a).representationSize≤H+1 := by
  have hs:=Paper37.DP.binarySize_le_self a
  simp only [Value.representationSize]
  omega

lemma bitValue_size (b : Bool) : (bitValue b).representationSize≤2 := by
  cases b <;> norm_num [bitValue,Value.representationSize]

lemma wordValue_size (x : List Bool) : (wordValue x).representationSize≤2*x.length+2 := by
  simp only [wordValue,Value.representationSize,List.map_map,Function.comp_def]
  have hh:=list_sum_bound x (fun b=>(bitValue b).representationSize) 2
    (fun b _=>bitValue_size b)
  omega

/-- The complete actual parser state is a polynomial-size finite array. -/
def stateSizeBound (H : ℕ) : ℕ := 4*(H+2)^2

def State.Valid (H : ℕ) (s : State) : Prop :=
  s.age+s.count≤H ∧ ∀d,s.hist d≤s.count

lemma stateValue_size {H : ℕ} {s : State} (hs : s.Valid H) :
    (stateValue H s).representationSize≤stateSizeBound H := by
  have ha : s.age≤H := by have hh:=hs.1;omega
  have hc : s.count≤H := by have hh:=hs.1;omega
  have har:=nat_representation_le ha
  have hcr:=nat_representation_le hc
  have hhist:=list_sum_bound (List.range (H+1))
    (fun d=>(Value.nat (s.hist d)).representationSize) (H+1)
    (by intro d hd; exact nat_representation_le ((hs.2 d).trans hc))
  simp only [List.length_range] at hhist
  simp only [stateValue,Value.representationSize,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,List.map_map,Function.comp_def] at *
  unfold stateSizeBound
  nlinarith

lemma step_valid {H : ℕ} {s : State} (hs : s.Valid H) (b : Bool)
    (hbudget : s.age+s.count+1≤H) : (step s b).Valid H := by
  constructor
  · cases b <;> simp [step] <;> omega
  · intro d
    cases b <;> simp only [step,if_false,if_true,false_and,and_false,and_true]
    · simpa using hs.2 d
    · split_ifs <;> have hh:=hs.2 d <;> omega

lemma run_valid {H : ℕ} {s : State} (x : List Bool) (hs : s.Valid H)
    (hbudget : s.age+s.count+x.length≤H) : (run s x).Valid H := by
  induction x generalizing s with
  | nil => exact hs
  | cons b x ih =>
    have hstep:=step_valid hs b (by simp only [List.length_cons] at hbudget;omega)
    change State.Valid H (run (step s b) x)
    apply ih hstep
    cases b <;> simp [step] at * <;> omega

/-- General array-loop peak estimate, including the complete produced array. -/
lemma tabulate_peak_le (ρ : Env) (i : ℕ) (bound body : Expr) (m A B : ℕ)
    (hm : (bound.eval ρ).natVal=m) (ha : bound.peak ρ≤A)
    (hb : ∀j<m,body.peak (Function.update ρ i (.nat j))≤B) :
    (Expr.tabulate i bound body).peak ρ≤A+(m+1)*B+2 := by
  rw [Expr.peak,Expr.eval,hm]
  apply max_le
  · simp only [Value.representationSize,List.map_map,Function.comp_def]
    have hs:=list_sum_bound (List.range m)
      (fun j=>(body.eval (Function.update ρ i (.nat j))).representationSize) B
      (by intro j hj;exact (representationSize_le_peak body _).trans (hb j (List.mem_range.mp hj)))
    simp only [List.length_range] at hs
    have hmono : m*B≤(m+1)*B := Nat.mul_le_mul_right B (by omega)
    omega
  · apply max_le (by omega)
    apply list_foldl_max_le _ _ _ (by omega)
    intro p hp
    obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hp
    have hh:=hb j (List.mem_range.mp hj)
    have hBB : B≤(m+1)*B := Nat.le_mul_of_pos_left _ (by omega)
    omega

def histogramCell : Expr := .ifLT (v 43) (.add (.get (v 42) (n 0)) (n 1))
  (.get (.get (v 42) (n 2)) (v 43))
  (.ifLT (.add (.get (v 42) (n 0)) (n 1)) (v 43)
    (.get (.get (v 42) (n 2)) (v 43))
    (.add (.get (.get (v 42) (n 2)) (v 43)) (n 1)))

lemma histogramCell_flat : Flat histogramCell := by
  unfold histogramCell
  repeat first | exact Flat.lit _ | exact Flat.var _ | apply Flat.get | apply Flat.ifLT |
    apply Flat.binary .add

lemma histogramCell_peak (ρ : Env) (B : ℕ)
    (hs : (ρ 42).representationSize≤B) (hi : (ρ 43).representationSize≤B) :
    histogramCell.peak ρ≤64*(B+1) := by
  have hv : histogramCell.varsBound ρ B := by
    simp only [histogramCell,Expr.varsBound]
    repeat' apply And.intro
    all_goals first | trivial | exact hs | exact hi
  have hh:=flat_peak_le histogramCell_flat ρ B hv
  simp only [histogramCell,Expr.flatBudget] at hh
  have hz : (0:ℕ).size=0 := by simp
  have ho : (1:ℕ).size=1 := by simpa using Nat.size_pow 0
  simp only [hz,ho] at hh
  unfold histogramCell
  have htwo:=Paper37.DP.binarySize_le_self 2
  omega

def histogramPeakBound (H : ℕ) : ℕ := 10*(H+2)+(H+2)*(64*(stateSizeBound H+1))+2

def parserPeakBound (H : ℕ) : ℕ := 3*histogramPeakBound H+100*(stateSizeBound H+1)+100

lemma frame_natural {a H : ℕ} (ha : a≤H+1) :
    (Value.nat a).representationSize≤stateSizeBound H := by
  have hh:=nat_representation_le ha
  unfold stateSizeBound
  nlinarith

lemma histogramIncrement_peak (ρ : Env) (H : ℕ) (s : State)
    (h0 : ρ 0=.nat H) (hs : ρ 42=stateValue H s) (hv : s.Valid H) :
    histogramIncrement.peak ρ≤histogramPeakBound H := by
  have hbound : (Expr.add (.var 0) (.lit 1)).peak ρ≤10*(H+2) := by
    have hn:=Paper37.DP.binarySize_le_self H
    simp only [Expr.peak,Expr.eval,h0,Value.representationSize,Value.natVal]
    have hh:=Paper37.DP.binarySize_le_self (H+1)
    have h1 : (1:ℕ).size=1 := by simpa using Nat.size_pow 0
    rw [h1]
    omega
  have hh:=tabulate_peak_le ρ 43 (.add (.var 0) (.lit 1)) histogramCell (H+1)
    (10*(H+2)) (64*(stateSizeBound H+1))
    (by simp [Expr.eval,h0,Value.natVal]) hbound (by
      intro j hj
      apply histogramCell_peak
      · simpa [hs] using stateValue_size hv
      · simpa using frame_natural (show j≤H+1 by omega))
  exact hh

lemma readState_peak (ρ : Env) (H : ℕ) (s : State) (i : ℕ) (hi : i≤2)
    (hs : ρ 42=stateValue H s) (hv : s.Valid H) :
    (Expr.get (.var 42) (.lit i)).peak ρ≤stateSizeBound H+4 := by
  apply get_peak_le (.var 42) (.lit i) ρ (stateSizeBound H) 3
  · simpa [Expr.peak,Expr.eval,hs] using stateValue_size hv
  · have hh:=nat_representation_le hi
    simpa [Expr.peak,Expr.eval,Value.representationSize] using hh

lemma parserStep_peak (ρ : Env) (H : ℕ) (s : State) (b : Bool)
    (h0 : ρ 0=.nat H) (hs : ρ 42=stateValue H s) (hb : ρ 41=bitValue b)
    (hv : s.Valid H) : parserStep.peak ρ≤parserPeakBound H := by
  have hh:=histogramIncrement_peak ρ H s h0 hs hv
  have hget (i : ℕ) (hi : i≤2) := readState_peak ρ H s i hi hs hv
  have hlit : (Expr.lit 1).peak ρ≤2 := by
    have hsize : (1:ℕ).size=1 := by simpa using Nat.size_pow 0
    simp [Expr.peak,Expr.eval,Value.representationSize,hsize]
  have hzero : (Expr.lit 0).peak ρ≤1 := by simp [Expr.peak,Expr.eval,Value.representationSize]
  have hadd (i : ℕ) (hi : i≤2) :
      (Expr.add (.get (.var 42) (.lit i)) (.lit 1)).peak ρ≤2*stateSizeBound H+16 := by
    have hp:=binary_peak_le .add (.get (.var 42) (.lit i)) (.lit 1) ρ
      (stateSizeBound H+4) 2 (hget i hi) hlit
    simpa [Op.expr] using hp
  let C:=histogramPeakBound H+2*stateSizeBound H+16
  have htrue:=array_peak_le
    [Expr.lit 0,Expr.add (.get (.var 42) (.lit 1)) (.lit 1),histogramIncrement] ρ (fun _=>C) (by
      intro e he
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at he
      rcases he with rfl|rfl|rfl
      · dsimp [C];omega
      · have hp:=hadd 1 (by omega);dsimp [C];omega
      · dsimp [C];omega)
  have hfalse:=array_peak_le
    [Expr.add (.get (.var 42) (.lit 0)) (.lit 1),Expr.get (.var 42) (.lit 1),Expr.get (.var 42) (.lit 2)]
    ρ (fun _=>C) (by
      intro e he
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at he
      rcases he with rfl|rfl|rfl
      · have hp:=hadd 0 (by omega);dsimp [C];omega
      · have hp:=hget 1 (by omega);dsimp [C];omega
      · have hp:=hget 2 (by omega);dsimp [C];omega)
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at htrue hfalse
  have hbit : (Expr.var 41).peak ρ≤2 := by
    simpa [Expr.peak,Expr.eval,hb] using bitValue_size b
  have hp:=if_peak_le (.lit 0) (.var 41)
    (.array [.lit 0,.add (.get (.var 42) (.lit 1)) (.lit 1),histogramIncrement])
    (.array [.add (.get (.var 42) (.lit 0)) (.lit 1),.get (.var 42) (.lit 1),.get (.var 42) (.lit 2)])
    ρ 1 2 (3*C+2) (3*C+2) hzero hbit (by omega) (by omega)
  have hmax : max 1 (max 2 (max (3*C+2) (3*C+2)))≤parserPeakBound H := by
    simp only [max_le_iff]
    unfold parserPeakBound
    dsimp only [C]
    omega
  simpa only [parserStep] using hp.trans hmax

lemma horizonBound_peak (ρ : Env) (H : ℕ) (h0 : ρ 0=.nat H) :
    (Expr.add (.var 0) (.lit 1)).peak ρ≤10*(H+2) := by
  have hn:=Paper37.DP.binarySize_le_self H
  have hh:=Paper37.DP.binarySize_le_self (H+1)
  have h1 : (1:ℕ).size=1 := by simpa using Nat.size_pow 0
  simp only [Expr.peak,Expr.eval,h0,Value.representationSize,Value.natVal,h1]
  omega

lemma parserBase_peak (ρ : Env) (H : ℕ) (h0 : ρ 0=.nat H) :
    parserBase.peak ρ≤parserPeakBound H := by
  have hh:=tabulate_peak_le ρ 43 (.add (.var 0) (.lit 1)) (.lit 0) (H+1)
    (10*(H+2)) 1 (by simp [Expr.eval,h0,Value.natVal]) (horizonBound_peak ρ H h0)
    (by intros;simp [Expr.peak,Expr.eval,Value.representationSize])
  have hz : (Expr.lit 0).peak ρ≤1 := by simp [Expr.peak,Expr.eval,Value.representationSize]
  have ha:=array_peak_le [Expr.lit 0,Expr.lit 0,Expr.tabulate 43 (.add (.var 0) (.lit 1)) (.lit 0)]
    ρ (fun _=>10*(H+2)+(H+2)+2) (by
      intro e he
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at he
      rcases he with rfl|rfl|rfl <;> dsimp only <;> omega)
  change parserBase.peak ρ≤_ at ha
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at ha
  unfold parserPeakBound histogramPeakBound stateSizeBound
  nlinarith

lemma fold_parser_peak (ρ : Env) (H : ℕ) (s : State) (x : List Bool)
    (h0 : ρ 0=.nat H) (hv : s.Valid H) (hbudget : s.age+s.count+x.length≤H)
    (p : ℕ) (hp : p≤parserPeakBound H) :
    ((x.map bitValue).foldl (fun vp bit =>
      let σ:=Function.update (Function.update ρ 41 bit) 42 vp.1
      (parserStep.eval σ,max vp.2 (parserStep.peak σ))) (stateValue H s,p)).2≤parserPeakBound H := by
  induction x generalizing s p with
  | nil => exact hp
  | cons b x ih =>
    have hb : s.age+s.count+1≤H := by simp only [List.length_cons] at hbudget;omega
    have hs:=step_valid hv b hb
    have hrest : (step s b).age+(step s b).count+x.length≤H := by
      cases b <;> simp [step] at * <;> omega
    let σ:=Function.update (Function.update ρ 41 (bitValue b)) 42 (stateValue H s)
    have hstep:=parserStep_eval σ H s b (by simpa [σ] using h0) (by simp [σ]) (by simp [σ])
    have hpeak:=parserStep_peak σ H s b (by simpa [σ] using h0) (by simp [σ]) (by simp [σ]) hv
    simp only [List.map_cons,List.foldl_cons]
    change ((x.map bitValue).foldl _ (parserStep.eval σ,max p (parserStep.peak σ))).2≤_
    rw [hstep]
    exact ih (step s b) hs hrest _ (max_le hp hpeak)

/-- Dynamic peak of the real finite parser, including every intermediate
histogram and all states along its actual fold. -/
theorem parserProgram_peak (ρ : Env) (H : ℕ) (x : List Bool)
    (h0 : ρ 0=.nat H) (hx : ρ 40=wordValue x) (hlen : x.length≤H) :
    parserProgram.peak ρ≤1000000*(H+2)^4 := by
  have hinitial : initial.Valid H := by constructor <;> simp [initial]
  have hvalid:=run_valid x hinitial (by simpa [initial] using hlen)
  have hstate:=stateValue_size hvalid
  have hbase:=parserBase_peak ρ H h0
  have hfold:=fold_parser_peak ρ H initial x h0 hinitial (by simpa [initial] using hlen) 0 (by omega)
  have he:=parserProgram_eval ρ H x h0 hx
  have hword:=wordValue_size x
  have hsmall : stateSizeBound H≤parserPeakBound H := by unfold parserPeakBound;omega
  have hword' : 2*x.length+2≤parserPeakBound H := by
    unfold parserPeakBound histogramPeakBound stateSizeBound
    nlinarith
  have hp : parserProgram.peak ρ≤parserPeakBound H := by
    rw [parserProgram,Expr.peak]
    apply max_le
    · rw [show (Expr.foldArray 41 42 (.var 40) parserBase parserStep).eval ρ=stateValue H (run initial x) from he]
      exact hstate.trans hsmall
    · apply max_le
      · simpa [Expr.peak,Expr.eval,hx] using hword.trans hword'
      · apply max_le hbase
        simp only [Expr.eval,hx,wordValue,Value.arrayVal]
        rw [parserBase_eval ρ H h0]
        exact hfold
  apply hp.trans
  unfold parserPeakBound histogramPeakBound stateSizeBound
  nlinarith [sq_nonneg (H:ℤ)]

def wordFrame (H : ℕ) : ℕ := 4*(H+2)

lemma word_frame (x : List Bool) (H : ℕ) (hx : x.length≤H) :
    (wordValue x).representationSize≤wordFrame H := by
  have hh:=wordValue_size x
  unfold wordFrame
  omega

lemma nat_wordFrame {a H : ℕ} (ha : a≤H+1) :
    (Value.nat a).representationSize≤wordFrame H := by
  have hh:=nat_representation_le ha
  unfold wordFrame
  omega

def dropBound : Expr := .sub (.length (.var 40)) (.var 44)
def dropCell : Expr := .get (.var 40) (.add (.var 44) (.var 45))

lemma dropBound_flat : Flat dropBound := by
  exact Flat.binary .sub _ _ (Flat.length _ (Flat.var _)) (Flat.var _)
lemma dropCell_flat : Flat dropCell := by
  exact Flat.get _ _ (Flat.var _) (Flat.binary .add _ _ (Flat.var _) (Flat.var _))

/-- Every array element and index expression in a run-time suffix extraction
has polynomial representation size, including the produced suffix itself. -/
theorem dropProgram_peak (ρ : Env) (H : ℕ) (x : List Bool) (d : ℕ)
    (hx : ρ 40=wordValue x) (hd : ρ 44=.nat d) (hlen : x.length≤H) (hdH : d≤H) :
    dropProgram.peak ρ≤100000*(H+2)^3 := by
  let B:=wordFrame H
  have hw : (ρ 40).representationSize≤B := by simpa [hx,B] using word_frame x H hlen
  have hdrop : (ρ 44).representationSize≤B := by simpa [hd,B] using nat_wordFrame (show d≤H+1 by omega)
  have hbound:=flat_peak_le dropBound_flat ρ B (by simpa only [dropBound,Expr.varsBound] using And.intro hw hdrop)
  have hbound' : dropBound.peak ρ≤64*(B+1) := hbound.trans (by simp [dropBound,Expr.flatBudget];omega)
  have hcell (i : ℕ) (hi : i<x.length-d) :
      dropCell.peak (Function.update ρ 45 (.nat i))≤64*(B+1) := by
    have hv : dropCell.varsBound (Function.update ρ 45 (.nat i)) B := by
      have hiB:=nat_wordFrame (H:=H) (a:=i) (by omega)
      simp only [dropCell,Expr.varsBound]
      exact ⟨by simpa using hw,by simpa using hdrop,by simpa [B] using hiB⟩
    apply (flat_peak_le dropCell_flat _ B hv).trans
    simp [dropCell,Expr.flatBudget]
    omega
  have ht:=tabulate_peak_le ρ 45 dropBound dropCell (x.length-d)
    (64*(B+1)) (64*(B+1)) (by simp [dropBound,Expr.eval,hx,hd,Value.natVal]) hbound' hcell
  have hm : x.length-d+1≤H+1 := by omega
  have hmul:=Nat.mul_le_mul_right (64*(B+1)) hm
  have hpoly : 64*(B+1)+(H+1)*(64*(B+1))+2≤100000*(H+2)^3 := by
    have hh : (H+2)^2≤(H+2)^3 := Nat.pow_le_pow_right (by omega) (by decide)
    calc _ ≤100000*(H+2)^2 := by dsimp [B,wordFrame];nlinarith
         _ ≤_ := Nat.mul_le_mul_left _ hh
  simpa only [dropProgram,dropBound,dropCell] using ht.trans (by omega)

def reverseCell : Expr := .get (.var 40)
  (.sub (.sub (.length (.var 40)) (.lit 1)) (.var 45))
lemma reverseCell_flat : Flat reverseCell := by
  exact Flat.get _ _ (Flat.var _) (Flat.binary .sub _ _
    (Flat.binary .sub _ _ (Flat.length _ (Flat.var _)) (Flat.lit _)) (Flat.var _))

theorem reverseProgram_peak (ρ : Env) (H : ℕ) (x : List Bool)
    (hx : ρ 40=wordValue x) (hlen : x.length≤H) :
    reverseProgram.peak ρ≤100000*(H+2)^3 := by
  let B:=wordFrame H
  have hw : (ρ 40).representationSize≤B := by simpa [hx,B] using word_frame x H hlen
  have hbound : (Expr.length (.var 40)).peak ρ≤B+1 := by
    exact length_peak_le _ _ _ (by simpa [Expr.peak,Expr.eval] using hw)
  have hcell (i : ℕ) (hi : i<x.length) :
      reverseCell.peak (Function.update ρ 45 (.nat i))≤128*(B+1) := by
    have hv : reverseCell.varsBound (Function.update ρ 45 (.nat i)) B := by
      have hiB:=nat_wordFrame (H:=H) (a:=i) (by omega)
      simp only [reverseCell,Expr.varsBound]
      exact ⟨by simpa using hw,⟨⟨by simpa using hw,trivial⟩,by simpa [B] using hiB⟩⟩
    apply (flat_peak_le reverseCell_flat _ B hv).trans
    have ho : (1:ℕ).size=1 := by simpa using Nat.size_pow 0
    simp [reverseCell,Expr.flatBudget,ho]
    omega
  have ht:=tabulate_peak_le ρ 45 (.length (.var 40)) reverseCell x.length
    (B+1) (128*(B+1)) (by simp [Expr.eval,hx,Value.natVal]) hbound hcell
  have hm:=Nat.mul_le_mul_right (128*(B+1)) (show x.length+1≤H+1 by omega)
  have hpoly : (B+1)+(H+1)*(128*(B+1))+2≤100000*(H+2)^3 := by
    have hh : (H+2)^2≤(H+2)^3 := Nat.pow_le_pow_right (by omega) (by decide)
    calc _ ≤100000*(H+2)^2 := by dsimp [B,wordFrame];nlinarith
         _ ≤_ := Nat.mul_le_mul_left _ hh
  simpa only [reverseProgram,reverseCell] using ht.trans (by omega)

def appendCell : Expr := .ifLT (.var 45) (.length (.var 40))
  (.get (.var 40) (.var 45)) (.var 46)
lemma appendCell_flat : Flat appendCell := by
  exact Flat.ifLT _ _ _ _ (Flat.var _) (Flat.length _ (Flat.var _))
    (Flat.get _ _ (Flat.var _) (Flat.var _)) (Flat.var _)

theorem appendProgram_peak (ρ : Env) (H : ℕ) (x : List Bool) (b : Bool)
    (hx : ρ 40=wordValue x) (hb : ρ 46=bitValue b) (hlen : x.length≤H) :
    appendProgram.peak ρ≤100000*(H+2)^3 := by
  let B:=wordFrame H
  have hw : (ρ 40).representationSize≤B := by simpa [hx,B] using word_frame x H hlen
  have hbit : (ρ 46).representationSize≤B := by
    have hh:=bitValue_size b
    simp only [hb]
    dsimp [B,wordFrame]
    omega
  have hbound : (Expr.add (.length (.var 40)) (.lit 1)).peak ρ≤16*(B+1) := by
    apply (flat_peak_le (Flat.binary .add (Expr.length (.var 40)) (.lit 1) (Flat.length _ (Flat.var _)) (Flat.lit _)) ρ B
      (by simpa only [Op.expr,Expr.varsBound] using And.intro hw (show True from trivial))).trans
    have ho : (1:ℕ).size=1 := by simpa using Nat.size_pow 0
    simp [Op.expr,Expr.flatBudget,ho]
    omega
  have hcell (i : ℕ) (hi : i<x.length+1) :
      appendCell.peak (Function.update ρ 45 (.nat i))≤64*(B+1) := by
    have hiB:=nat_wordFrame (H:=H) (a:=i) (by omega)
    have hv : appendCell.varsBound (Function.update ρ 45 (.nat i)) B := by
      simp only [appendCell,Expr.varsBound]
      exact ⟨by simpa [B] using hiB,by simpa using hw,
        ⟨by simpa using hw,by simpa [B] using hiB⟩,by simpa using hbit⟩
    apply (flat_peak_le appendCell_flat _ B hv).trans
    simp [appendCell,Expr.flatBudget]
    omega
  have ht:=tabulate_peak_le ρ 45 (.add (.length (.var 40)) (.lit 1)) appendCell (x.length+1)
    (16*(B+1)) (64*(B+1)) (by simp [Expr.eval,hx,Value.natVal]) hbound hcell
  have hm:=Nat.mul_le_mul_right (64*(B+1)) (show x.length+1+1≤H+2 by omega)
  have hpoly : 16*(B+1)+(H+2)*(64*(B+1))+2≤100000*(H+2)^3 := by
    have hh : (H+2)^2≤(H+2)^3 := Nat.pow_le_pow_right (by omega) (by decide)
    calc _ ≤100000*(H+2)^2 := by dsimp [B,wordFrame];nlinarith
         _ ≤_ := Nat.mul_le_mul_left _ hh
  simpa only [appendProgram,appendCell] using ht.trans (by omega)

def firstBody : Expr := .ifLT (.lit 0) (.var 41) (.lit 0) (.add (.var 44) (.lit 1))
lemma firstBody_flat : Flat firstBody := by
  exact Flat.ifLT _ _ _ _ (Flat.lit _) (Flat.var _) (Flat.lit _)
    (Flat.binary .add _ _ (Flat.var _) (Flat.lit _))

lemma firstBody_eval (ρ : Env) (a : ℕ) (b : Bool)
    (ha : ρ 44=.nat a) (hb : ρ 41=bitValue b) :
    firstBody.eval ρ=.nat (if b then 0 else a+1) := by
  cases b <;> simp [firstBody,Expr.eval,ha,hb,bitValue,Value.natVal]

lemma firstBody_peak (ρ : Env) (H a : ℕ) (b : Bool)
    (ha : ρ 44=.nat a) (hb : ρ 41=bitValue b) (haH : a≤H) :
    firstBody.peak ρ≤64*(wordFrame H+1) := by
  have hbit : (ρ 41).representationSize≤wordFrame H := by
    have hh:=bitValue_size b
    rw [hb]
    unfold wordFrame
    omega
  have hacc : (ρ 44).representationSize≤wordFrame H := by
    simpa [ha] using nat_wordFrame (show a≤H+1 by omega)
  have hv : firstBody.varsBound ρ (wordFrame H) := by
    simpa only [firstBody,Expr.varsBound] using
      And.intro (show True from trivial) (And.intro hbit (And.intro (show True from trivial)
        (And.intro hacc (show True from trivial))))
  apply (flat_peak_le firstBody_flat ρ (wordFrame H) hv).trans
  have ho : (1:ℕ).size=1 := by simpa using Nat.size_pow 0
  simp [firstBody,Expr.flatBudget,ho]
  omega

lemma fold_first_peak (ρ : Env) (H a : ℕ) (x : List Bool) (hbudget : a+x.length≤H)
    (p : ℕ) (hp : p≤64*(wordFrame H+1)) :
    ((x.map bitValue).foldl (fun vp bit =>
      let σ:=Function.update (Function.update ρ 41 bit) 44 vp.1
      (firstBody.eval σ,max vp.2 (firstBody.peak σ))) (.nat a,p)).2≤64*(wordFrame H+1) := by
  induction x generalizing a p with
  | nil => exact hp
  | cons b x ih =>
    let σ:=Function.update (Function.update ρ 41 (bitValue b)) 44 (.nat a)
    have he:=firstBody_eval σ a b (by simp [σ]) (by simp [σ])
    have hpeak:=firstBody_peak σ H a b (by simp [σ]) (by simp [σ]) (by simp only [List.length_cons] at hbudget;omega)
    have hrest : (if b then 0 else a+1)+x.length≤H := by
      cases b <;> simp at * <;> omega
    simp only [List.map_cons,List.foldl_cons]
    change ((x.map bitValue).foldl _ (firstBody.eval σ,max p (firstBody.peak σ))).2≤_
    rw [he]
    exact ih _ hrest _ (max_le hp hpeak)

lemma firstIndex_le_length (x : List Bool) : firstIndex x≤x.length := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simp [firstIndex] at * <;> omega

/-- Dynamic peak of the genuine first-renewal scan, including all reversed
input entries and all scalar accumulators along its actual execution. -/
theorem firstIndexProgram_peak (ρ : Env) (H : ℕ) (x : List Bool)
    (hx : ρ 40=wordValue x) (hlen : x.length≤H) :
    firstIndexProgram.peak ρ≤100000*(H+2)^3 := by
  have hrev:=reverseProgram_peak ρ H x hx hlen
  have he:=firstIndexProgram_eval ρ x hx
  have hre:=reverseProgram_eval ρ x hx
  have houtput:=nat_representation_le ((firstIndex_le_length x).trans hlen)
  have hfold:=fold_first_peak ρ H 0 x.reverse (by simpa using hlen) 0 (by omega)
  have hC : 64*(wordFrame H+1)≤100000*(H+2)^3 := by
    have hpow : (H+2)^2≤(H+2)^3 := Nat.pow_le_pow_right (by omega) (by decide)
    calc _ ≤100000*(H+2)^2 := by unfold wordFrame;nlinarith
         _ ≤_ := Nat.mul_le_mul_left _ hpow
  have hlin : H+1≤64*(wordFrame H+1) := by unfold wordFrame;omega
  rw [firstIndexProgram,Expr.peak]
  apply max_le
  · rw [show (Expr.foldArray 41 44 reverseProgram (.lit 0)
      (.ifLT (.lit 0) (.var 41) (.lit 0) (.add (.var 44) (.lit 1)))).eval ρ=.nat (firstIndex x) from he]
    exact houtput.trans (hlin.trans hC)
  · apply max_le hrev
    apply max_le
    · have hz : (Expr.lit 0).peak ρ=1 := by simp [Expr.peak,Expr.eval,Value.representationSize]
      rw [hz]
      omega
    · rw [hre]
      change ((x.reverse.map bitValue).foldl _ ((Expr.lit 0).eval ρ,0)).2≤_
      rw [show (Expr.lit 0).eval ρ=Value.nat 0 by simp [Expr.eval]]
      apply le_trans _ hC
      simpa only [firstBody] using hfold

end Paper37.WordProgram
