import Paper15.NaturalChecker
import Paper15.ExactSoundness
namespace Paper15.NaturalExact
open Exact Finset BigOperators

def Cube.get (c : Cube) (i j k : Fin 3) : Corner := Tri.get (Tri.get (Tri.get c i) j) k
def Corner.eval (c : Corner) (u : Fin 3) : Nat := if u=0 then c.one else if u=1 then c.three else c.pair
def offset (u : Fin 3) : Nat := if u=0 then 3 else 1

lemma map3_get {α β : Type} (f : α → β) (v : Tri α) (i : Fin 3) :
    (map3 f v).get i=f (v.get i) := by fin_cases i <;> rfl
lemma zip3_get {α β γ : Type} (f : α → β → γ) (v : Tri α) (w : Tri β) (i : Fin 3) :
    (zip3 f v w).get i=f (v.get i) (w.get i) := by fin_cases i <;> rfl
lemma mix3_get {α : Type} (add : α → α → α) (double : α → α) (v : Tri α) (i j k : Fin 3) :
    (mix3 add double v i j).get k=if k=i then add (v.get k) (v.get j) else double (v.get k) := by
  fin_cases i <;> fin_cases k <;> simp [mix3,Tri.get]
lemma Corner.eval_add (f g : Corner) (u : Fin 3) : (f.add g).eval u=f.eval u+g.eval u := by fin_cases u <;> rfl
lemma Corner.eval_double (f : Corner) (u : Fin 3) : f.double.eval u=2*f.eval u := by fin_cases u <;> rfl

lemma child_eval (c : Cell) (a r s u i j k : Fin 3) :
    (Cube.get (child c a r s).corners i j k).eval u =
      if a=0 then
        if i=r then (Cube.get c.corners i j k).eval u+(Cube.get c.corners s j k).eval u
        else 2*(Cube.get c.corners i j k).eval u
      else if a=1 then
        if j=r then (Cube.get c.corners i j k).eval u+(Cube.get c.corners i s k).eval u
        else 2*(Cube.get c.corners i j k).eval u
      else
        if k=r then (Cube.get c.corners i j k).eval u+(Cube.get c.corners i j s).eval u
        else 2*(Cube.get c.corners i j k).eval u := by
  fin_cases a
  · by_cases hi : i=r <;>
      simp [child,Cube.get,mix3_get,map3_get,zip3_get,rowAdd,rowDouble,planeAdd,planeDouble,
        Corner.eval_add,Corner.eval_double,hi]
  · by_cases hj : j=r <;>
      simp [child,Cube.get,mix3_get,map3_get,zip3_get,rowAdd,rowDouble,planeAdd,planeDouble,
        Corner.eval_add,Corner.eval_double,hj]
  · by_cases hk : k=r <;>
      simp [child,Cube.get,mix3_get,map3_get,zip3_get,rowAdd,rowDouble,planeAdd,planeDouble,
        Corner.eval_add,Corner.eval_double,hk]

noncomputable section

def Represents (T : DetTriangle) (n : Cell) (c : ProductCell) : Prop :=
  0<n.den ∧ ∀u i j k, ((Cube.get n.corners i j k).eval u : ℝ)-(offset u:ℝ)*n.den=
    (n.den:ℝ)*Exact.moment T c u i j k

lemma rootCorner_eval (a b c : Bool) (u : Fin 3) :
    ((rootCorner a b c).eval u : ℝ)-(offset u:ℝ) =
      if u=0 then signOfBit a+signOfBit b+signOfBit c
      else if u=1 then signOfBit a*signOfBit b*signOfBit c
      else signOfBit a*signOfBit b+signOfBit b*signOfBit c+signOfBit c*signOfBit a := by
  fin_cases u <;> cases a <;> cases b <;> cases c <;>
    norm_num [rootCorner,Corner.eval,offset,signOfBit]

lemma represents_root (w : Nat) : Represents (DetTriangle.ofPattern w) (root w) fullSourceCell := by
  refine ⟨by change (0:Nat)<1; decide,?_⟩
  intro u i j k
  simp only [root,Cube.get,Tri.get_tabulate,Nat.cast_one,mul_one,one_mul]
  rw [rootCorner_eval]
  fin_cases u <;> simp [Exact.moment,Exact.momentWeight,fullSourceCell,Exact.weightExp_dirac,
    w1,w2,w3,DetTriangle.ofPattern,bitOf]

lemma Represents.child {T : DetTriangle} {n : Cell} {c : ProductCell}
    (h : Represents T n c) (a r s : Fin 3) :
    Represents T (NaturalExact.child n a r s) (cellChild c a r s) := by
  refine ⟨mul_pos (by decide) h.1,?_⟩
  intro u i j k
  have hd : (NaturalExact.child n a r s).den=2*n.den := rfl
  have hi := h.2 u i j k
  have hix := h.2 u s j k
  have hiy := h.2 u i s k
  have hiz := h.2 u i j s
  rw [child_eval,Exact.moment_child,hd]
  split_ifs <;> simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] <;> nlinarith

lemma Cube.all_iff (v : Cube) (p : Corner → Bool) :
    v.all (fun xs => xs.all (fun ys => ys.all p))=true ↔ ∀i j k,p (Cube.get v i j k)=true := by
  simp only [Tri.all_iff,Cube.get]

lemma leafValid_sound {T : DetTriangle} {n : Cell} {c : ProductCell}
    (hrep : Represents T n c) (w : Witness) (hv : leafValid n w=true) :
    ∃lam mu : ℝ,∀i j k,certForm T lam mu (c 0 i) (c 1 j) (c 2 k)≤0 := by
  change ((decide (0<n.den) && decide (0<w.den)) && _)=true at hv
  have hw : 0<w.den := of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).2
  have hall := (Cube.all_iff n.corners (satisfies n.den w)).mp (Bool.and_eq_true_iff.mp hv).2
  have hdR : (0:ℝ)<n.den := by exact_mod_cast hrep.1
  have hwR : (0:ℝ)<w.den := by exact_mod_cast hw
  let lp : ℝ:=w.lp
  let ln : ℝ:=w.ln
  let mp : ℝ:=w.mp
  let mn : ℝ:=w.mn
  let d : ℝ:=w.den
  refine ⟨(lp-ln)/d,(mp-mn)/d,?_⟩
  intro i j k
  let f:=Cube.get n.corners i j k
  have hi : 25*w.den*f.pair+(75*w.lp+25*w.mp)*n.den+25*w.ln*f.one+25*w.mn*f.three ≤
      (52*w.den+75*w.ln+25*w.mn)*n.den+25*w.lp*f.one+25*w.mp*f.three := of_decide_eq_true (hall i j k)
  have hiR : 25*d*(f.pair:ℝ)+(75*lp+25*mp)*n.den+25*ln*f.one+25*mn*f.three ≤
      (52*d+75*ln+25*mn)*n.den+25*lp*f.one+25*mp*f.three := by
    dsimp [lp,ln,mp,mn,d]
    exact_mod_cast hi
  have he1 : (f.one:ℝ)-3*n.den=(n.den:ℝ)*weightExp (w1 T) (c 0 i) (c 1 j) (c 2 k) := hrep.2 0 i j k
  have he3 : (f.three:ℝ)-n.den=(n.den:ℝ)*weightExp (w2 T) (c 0 i) (c 1 j) (c 2 k) := by simpa [Corner.eval,offset,Exact.moment,Exact.momentWeight,f] using hrep.2 1 i j k
  have he2 : (f.pair:ℝ)-n.den=(n.den:ℝ)*weightExp (w3 T) (c 0 i) (c 1 j) (c 2 k) := by simpa [Corner.eval,offset,Exact.moment,Exact.momentWeight,f] using hrep.2 2 i j k
  have he1' : (f.one:ℝ)=(n.den:ℝ)*weightExp (w1 T) (c 0 i) (c 1 j) (c 2 k)+3*n.den := by linarith
  have he3' : (f.three:ℝ)=(n.den:ℝ)*weightExp (w2 T) (c 0 i) (c 1 j) (c 2 k)+n.den := by linarith
  have he2' : (f.pair:ℝ)=(n.den:ℝ)*weightExp (w3 T) (c 0 i) (c 1 j) (c 2 k)+n.den := by linarith
  have he : (25*(n.den:ℝ)*d)*certForm T ((lp-ln)/d) ((mp-mn)/d) (c 0 i) (c 1 j) (c 2 k)=
      (25*d*(f.pair:ℝ)+(75*lp+25*mp)*n.den+25*ln*f.one+25*mn*f.three)-
      ((52*d+75*ln+25*mn)*n.den+25*lp*f.one+25*mp*f.three) := by
    simp only [certForm,twentySevenTwentyFifths]
    rw [he1',he3',he2']
    field_simp [show d≠0 from hwR.ne']
    ring
  have hfactor : (0:ℝ)<25*(n.den:ℝ)*d := by dsimp [d]; positivity
  apply (mul_le_mul_left hfactor).mp
  rw [mul_zero,he]
  linarith

theorem valid_sound (t : Trace) : ∀{T : DetTriangle}{n : Cell}{c : ProductCell},
    Represents T n c → valid n t=true → Nonempty (FullCertTree T c) := by
  induction t with
  | leaf w =>
    intro T n c hn hv
    obtain ⟨lam,mu,hc⟩:=leafValid_sound hn w hv
    exact ⟨FullCertTree.leaf lam mu hc⟩
  | split a i j l r hl hr =>
    intro T n c hn hv
    change ((decide (i≠j) && valid (NaturalExact.child n a i j) l) && valid (NaturalExact.child n a j i) r)=true at hv
    obtain ⟨⟨hij,hlv⟩,hrv⟩:=(Bool.and_eq_true_iff.mp hv).imp (fun h => Bool.and_eq_true_iff.mp h) id
    obtain ⟨tl⟩:=hl (hn.child a i j) hlv
    obtain ⟨tr⟩:=hr (hn.child a j i) hrv
    exact ⟨FullCertTree.split a i j (of_decide_eq_true hij) tl tr⟩
  | checkpoint cc t ih =>
    intro T n c hn hv
    obtain ⟨he,ht⟩:=Bool.and_eq_true_iff.mp hv
    have heq : n=cc := of_decide_eq_true he
    subst cc
    exact ih hn ht

theorem gapHolds_of_valid (w : Nat) (t : Trace) (h : valid (root w) t=true) :
    GapHolds (DetTriangle.ofPattern w) := by
  obtain ⟨tree⟩:=valid_sound t (represents_root w) h
  exact gapHolds_of_fullCertTree tree

end
end Paper15.NaturalExact
