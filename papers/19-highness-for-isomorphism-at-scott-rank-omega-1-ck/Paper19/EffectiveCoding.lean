import Paper19.EffectiveNormalForm

namespace Paper19

namespace Effective

def addFirst (z : ℕ) : Node → Node
  | [] => []
  | a :: l => (a + z) :: l

theorem blocksAux_add (η : Bin) (z : ℕ) :
    completedBlocksAux η z = addFirst z (completedBlocks η) := by
  induction η generalizing z with
  | nil => rfl
  | cons b l ih =>
    cases b with
    | true => simp [completedBlocksAux, completedBlocks, addFirst]
    | false =>
      change completedBlocksAux l (z + 1) = addFirst z (completedBlocksAux l 1)
      rw [ih, ih]
      cases completedBlocks l <;> simp [addFirst] <;> omega

theorem addFirst_primrec : Primrec₂ addFirst := by
  have h : Primrec (fun p : ℕ × Node => List.casesOn (motive := fun _ => Node) p.2 [] (fun a l => (a + p.1) :: l)) :=
    Primrec.list_casesOn Primrec.snd (Primrec.const [])
      (Primrec.to₂ (Primrec.list_cons.comp
        (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd)))
  exact h.to₂.of_eq (fun z l => by cases l <;> rfl)

theorem blocks_primrec : Primrec completedBlocks := by
  have h := Primrec.list_rec (α := Bin) (β := Bool) (σ := Node)
    Primrec.id (Primrec.const [])
    (Primrec.to₂ (Primrec.cond (Primrec.fst.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.const 0) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (addFirst_primrec.comp (Primrec.const 1) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  apply h.of_eq
  intro η
  induction η with
  | nil => rfl
  | cons b l ih =>
    change (bif b then 0 :: (List.rec (motive := fun _ => Node) [] (fun b l IH => bif b then 0 :: IH else addFirst 1 IH) l)
      else addFirst 1 (List.rec (motive := fun _ => Node) [] (fun b l IH => bif b then 0 :: IH else addFirst 1 IH) l)) = _
    change (List.rec (motive := fun _ => Node) [] (fun b l IH => bif b then 0 :: IH else addFirst 1 IH) l) = _ at ih
    rw [ih]
    cases b
    · exact (blocksAux_add l 1).symm
    · rfl

/-- Take implemented by bounded tabulation, with an explicit primitive-
recursive proof on the standard list encoding. -/
def takeNode (p : Node × ℕ) : Node :=
  (List.range (min p.2 p.1.length)).map (fun i => p.1.getD i 0)

theorem takeNode_eq (p : Node × ℕ) : takeNode p = p.1.take p.2 := by
  apply List.ext_getElem
  · simp [takeNode]
  · intro i hi hi'
    have hiL : i < p.1.length := by simp [takeNode] at hi; omega
    simp [takeNode, List.getElem_take, List.getElem?_eq_getElem hiL]

theorem takeNode_primrec : Primrec takeNode :=
  Primrec.list_map (Primrec.list_range.comp
    (Primrec.nat_min.comp Primrec.snd (Primrec.list_length.comp Primrec.fst)))
    (Primrec.to₂ ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd))

def bitList (p : Node × ℕ) : Bin :=
  if p.2 ≤ p.1.length then
    (List.range p.2).map (fun i => decide (p.1.getD i 0 % 2 = 1)) else []

theorem bitList_eq (p : Node × ℕ) : bitList p = bitPrefix p.1 p.2 := by
  unfold bitList bitPrefix
  split_ifs with h
  · apply List.ext_getElem
    · simp
    · intro i hi hi'
      have hiL : i < p.1.length := by simp at hi; omega
      simp [bitsOf, List.getElem?_eq_getElem hiL, List.get_eq_getElem]
  · rfl

theorem bitList_primrec : Primrec bitList := by
  apply Primrec.ite (Primrec.nat_le.comp Primrec.snd (Primrec.list_length.comp Primrec.fst))
    ?_ (Primrec.const [])
  apply Primrec.list_map (Primrec.list_range.comp Primrec.snd)
  exact Primrec.to₂ ((Primrec.eq.comp
    (Primrec.nat_mod.comp ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.const 2)) (Primrec.const 1)).decide)

end Effective

variable {α β : Type} [Primcodable α] [Primcodable β]

theorem _root_.ComputablePred.comp' {p : β → Prop} (hp : ComputablePred p) {f : α → β} (hf : Computable f) :
    ComputablePred (fun x => p (f x)) := by
  letI := hp.choose
  exact (hp.decide.comp hf).computablePred

theorem _root_.ComputablePred.and' {p q : α → Prop} (hp : ComputablePred p) (hq : ComputablePred q) :
    ComputablePred (fun x => p x ∧ q x) := by
  classical
  exact ((Primrec.and.to_comp.comp hp.decide hq.decide).of_eq (by simp)).computablePred

theorem _root_.ComputablePred.boundedAll {p : α × ℕ → Prop} (hp : ComputablePred p) {f : α → ℕ}
    (hf : Computable f) : ComputablePred (fun a => ∀ i < f a, p (a, i)) := by
  classical
  have hb : Computable (fun a => Nat.rec (motive := fun _ => Bool) true (fun i b => b && decide (p (a, i))) (f a)) :=
    Computable.nat_rec hf (Computable.const true)
      (Computable.to₂ (Primrec.and.to_comp.comp (Computable.snd.comp Computable.snd)
        (hp.decide.comp (Computable.fst.pair (Computable.fst.comp Computable.snd)))))
  have hb' : ComputablePred (fun a =>
      (Nat.rec (motive := fun _ => Bool) true (fun i b => b && decide (p (a, i))) (f a)) = true) :=
    ⟨inferInstance, by simpa using hb⟩
  apply hb'.of_eq
  intro a
  induction f a with
  | zero => simp
  | succ n ih => simp [Nat.rec_add_one, ih, Nat.forall_lt_succ]

/-- Membership in S is computable from membership in T. -/
theorem STree_computable (T : Tree) (hT : ComputablePred T.mem) :
    ComputablePred (STree T).mem := by
  classical
  have hrt : ComputablePred (fun p : Bin × ℕ => RT T p.1 p.2) := by
    have hlen : PrimrecPred (fun p : Bin × ℕ =>
        p.2 + 1 ≤ (completedBlocks p.1).length) :=
      Primrec.nat_le.comp (Primrec.succ.comp Primrec.snd)
        (Primrec.list_length.comp (Effective.blocks_primrec.comp Primrec.fst))
    have hm := hT.comp' (Effective.takeNode_primrec.comp
      ((Effective.blocks_primrec.comp Primrec.fst).pair (Primrec.succ.comp Primrec.snd))).to_comp
    exact (hlen.computablePred.and' hm).of_eq (by simp [RT, Effective.takeNode_eq])
  let q : Node × ℕ → ℕ := fun p => p.1.getD p.2 0 / 2
  have hq : Primrec q := Primrec.nat_div.comp
    ((Primrec.list_getD 0).comp Primrec.fst Primrec.snd) (Primrec.const 2)
  have hr : ComputablePred (fun p : Node × ℕ =>
      RT T (bitPrefix p.1 (q p)) p.2) :=
    (hrt.comp' ((Effective.bitList_primrec.comp (Primrec.fst.pair hq)).pair Primrec.snd).to_comp).of_eq
      (by simp [Effective.bitList_eq])
  have hb : ComputablePred (fun p : Node × ℕ => q p ≤ p.1.length) :=
    (Primrec.nat_le.comp hq (Primrec.list_length.comp Primrec.fst)).computablePred
  have hc := (hb.and' hr.not).not
  have ha := hc.boundedAll Primrec.list_length.to_comp
  apply ha.of_eq
  intro σ
  simp only [not_and, not_not] 
  constructor
  · intro h i hi
    have hi' : i.val < σ.length := i.is_lt
    have hd : σ.getD i.val 0 = σ.get i := by
      simp [List.getElem?_eq_getElem hi', List.get_eq_getElem]
    have hq' : q (σ, i.val) ≤ σ.length := by simpa [q, hd, quotsOf] using hi
    simpa [q, hd, quotsOf] using h i.val hi' hq'
  · intro h i hi hq'
    have hd : σ.getD i 0 = σ.get ⟨i, hi⟩ := by
      simp [List.getElem?_eq_getElem hi, List.get_eq_getElem]
    have hq'' : quotsOf σ ⟨i, hi⟩ ≤ σ.length := by simpa [q, quotsOf, List.get_eq_getElem, List.getElem?_eq_getElem hi] using hq'
    simpa [q, quotsOf, List.get_eq_getElem, List.getElem?_eq_getElem hi] using h ⟨i, hi⟩ hq''

end Paper19
