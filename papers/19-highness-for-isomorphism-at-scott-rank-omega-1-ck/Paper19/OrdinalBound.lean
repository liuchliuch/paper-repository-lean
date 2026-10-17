import Paper19.EffectiveKB

namespace Paper19

structure RecursiveWellOrder where
  domain : Node → Prop
  domain_recursive : ComputablePred domain
  rel : Node → Node → Prop
  rel_recursive : ComputablePred (fun p : Node × Node => rel p.1 p.2)
  wellOrder : IsWellOrder {x : Node // domain x} (fun x y => rel x.val y.val)

noncomputable def RecursiveWellOrder.val (w : RecursiveWellOrder) : Ordinal := by
  letI := w.wellOrder
  exact Ordinal.type (fun x y : {x : Node // w.domain x} => w.rel x.val y.val)

def WMem (T : Tree) (n : ℕ) : Node → Prop
  | [] => True
  | c::tail =>
    let σ := Denumerable.ofNat Node c
    σ ∈ deadLevel (STree T) n ∧ (STree T).mem (σ ++ tail)

noncomputable def WTree (T : Tree) (hT : ComputablePred T.mem) (n : ℕ) : Tree where
  mem := WMem T n
  decMem := by
    intro v
    cases v with
    | nil => exact isTrue trivial
    | cons c tail =>
      letI : DecidablePred (fun σ => σ ∈ deadLevel (STree T) n) := (deadLevel_computable T hT n).choose
      exact inferInstanceAs (Decidable (_ ∧ _))
  mem_nil := trivial
  mem_prefix := by
    intro σ τ hτ hp
    cases σ with
    | nil => trivial
    | cons c tail =>
      obtain ⟨rest,rfl⟩ := hp
      change _ ∧ (STree T).mem (Denumerable.ofNat Node c ++ (tail ++ rest)) at hτ
      refine ⟨hτ.1,(STree T).mem_prefix hτ.2 ?_⟩
      exact ⟨rest,by simp [List.append_assoc]⟩

theorem WMem_computable (T : Tree) (hT : ComputablePred T.mem) (n : ℕ) : ComputablePred (WMem T n) := by
  have he : PrimrecPred (fun v : Node => v=[]) := Primrec.eq.comp Primrec.id (Primrec.const [])
  have hs : Primrec (fun v : Node => Denumerable.ofNat Node (v.getD 0 0)) :=
    (Primrec.ofNat Node).comp ((Primrec.list_getD 0).comp Primrec.id (Primrec.const 0))
  have hd := (deadLevel_computable T hT n).comp' hs.to_comp
  have hm := (STree_computable T hT).comp'
    (Computable.list_append.comp hs.to_comp Primrec.list_tail.to_comp)
  exact (he.computablePred.or' (hd.and' hm)).of_eq (fun v => by cases v <;> simp [WMem])

theorem WTree_no_path (T : Tree) (hT : ComputablePred T.mem) (n : ℕ) :
    ¬∃ g, (WTree T hT n).IsPath g := by
  rintro ⟨g,hg⟩
  let σ := Denumerable.ofNat Node (g 0)
  have hnodes (k : ℕ) : σ ∈ deadLevel (STree T) n ∧
      (STree T).mem (σ ++ streamPrefix (fun i => g (i+1)) k) := by
    have h := hg (k+1)
    rw [List.ofFn_succ] at h
    exact h
  let a : ℕ → Node := fun k => σ ++ streamPrefix (fun i => g (i+1)) k
  have hlen (k : ℕ) : (a k).length = σ.length+k := by simp [a]
  have hp (k : ℕ) : a k <+: a (k+1) := by
    obtain ⟨rest,hr⟩ := streamPrefix_prefix (fun i => g (i+1)) (Nat.le_succ k)
    exact ⟨rest,by simpa [a,List.append_assoc] using congrArg (List.append σ) hr⟩
  have hm (k : ℕ) : (STree T).mem (a k) := (hnodes k).2
  apply (hnodes 0).1.2.2
  refine ⟨chainStream a,chainStream_path (STree T) a hlen hp hm,?_⟩
  simpa [a,streamPrefix] using (chainStream_prefix a hlen hp 0).symm

theorem tree_root_accessible (S : Tree) (hn : ¬∃ g, S.IsPath g) : Acc (fun y x => TreeChild S x y) [] := by
  classical
  by_contra h
  obtain ⟨a,ha0,ha⟩ := not_acc_iff_exists_descending_chain.mp h
  have hlen (k : ℕ) : (a k).length=0+k := by
    induction k with
    | zero => simp [ha0]
    | succ k ih => rw [(ha k).2.1,ih]; omega
  have hp (k : ℕ) : a k <+: a (k+1) := by
    rw [← (ha k).2.2]; exact List.take_prefix _ _
  have hm (k : ℕ) : S.mem (a k) := by
    rw [← (ha k).2.2]
    exact S.mem_prefix (ha k).1 (List.take_prefix _ _)
  exact hn ⟨chainStream a,chainStream_path S a hlen hp hm⟩

theorem WTree_wellOrder (T : Tree) (hT : ComputablePred T.mem) (n : ℕ) :
    IsWellOrder {v : Node // (WTree T hT n).mem v} (fun x y => KB x.val y.val) where
  trichotomous x y := by
    rcases KB.trichotomy x.val y.val with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr h)
  trans _ _ _ := KB.trans
  wf := KB_subtree_wf (tree_root_accessible (WTree T hT n) (WTree_no_path T hT n))

def levelWellOrder (T : Tree) (hT : ComputablePred T.mem) (n : ℕ) : RecursiveWellOrder :=
  ⟨WMem T n,WMem_computable T hT n,KB,KB_computable,WTree_wellOrder T hT n⟩

theorem TreeChild.eq_append {S : Tree} {x y : Node} (h : TreeChild S x y) : ∃ a, y=x++[a] := by
  have hp : x <+: y := by rw [← h.2.2]; exact List.take_prefix _ _
  obtain ⟨rest,rfl⟩ := hp
  have hr : rest.length=1 := by have hh := h.2.1; simp only [List.length_append] at hh; omega
  obtain ⟨a,rfl⟩ := List.length_eq_one.mp hr
  exact ⟨a,rfl⟩

theorem KB.append_one (x : Node) (a : ℕ) : KB (x++[a]) x := by
  induction x with
  | nil => trivial
  | cons b xs ih => exact Or.inr ⟨rfl,ih⟩

/-- The paper's actual KB-order bound, in the ordinary computable-well-order
presentation of ordinals, independent of the recursive rank-test notation. -/
theorem lemma3_KB_bound (T : Tree) (hT : ComputablePred T.mem) (n : ℕ) :
    ∃ w : RecursiveWellOrder, ∀ σ ∈ deadLevel (STree T) n,
      ∀ hs : Acc (fun τ σ => SChild T σ τ) σ, hs.rank < w.val := by
  let W := WTree T hT n
  let R := fun x y : {v : Node // W.mem v} => KB x.val y.val
  letI : IsWellOrder {v : Node // W.mem v} R := WTree_wellOrder T hT n
  refine ⟨levelWellOrder T hT n,?_⟩
  intro σ hd hs
  let code := @Encodable.encode Node (inferInstance : Denumerable Node).toEncodable σ
  have hw (tail : Node) (hm : (STree T).mem (σ++tail)) : W.mem (code::tail) := by
    change _ ∧ _
    simpa [code] using And.intro hd hm
  have aux : ∀ (τ : Node) (hτ : Acc (fun τ σ => SChild T σ τ) τ) (tail : Node)
      (he : τ=σ++tail) (hm : (STree T).mem τ),
      hτ.rank ≤ Ordinal.typein R ⟨code::tail,hw tail (he ▸ hm)⟩ := by
    intro τ hτ
    induction hτ with
    | intro τ hτ ih =>
      intro tail he hm
      rw [Acc.rank_eq]
      apply Ordinal.iSup_le
      intro y
      obtain ⟨a,ha⟩ := TreeChild.eq_append (show TreeChild (STree T) τ y.val from y.property)
      have hy : y.val = σ++(tail++[a]) := by rw [ha,he,List.append_assoc]
      have hyr := ih y.val y.property (tail++[a]) hy y.property.1
      have hk : Ordinal.typein R ⟨code::(tail++[a]),hw _ (hy ▸ y.property.1)⟩ <
          Ordinal.typein R ⟨code::tail,hw _ (he ▸ hm)⟩ :=
        (Ordinal.typein_lt_typein R).mpr (KB.append_one (code::tail) a)
      exact Order.succ_le_iff.mpr (hyr.trans_lt hk)
  have hm : (STree T).mem σ := hd.1
  have he : σ=σ++[] := by simp
  have hb := aux σ hs [] he hm
  exact hb.trans_lt (Ordinal.typein_lt_type R ⟨code::[],hw [] (he ▸ hm)⟩)

end Paper19
