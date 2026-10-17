import Paper19.UniformEnumeration
import Paper19.NatModel

namespace Paper19
open UniformOracleComputable
open scoped symmDiff

/-- Characteristic oracle on the fixed standard coding of finite sequences. -/
def treeOracle (T : Tree) : Stream := fun c =>
  if T.mem (Denumerable.ofNat Node c) then 1 else 0

@[simp] theorem treeOracle_encode (T : Tree) (v : Node) :
    treeOracle T (Encodable.encode v)=1 ↔ T.mem v := by
  simp [treeOracle]

def rtProgram (o : Stream) (p : Bin × ℕ) : Bool :=
  decide (p.2+1 ≤ (completedBlocks p.1).length) &&
    decide (o (Encodable.encode (Effective.takeNode (completedBlocks p.1,p.2+1)))=1)

theorem rtProgram_uniform : UniformOracleComputable rtProgram := by
  have hb : Primrec (fun p : Bin × ℕ => completedBlocks p.1) := Effective.blocks_primrec.comp Primrec.fst
  have hn : Primrec (fun p : Bin × ℕ => p.2+1) := Primrec.succ.comp Primrec.snd
  have hl : Primrec (fun p : Bin × ℕ => decide (p.2+1 ≤ (completedBlocks p.1).length)) :=
    (Primrec.nat_le.comp hn (Primrec.list_length.comp hb)).decide
  have hp : Primrec (fun p : Bin × ℕ => Encodable.encode
      (Effective.takeNode (completedBlocks p.1,p.2+1))) :=
    Primrec.encode.comp (Effective.takeNode_primrec.comp (hb.pair hn))
  have hq : UniformOracleComputable (fun o (p : Bin × ℕ) => o (Encodable.encode
      (Effective.takeNode (completedBlocks p.1,p.2+1)))) :=
    UniformOracleComputable.comp (f := fun o => o)
      (g := fun _ (p : Bin × ℕ) => Encodable.encode (Effective.takeNode (completedBlocks p.1,p.2+1)))
      query (base hp.to_comp)
  have he : UniformOracleComputable (fun _ (n : ℕ) => decide (n=1)) :=
    base (Primrec.eq.comp Primrec.id (Primrec.const 1)).decide.to_comp
  have heq := UniformOracleComputable.comp (f := fun _ (n : ℕ) => decide (n=1))
    (g := fun o (p : Bin × ℕ) => o (Encodable.encode (Effective.takeNode (completedBlocks p.1,p.2+1)))) he hq
  have hpair := UniformOracleComputable.pair
    (f := fun _ (p : Bin × ℕ) => decide (p.2+1 ≤ (completedBlocks p.1).length))
    (g := fun o (p : Bin × ℕ) => decide (o (Encodable.encode (Effective.takeNode (completedBlocks p.1,p.2+1)))=1))
    (base hl.to_comp) heq
  have hres := UniformOracleComputable.comp
    (f := fun _ (p : Bool × Bool) => p.1 && p.2)
    (g := fun o (p : Bin × ℕ) => (decide (p.2+1 ≤ (completedBlocks p.1).length),
      decide (o (Encodable.encode (Effective.takeNode (completedBlocks p.1,p.2+1)))=1)))
    (base Primrec.and.to_comp) hpair
  exact hres.of_eq (fun _ _ => rfl)

@[simp] theorem rtProgram_correct (T : Tree) (p : Bin × ℕ) :
    rtProgram (treeOracle T) p=true ↔ RT T p.1 p.2 := by
  simp [rtProgram,RT,Effective.takeNode_eq]

def sProgram (o : Stream) (v : Node) : Bool :=
  foldAll (fun o p => bif decide (p.1.getD p.2 0 / 2 ≤ p.1.length) then
    rtProgram o (Effective.bitList (p.1,p.1.getD p.2 0 / 2),p.2) else true)
    (fun _ v => v.length) o v

theorem sProgram_uniform : UniformOracleComputable sProgram := by
  have hq : Primrec (fun p : Node × ℕ => p.1.getD p.2 0 / 2) :=
    Primrec.nat_div.comp ((Primrec.list_getD 0).comp Primrec.fst Primrec.snd) (Primrec.const 2)
  have hc := (Primrec.nat_le.comp hq (Primrec.list_length.comp Primrec.fst)).decide
  have hr := rtProgram_uniform.comp (base ((Effective.bitList_primrec.comp
    (Primrec.fst.pair hq)).pair Primrec.snd).to_comp)
  exact foldAll_uniform (cond (base hc.to_comp) hr (const true)) (base Primrec.list_length.to_comp)

@[simp] theorem sProgram_correct (T : Tree) (v : Node) :
    sProgram (treeOracle T) v=true ↔ (STree T).mem v := by
  rw [sProgram,foldAll_true]
  constructor
  · intro h i hi
    have hb : v.getD i.val 0 / 2 ≤ v.length := by
      simpa [quotsOf,List.get_eq_getElem,List.getElem?_eq_getElem i.is_lt] using hi
    have hh := h i.val i.is_lt
    simp only [decide_eq_true hb,Bool.cond_true,rtProgram_correct] at hh
    simpa [Effective.bitList_eq,quotsOf,List.get_eq_getElem,List.getElem?_eq_getElem i.is_lt] using hh
  · intro h i hi
    by_cases hb : v.getD i 0 / 2 ≤ v.length
    · simp only [decide_eq_true hb,Bool.cond_true,rtProgram_correct]
      have hh := h ⟨i,hi⟩ (by simpa [quotsOf,List.get_eq_getElem,List.getElem?_eq_getElem hi] using hb)
      simpa [Effective.bitList_eq,quotsOf,List.get_eq_getElem,List.getElem?_eq_getElem hi] using hh
    · rw [decide_eq_false hb]; rfl

def gProgram (o : Stream) (p : ℕ × Finset Node) : Bool :=
  listAllProgram ([] : Node) (fun p => FiniteCoding.nodes p.2)
    (fun o q => sProgram o q.2 && decide (q.2.length=q.1.1)) o p

theorem gProgram_uniform : UniformOracleComputable gProgram := by
  have hl : Primrec (fun q : (ℕ × Finset Node) × Node => decide (q.2.length=q.1.1)) :=
    (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)).decide
  have hs := UniformOracleComputable.comp (f := sProgram)
    (g := fun _ (q : (ℕ × Finset Node) × Node) => q.2) sProgram_uniform
    (base (f := fun q : (ℕ × Finset Node) × Node => q.2) Computable.snd)
  have hand : UniformOracleComputable (fun _ (p : Bool × Bool) => p.1 && p.2) := base Primrec.and.to_comp
  have hc := UniformOracleComputable.comp (f := fun _ (p : Bool × Bool) => p.1 && p.2)
      (g := fun o (q : (ℕ × Finset Node) × Node) => (sProgram o q.2,decide (q.2.length=q.1.1))) hand
      (UniformOracleComputable.pair
        (f := fun o (q : (ℕ × Finset Node) × Node) => sProgram o q.2)
        (g := fun _ (q : (ℕ × Finset Node) × Node) => decide (q.2.length=q.1.1)) hs (base hl.to_comp))
  have hres := listAllProgram_uniform (l := fun p : ℕ × Finset Node => FiniteCoding.nodes p.2)
    (p := fun o q => sProgram o q.2 && decide (q.2.length=q.1.1)) []
    (Computable.comp (f := FiniteCoding.nodes) (g := fun p : ℕ × Finset Node => p.2)
      FiniteCoding.nodes_primrec.to_comp Computable.snd) hc
  exact hres.of_eq (fun _ _ => rfl)

@[simp] theorem gProgram_correct (T : Tree) (p : ℕ × Finset Node) :
    gProgram (treeOracle T) p=true ↔ GMem T p.1 p.2 := by
  simp [gProgram,listAllProgram_true,GMem,level]

def domainProgram (o : Stream) (c : ℕ) : Bool :=
  bif decide (c%2=0) then true else gProgram o (decodeVector c)

theorem domainProgram_uniform : UniformOracleComputable domainProgram := by
  exact cond (base (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
    (Primrec.const 0)).decide.to_comp) (const true)
    (gProgram_uniform.comp (base decodeVector_primrec.to_comp))

@[simp] theorem domainProgram_correct (T : Tree) (c : ℕ) :
    domainProgram (treeOracle T) c=true ↔ codedDomain T c := by
  by_cases h : c%2=0 <;> simp [domainProgram,codedDomain,rawDecode,GoodDom,decodeVector,h]

theorem domainProgram_infinite (o : Stream) : Set.Infinite {c | domainProgram o c=true} := by
  apply Set.infinite_of_injective_forall_mem (f := fun k => 2*k)
  · intro a b h; change 2*a=2*b at h; omega
  · intro k; simp [domainProgram]

noncomputable def enumProgram := nthProgram domainProgram
noncomputable def rankProgram := countProgram domainProgram

theorem enumProgram_uniform : UniformOracleComputable enumProgram :=
  nthProgram_uniform domainProgram_uniform domainProgram_infinite

theorem rankProgram_uniform : UniformOracleComputable rankProgram := countProgram_uniform domainProgram_uniform

@[simp] theorem enumProgram_correct (T : Tree) : enumProgram (treeOracle T)=enumerateDomain T := by
  unfold enumProgram nthProgram enumerateDomain
  congr 1
  funext c
  exact propext (domainProgram_correct T c)

@[simp] theorem rankProgram_correct (T : Tree) : rankProgram (treeOracle T)=rankInDomain T := by
  unfold rankProgram countProgram rankInDomain
  congr 1
  funext c
  exact propext (domainProgram_correct T c)

/-- Tree-independent finite part of the D test. -/
def dShape (p : ℕ × (ℕ × ℕ)) : Bool :=
  let K := decodeVector p.1
  let X := decodeVector p.2.1
  let Y := decodeVector p.2.2
  decide (p.1%2=0 ∧ p.2.1%2≠0 ∧ p.2.2%2≠0 ∧ K.1=X.1 ∧ Y.1=X.1 ∧ Y.2 = X.2 ∆ K.2)

theorem dShape_computable : Computable dShape := by
  let K := fun p : ℕ × (ℕ × ℕ) => decodeVector p.1
  let X := fun p : ℕ × (ℕ × ℕ) => decodeVector p.2.1
  let Y := fun p : ℕ × (ℕ × ℕ) => decodeVector p.2.2
  have hk : Primrec K := decodeVector_primrec.comp Primrec.fst
  have hx : Primrec X := decodeVector_primrec.comp (Primrec.fst.comp Primrec.snd)
  have hy : Primrec Y := decodeVector_primrec.comp (Primrec.snd.comp Primrec.snd)
  have htK : PrimrecPred (fun p : ℕ × (ℕ × ℕ) => p.1%2=0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2)) (Primrec.const 0)
  have htX : PrimrecPred (fun p : ℕ × (ℕ × ℕ) => p.2.1%2≠0) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 2)) (Primrec.const 0)).not
  have htY : PrimrecPred (fun p : ℕ × (ℕ × ℕ) => p.2.2%2≠0) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 2)) (Primrec.const 0)).not
  have hnK := (Primrec.eq.comp (Primrec.fst.comp hk) (Primrec.fst.comp hx)).computablePred
  have hnY := (Primrec.eq.comp (Primrec.fst.comp hy) (Primrec.fst.comp hx)).computablePred
  have hdiff := FiniteCoding.symmDiff_computable.comp ((Primrec.snd.comp hx).pair (Primrec.snd.comp hk)).to_comp
  have he := (Primrec.eq.decide.to_comp.comp (Primrec.snd.comp hy).to_comp hdiff).computablePred
  exact (htK.computablePred.and' (htX.computablePred.and' (htY.computablePred.and'
    (hnK.and' (hnY.and' he))))).decide

def dProgram (o : Stream) (p : ℕ × (ℕ × ℕ)) : Bool :=
  dShape p && gProgram o ((decodeVector p.2.1).1,(decodeVector p.1).2)

theorem dProgram_uniform : UniformOracleComputable dProgram := by
  have hi : Primrec (fun p : ℕ × (ℕ × ℕ) => ((decodeVector p.2.1).1,(decodeVector p.1).2)) :=
    (Primrec.fst.comp (decodeVector_primrec.comp (Primrec.fst.comp Primrec.snd))).pair
      (Primrec.snd.comp (decodeVector_primrec.comp Primrec.fst))
  have hg : UniformOracleComputable (fun o (p : ℕ × (ℕ × ℕ)) =>
      gProgram o ((decodeVector p.2.1).1,(decodeVector p.1).2)) :=
    UniformOracleComputable.comp (f := gProgram)
      (g := fun _ (p : ℕ × (ℕ × ℕ)) => ((decodeVector p.2.1).1,(decodeVector p.1).2))
      gProgram_uniform (base hi.to_comp)
  exact UniformOracleComputable.comp (f := fun _ (p : Bool × Bool) => p.1 && p.2)
    (g := fun o p => (dShape p,gProgram o ((decodeVector p.2.1).1,(decodeVector p.1).2)))
    (base Primrec.and.to_comp) ((base dShape_computable).pair hg)

@[simp] theorem dProgram_correct (T : Tree) (p : ℕ × (ℕ × ℕ)) :
    dProgram (treeOracle T) p=codedD T p := by
  apply Bool.eq_iff_iff.mpr
  simp only [dProgram,Bool.and_eq_true,gProgram_correct,dShape,codedD,decide_eq_true_eq]
  tauto

def rootTree : Tree where
  mem v := v=[]
  decMem _ := inferInstance
  mem_nil := rfl
  mem_prefix := by intro σ τ ht hp; subst τ; exact List.eq_nil_of_length_eq_zero (by have := hp.length_le; simp_all)

/-- A finite collection of fixed oracle programs for the fixed finite language. -/
structure ModelPrograms where
  index : Stream → ℕ → Bool
  zero : Stream → Unit → ℕ
  named : Stream → Unit → ℕ
  succ : Stream → ℕ → ℕ
  proj : Stream → ℕ → ℕ
  level : Stream → ℕ → ℕ
  rel : Stream → ℕ × (ℕ × ℕ) → Bool

structure ModelPrograms.Uniform (P : ModelPrograms) : Prop where
  index : UniformOracleComputable P.index
  zero : UniformOracleComputable P.zero
  named : UniformOracleComputable P.named
  succ : UniformOracleComputable P.succ
  proj : UniformOracleComputable P.proj
  level : UniformOracleComputable P.level
  rel : UniformOracleComputable P.rel

noncomputable def constructorPrograms (tag : Bool) : ModelPrograms where
  index o n := decide (enumProgram o n % 2=0)
  zero o _ := rankProgram o 0
  named o _ := rankProgram o (if tag then 2*encIndex 0 {[]}+1 else 2*encIndex 0 ∅+1)
  succ o n := rankProgram o (codedSucc (enumProgram o n))
  proj o n := rankProgram o (codedProj rootTree (enumProgram o n))
  level o n := rankProgram o (codedLevel (enumProgram o n))
  rel o p := dProgram o (enumProgram o p.1,enumProgram o p.2.1,enumProgram o p.2.2)

theorem constructorPrograms_uniform (tag : Bool) : (constructorPrograms tag).Uniform := by
  have hi := (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0)).decide.to_comp
  exact ⟨(base hi).comp enumProgram_uniform,
    rankProgram_uniform.comp (const 0),rankProgram_uniform.comp (const _),
    rankProgram_uniform.comp ((base codedSucc_computable).comp enumProgram_uniform),
    rankProgram_uniform.comp ((base (codedProj_computable rootTree)).comp enumProgram_uniform),
    rankProgram_uniform.comp ((base codedLevel_computable).comp enumProgram_uniform),
    dProgram_uniform.comp ((enumProgram_uniform.comp fst).pair
      ((enumProgram_uniform.comp (fst.comp snd)).pair (enumProgram_uniform.comp (snd.comp snd))))⟩

noncomputable def ModelPrograms.run (P : ModelPrograms) (o : Stream) : NatModel where
  index := P.index o
  zero := P.zero o ()
  named := P.named o ()
  succ := P.succ o
  proj := P.proj o
  level := P.level o
  rel := P.rel o

/-- One constructor independent of T; its specialization is exactly the
natural-number presentation used in Theorem 1. -/
theorem constructorPrograms_correct (T : Tree) (tag : Bool) :
    (constructorPrograms tag).run (treeOracle T)=natModel T tag := by
  cases tag <;> simp only [ModelPrograms.run,constructorPrograms,enumProgram_correct,rankProgram_correct,
    natModel,dProgram_correct]
  all_goals rfl

end Paper19
