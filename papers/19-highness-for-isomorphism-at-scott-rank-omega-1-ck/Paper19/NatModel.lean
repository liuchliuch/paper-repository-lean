import Paper19.CodedOperations
import Paper19.ComputableEnumeration

namespace Paper19

/-- Precisely the paper's fixed finite signature on the domain Nat. -/
structure NatModel where
  index : ℕ → Bool
  zero : ℕ
  named : ℕ
  succ : ℕ → ℕ
  proj : ℕ → ℕ
  level : ℕ → ℕ
  rel : ℕ × (ℕ × ℕ) → Bool

structure NatModel.Computable (M : NatModel) : Prop where
  index : _root_.Computable M.index
  succ : _root_.Computable M.succ
  proj : _root_.Computable M.proj
  level : _root_.Computable M.level
  rel : _root_.Computable M.rel

noncomputable def enumerateDomain (T : Tree) : ℕ → ℕ := Nat.nth (codedDomain T)
def rankInDomain (T : Tree) : ℕ → ℕ := Nat.count (codedDomain T)

@[simp] theorem enumerateDomain_mem (T : Tree) (n : ℕ) : codedDomain T (enumerateDomain T n) :=
  Nat.nth_mem_of_infinite (codedDomain_infinite T) n

@[simp] theorem rankInDomain_enumerate (T : Tree) (n : ℕ) : rankInDomain T (enumerateDomain T n) = n :=
  Nat.count_nth_of_infinite (codedDomain_infinite T) n

@[simp] theorem enumerateDomain_rank (T : Tree) {n : ℕ} (hn : codedDomain T n) :
    enumerateDomain T (rankInDomain T n) = n := Nat.nth_count hn

theorem enumerateDomain_computable (T : Tree) (hT : ComputablePred T.mem) : Computable (enumerateDomain T) :=
  nth_computable _ (codedDomain_computable T hT) (codedDomain_infinite T)

theorem rankInDomain_computable (T : Tree) (hT : ComputablePred T.mem) : Computable (rankInDomain T) :=
  count_computable _ (codedDomain_computable T hT)

/-- The increasing enumeration gives a genuine bijection with all Nat. -/
noncomputable def carrierEquivNat (T : Tree) : Carrier T ≃ ℕ where
  toFun x := rankInDomain T (rawCode x.val)
  invFun n := ⟨rawDecode T (enumerateDomain T n), enumerateDomain_mem T n⟩
  left_inv := by
    intro x
    apply Subtype.ext
    have hx : codedDomain T (rawCode x.val) := by simpa [codedDomain] using x.property
    simp [enumerateDomain_rank T hx]
  right_inv := by intro n; simp

@[simp] theorem enumerate_equiv (T : Tree) (x : Carrier T) :
    enumerateDomain T (carrierEquivNat T x) = rawCode x.val :=
  enumerateDomain_rank T (by simpa [codedDomain] using x.property)

noncomputable def natModel (T : Tree) (tag : Bool) : NatModel where
  index n := decide (enumerateDomain T n % 2 = 0)
  zero := rankInDomain T (rawCode (Dom.idx 0 : Dom T))
  named := rankInDomain T (rawCode (namedRoot T tag).val)
  succ n := rankInDomain T (codedSucc (enumerateDomain T n))
  proj n := rankInDomain T (codedProj T (enumerateDomain T n))
  level n := rankInDomain T (codedLevel (enumerateDomain T n))
  rel p := codedD T (enumerateDomain T p.1, enumerateDomain T p.2.1, enumerateDomain T p.2.2)

theorem natModel_computable (T : Tree) (hT : ComputablePred T.mem) (tag : Bool) :
    (natModel T tag).Computable := by
  have he := enumerateDomain_computable T hT
  have hr := rankInDomain_computable T hT
  have hi : PrimrecPred (fun n : ℕ => n%2=0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0)
  exact ⟨hi.decide.to_comp.comp he,
    hr.comp (codedSucc_computable.comp he), hr.comp ((codedProj_computable T).comp he),
    hr.comp (codedLevel_computable.comp he),
    (codedD_computable T hT).comp ((he.comp Computable.fst).pair
      ((he.comp (Computable.fst.comp Computable.snd)).pair (he.comp (Computable.snd.comp Computable.snd))))⟩

@[simp] theorem natModel_index (T : Tree) (tag : Bool) (x : Carrier T) :
    (natModel T tag).index (carrierEquivNat T x) = true ↔ Carrier.isIdx x := by
  simp only [natModel,enumerate_equiv,decide_eq_true_eq]
  cases x with
  | mk x hx => cases x <;> simp [rawCode,Carrier.isIdx,isIndex]

@[simp] theorem natModel_zero (T : Tree) (tag : Bool) :
    (natModel T tag).zero = carrierEquivNat T (Carrier.idx 0) := rfl

@[simp] theorem natModel_named (T : Tree) (tag : Bool) :
    (natModel T tag).named = carrierEquivNat T (namedRoot T tag) := rfl

@[simp] theorem natModel_succ (T : Tree) (tag : Bool) (x : Carrier T) :
    (natModel T tag).succ (carrierEquivNat T x) = carrierEquivNat T (Carrier.succ x) := by
  simp only [natModel,enumerate_equiv,codedSucc_correct]
  rfl

@[simp] theorem natModel_proj (T : Tree) (tag : Bool) (x : Carrier T) :
    (natModel T tag).proj (carrierEquivNat T x) = carrierEquivNat T (Carrier.projD x) := by
  simp only [natModel,enumerate_equiv,codedProj_correct]
  rfl

@[simp] theorem natModel_level (T : Tree) (tag : Bool) (x : Carrier T) :
    (natModel T tag).level (carrierEquivNat T x) = carrierEquivNat T (Carrier.levelOf x) := by
  simp only [natModel,enumerate_equiv,codedLevel_correct]
  rfl

@[simp] theorem natModel_rel (T : Tree) (tag : Bool) (k x y : Carrier T) :
    (natModel T tag).rel (carrierEquivNat T k,carrierEquivNat T x,carrierEquivNat T y)=true ↔
      Carrier.D k x y := by
  simp only [natModel,enumerate_equiv,codedD_correct]
  rfl

end Paper19
