import Paper19.DecidablePresentation
import Paper19.FiniteOperations

namespace Paper19
open scoped symmDiff

theorem _root_.ComputablePred.listAll {α β : Type} [Primcodable α] [Primcodable β]
    (d : β) {f : α → List β} (hf : Computable f) {p : α × β → Prop}
    (hp : ComputablePred p) : ComputablePred (fun a => ∀ b ∈ f a, p (a,b)) := by
  have hi := hp.comp' (Computable.fst.pair
    ((Primrec.list_getD d).to_comp.comp (hf.comp Computable.fst) Computable.snd))
  have ha := hi.boundedAll (Computable.list_length.comp hf)
  apply ha.of_eq
  intro a
  rw [List.forall_mem_iff_getElem]
  constructor
  · intro h i hi
    simpa only [List.getD_eq_getElem _ d hi] using h i hi
  · intro h i hi
    simpa only [List.getD_eq_getElem _ d hi] using h i hi

theorem GMem_computable (T : Tree) (hT : ComputablePred T.mem) :
    ComputablePred (fun p : ℕ × Finset Node => GMem T p.1 p.2) := by
  have hm := (STree_computable T hT).comp'
    (Computable.snd : Computable (fun p : (ℕ × Finset Node) × Node => p.2))
  have hl : PrimrecPred (fun p : (ℕ × Finset Node) × Node => p.2.length = p.1.1) :=
    Primrec.eq.comp (Primrec.list_length.comp Primrec.snd) (Primrec.fst.comp Primrec.fst)
  have ha := (hm.and' hl.computablePred).listAll ([] : Node)
    (FiniteCoding.nodes_primrec.comp Primrec.snd).to_comp
  -- listAll's list argument is fixed by the explicit type below.
  apply ha.of_eq
  rintro ⟨n,F⟩
  simp [GMem, level]

@[simp] theorem twice_add_one_div_two (n : ℕ) : (2*n+1)/2 = n := by omega

/-- A computable bijective coding of the unrestricted tagged domain. -/
def rawCode {T : Tree} : Dom T → ℕ
  | .idx k => 2*k
  | .vec n F => 2 * encIndex n F + 1

def rawDecode (T : Tree) (code : ℕ) : Dom T :=
  if code % 2 = 0 then .idx (code/2)
  else .vec (decodeIndex (code/2)).1 (decodeIndex (code/2)).2

@[simp] theorem rawDecode_rawCode {T : Tree} (x : Dom T) : rawDecode T (rawCode x) = x := by
  cases x with
  | idx k => simp [rawCode,rawDecode]
  | vec n F => simp [rawCode,rawDecode]

@[simp] theorem rawCode_rawDecode (T : Tree) (code : ℕ) : rawCode (rawDecode T code) = code := by
  unfold rawDecode
  split_ifs with h
  · simp only [rawCode]; omega
  · simp only [rawCode,encIndex_decodeIndex]
    have hm := Nat.mod_lt code (by decide : 0 < 2)
    omega

theorem decodeIndex_primrec : Primrec decodeIndex :=
  Primrec.fst.comp Primrec.unpair |>.pair
    ((Primrec.ofNat (Finset Node)).comp (Primrec.snd.comp Primrec.unpair))

theorem encIndex_primrec : Primrec (fun p : ℕ × Finset Node => encIndex p.1 p.2) :=
  Primrec₂.natPair.comp Primrec.fst (Primrec.encode.comp Primrec.snd)

/-- Decidable coded domain, uniformly using only membership in S. -/
def codedDomain (T : Tree) (code : ℕ) : Prop := GoodDom (rawDecode T code)

instance codedDomain.decidable (T : Tree) (code : ℕ) : Decidable (codedDomain T code) :=
  GoodDom.decidable (rawDecode T code)

theorem codedDomain_computable (T : Tree) (hT : ComputablePred T.mem) : ComputablePred (codedDomain T) := by
  have hi : PrimrecPred (fun code : ℕ => code % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0)
  have hd := (GMem_computable T hT).comp'
    (decodeIndex_primrec.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2))).to_comp
  exact (hi.computablePred.or' hd).of_eq (fun code => by
    by_cases h : code % 2 = 0 <;> simp [codedDomain,rawDecode,GoodDom,h])

/-- The index sort witnesses that the coded domain is infinite. -/
theorem codedDomain_infinite (T : Tree) : Set.Infinite {code | codedDomain T code} := by
  apply Set.infinite_of_injective_forall_mem (f := fun k => 2*k)
  · intro a b h
    change 2*a = 2*b at h
    omega
  · intro k; simp [codedDomain,rawDecode,GoodDom]

end Paper19
