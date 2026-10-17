import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.WellFoundedSet
import Mathlib.Order.SymmDiff
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Fintype.Basic
import Mathlib.Computability.Primrec

/-!
# Core definitions for Paper 19 — FROZEN DEFINITIONAL LAYER.
# Parallel agents must NOT overwrite this file.
-/

namespace Paper19

open scoped symmDiff

set_option linter.unusedVariables false

abbrev Node := List ℕ
abbrev Stream := ℕ → ℕ
abbrev Bin := List Bool
abbrev BinVec (n : ℕ) := Fin n → Bool
abbrev BoundVec (n : ℕ) := Fin n → ℕ

instance boundVecLE (n : ℕ) : LE (BoundVec n) :=
  ⟨fun u v => ∀ i : Fin n, u i ≤ v i⟩

instance boundVecPreorder (n : ℕ) : Preorder (BoundVec n) where
  le_refl := fun _ _ => le_rfl
  le_trans := fun _ _ _ huv hvw i => (huv i).trans (hvw i)

instance boundVecPartialOrder (n : ℕ) : PartialOrder (BoundVec n) where
  le_antisymm := by
    intro u v huv hvu
    funext i
    exact le_antisymm (huv i) (hvu i)

theorem BoundVec.le_def {n : ℕ} {u v : BoundVec n} :
    u ≤ v ↔ ∀ i : Fin n, u i ≤ v i :=
  Iff.rfl

structure Tree where
  mem : Node → Prop
  decMem : ∀ σ, Decidable (mem σ)
  mem_nil : mem []
  mem_prefix : ∀ {σ τ}, mem τ → σ <+: τ → mem σ

attribute [instance] Tree.decMem

namespace Tree
def IsPath (T : Tree) (f : Stream) : Prop :=
  ∀ n : ℕ, T.mem (List.ofFn (fun i : Fin n => f i))
def IsExtendible (T : Tree) (σ : Node) : Prop :=
  ∃ f : Stream, T.IsPath f ∧ σ = List.ofFn (fun i : Fin σ.length => f i)
end Tree

def extLevel (T : Tree) (n : ℕ) : Set Node :=
  {σ | T.mem σ ∧ σ.length = n ∧ Tree.IsExtendible T σ}
def deadLevel (T : Tree) (n : ℕ) : Set Node :=
  {σ | T.mem σ ∧ σ.length = n ∧ ¬ Tree.IsExtendible T σ}
def level (T : Tree) (n : ℕ) : Set Node := {σ | T.mem σ ∧ σ.length = n}

def bitsOf (v : Node) (j : Fin v.length) : Bool :=
  decide (v.get j % 2 = 1)
def quotsOf (v : Node) (j : Fin v.length) : ℕ := v.get j / 2
def encodeBound {n : ℕ} (ρ : BinVec n) (u : BoundVec n) : Node :=
  List.ofFn (fun j : Fin n => 2 * u j + if ρ j then 1 else 0)

@[simp] theorem encodeBound_length {n : ℕ} (ρ : BinVec n) (u : BoundVec n) :
    (encodeBound ρ u).length = n := by simp [encodeBound]

theorem encodeBound_get {n : ℕ} (ρ : BinVec n) (u : BoundVec n) (j : Fin n) :
    (encodeBound ρ u).get ⟨j, by simp [encodeBound]⟩
      = 2 * u j + if ρ j then 1 else 0 := by simp [encodeBound]

theorem bitsOf_encodeBound {n : ℕ} (ρ : BinVec n) (u : BoundVec n) (j : Fin n) :
    bitsOf (encodeBound ρ u) ⟨j, by simp [encodeBound]⟩ = ρ j := by
  unfold bitsOf
  rw [encodeBound_get]
  by_cases h : ρ j <;> simp [h] <;> omega

theorem quotsOf_encodeBound {n : ℕ} (ρ : BinVec n) (u : BoundVec n) (j : Fin n) :
    quotsOf (encodeBound ρ u) ⟨j, by simp [encodeBound]⟩ = u j := by
  unfold quotsOf
  rw [encodeBound_get]
  by_cases h : ρ j <;> simp [h] <;> omega

def bitPrefix (v : Node) (q : ℕ) : Bin :=
  if h : q ≤ v.length then
    List.ofFn (fun j : Fin q => bitsOf v ⟨j, lt_of_lt_of_le j.is_lt h⟩)
  else []

theorem bitPrefix_of_le {v : Node} {q : ℕ} (hq : q ≤ v.length) :
    bitPrefix v q =
      List.ofFn (fun j : Fin q => bitsOf v ⟨j, lt_of_lt_of_le j.is_lt hq⟩) := by
  simp [bitPrefix, hq]

theorem bitPrefix_length {v : Node} {q : ℕ} (hq : q ≤ v.length) :
    (bitPrefix v q).length = q := by simp [bitPrefix_of_le hq]

theorem IsPrefix.get_eq {α : Type*} {σ τ : List α} (hp : σ <+: τ) (j : Fin σ.length) :
    σ.get j = τ.get ⟨j, j.is_lt.trans_le hp.length_le⟩ := by
  obtain ⟨t, rfl⟩ := hp
  simp [List.get_eq_getElem, List.getElem_append_left]

theorem bitsOf_prefix {σ τ : Node} (hp : σ <+: τ) (j : Fin σ.length) :
    bitsOf σ j = bitsOf τ ⟨j, j.is_lt.trans_le hp.length_le⟩ := by
  unfold bitsOf
  rw [IsPrefix.get_eq hp]

theorem quotsOf_prefix {σ τ : Node} (hp : σ <+: τ) (j : Fin σ.length) :
    quotsOf σ j = quotsOf τ ⟨j, j.is_lt.trans_le hp.length_le⟩ := by
  unfold quotsOf
  rw [IsPrefix.get_eq hp]

theorem bitPrefix_prefix {σ τ : Node} (hp : σ <+: τ) {q : ℕ} (hq : q ≤ σ.length) :
    bitPrefix σ q = bitPrefix τ q := by
  rw [bitPrefix_of_le hq, bitPrefix_of_le (hq.trans hp.length_le)]
  congr 1
  funext j
  exact bitsOf_prefix hp ⟨j, lt_of_lt_of_le j.is_lt hq⟩

def completedBlocksAux : Bin → ℕ → List ℕ
  | [], _ => []
  | true :: rest, z => z :: completedBlocksAux rest 0
  | false :: rest, z => completedBlocksAux rest (z + 1)
def completedBlocks (η : Bin) : List ℕ := completedBlocksAux η 0

@[simp] theorem completedBlocks_nil : completedBlocks [] = [] := rfl
@[simp] theorem completedBlocks_true (rest : Bin) :
    completedBlocks (true :: rest) = 0 :: completedBlocks rest := rfl
theorem completedBlocks_false (rest : Bin) :
    completedBlocks (false :: rest) = completedBlocksAux rest 1 := rfl

def RT (T : Tree) (η : Bin) (i : ℕ) : Prop :=
  (completedBlocks η).length ≥ i + 1 ∧
    T.mem ((completedBlocks η).take (i + 1))

instance RT.decidable (T : Tree) (η : Bin) (i : ℕ) : Decidable (RT T η i) := by
  unfold RT; infer_instance

def decodeBoundOf (f : Stream) (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (i + 1), (f j + 1)

@[simp] theorem decodeBoundOf_zero (f : Stream) : decodeBoundOf f 0 = f 0 + 1 := by
  simp [decodeBoundOf]

theorem decodeBoundOf_succ (f : Stream) (i : ℕ) :
    decodeBoundOf f (i + 1) = decodeBoundOf f i + f (i + 1) + 1 := by
  have h := Finset.sum_range_succ (fun j => f j + 1) (i + 1)
  simp [decodeBoundOf] at h ⊢
  omega

def binaryOf (f : Stream) (k : ℕ) : Bool :=
  decide (∃ j ≤ k, k + 1 = decodeBoundOf f j)

def binaryPrefix (f : Stream) (n : ℕ) : Bin :=
  List.ofFn (fun k : Fin n => binaryOf f k)

def IsQT (T : Tree) (X : ℕ → Bool) (b : Stream) : Prop :=
  ∀ i : ℕ, RT T (List.ofFn (fun k : Fin (b i) => X k)) i

def pathOfQT (X : ℕ → Bool) (b : Stream) : Stream :=
  fun i => (completedBlocks (List.ofFn (fun k : Fin (b i) => X k))).getD i 0

def S_mem (T : Tree) (v : Node) : Prop :=
  ∀ i : Fin v.length,
    quotsOf v i ≤ v.length →
      RT T (bitPrefix v (quotsOf v i)) i.val

instance S_mem.decidable (T : Tree) (v : Node) : Decidable (S_mem T v) := by
  unfold S_mem; infer_instance

def STree (T : Tree) : Tree where
  mem := S_mem T
  decMem := S_mem.decidable T
  mem_nil := by
    intro i hi
    exact absurd i.is_lt (Nat.not_lt_zero i.val)
  mem_prefix := by
    intro σ τ hτ hp
    intro i hq
    have hiτ : i.val < τ.length := i.is_lt.trans_le hp.length_le
    have hqeq : quotsOf σ i = quotsOf τ ⟨i.val, hiτ⟩ := quotsOf_prefix hp i
    have hqτ : quotsOf τ ⟨i.val, hiτ⟩ ≤ τ.length := by
      rw [← hqeq]
      exact hq.trans hp.length_le
    have hRT : RT T (bitPrefix τ (quotsOf τ ⟨i.val, hiτ⟩)) i.val :=
      hτ ⟨i.val, hiτ⟩ hqτ
    have hbit : bitPrefix σ (quotsOf σ i) = bitPrefix τ (quotsOf σ i) :=
      bitPrefix_prefix hp hq
    rw [hbit, hqeq]
    exact hRT

def Urho (T : Tree) {n : ℕ} (ρ : BinVec n) : Set (BoundVec n) :=
  {u | Tree.IsExtendible (STree T) (encodeBound ρ u)}

def proj (T : Tree) (n : ℕ) (F : Finset Node) : Finset Node :=
  ((F.filter (fun τ => τ.length = n + 1)).image (fun τ => τ.take n)).filter
    (fun σ => Odd ((F.filter (fun τ => τ.take n = σ)).card))

structure CoherentIso (T : Tree) where
  h : ℕ → Finset Node
  coherence : ∀ n, proj T n (h (n + 1)) = h n
  root : h 0 = {[]}

structure CoherentAut (T : Tree) where
  h : ℕ → Finset Node
  coherence : ∀ n, proj T n (h (n + 1)) = h n
  root : h 0 = ∅

def CoherentIso.act {T : Tree} (c : CoherentIso T) (n : ℕ) (F : Finset Node) : Finset Node :=
  F ∆ c.h n
def CoherentAut.act {T : Tree} (c : CoherentAut T) (n : ℕ) (F : Finset Node) : Finset Node :=
  F ∆ c.h n

inductive Dom (T : Tree) where
  | idx (k : ℕ)
  | vec (n : ℕ) (F : Finset Node)

def isIndex {T : Tree} : Dom T → Prop
  | .idx _ => True
  | .vec _ _ => False

def Dom.zeroIdx {T : Tree} : Dom T := .idx 0
def Dom.succ {T : Tree} : Dom T → Dom T
  | .idx k => .idx (k + 1)
  | d => d
def Dom.levelOf {T : Tree} : Dom T → Dom T
  | .vec n _ => .idx n
  | d => d
def Dom.projD {T : Tree} : Dom T → Dom T
  | .vec (n + 1) F => .vec n (proj T n F)
  | d => d
def Dom.cA {T : Tree} : Dom T := .vec 0 ∅
def Dom.cB {T : Tree} : Dom T := .vec 0 {[]}

def nodeCode (σ : Node) : ℕ := σ.foldl (fun acc x => Nat.pair acc (x + 1)) 0
noncomputable def finsetCode (H : Finset Node) : ℕ :=
  ((H.toList.mergeSort (· ≤ ·)).map nodeCode).foldl
    (fun acc c => Nat.pair (acc + 1) c) 0
/-- Fixed computable bijection naming the translation relations. -/
def encIndex (n : ℕ) (H : Finset Node) : ℕ :=
  Nat.pair n (@Encodable.encode (Finset Node)
    (inferInstance : Denumerable (Finset Node)).toEncodable H)

def decodeIndex (code : ℕ) : ℕ × Finset Node :=
  ((Nat.unpair code).1, Denumerable.ofNat (Finset Node) (Nat.unpair code).2)

@[simp] theorem decodeIndex_encIndex (n : ℕ) (H : Finset Node) :
    decodeIndex (encIndex n H) = (n, H) := by
  simp [decodeIndex, encIndex]

@[simp] theorem encIndex_decodeIndex (code : ℕ) :
    encIndex (decodeIndex code).1 (decodeIndex code).2 = code := by
  simp [decodeIndex, encIndex]

theorem encIndex_injective {n m : ℕ} {F G : Finset Node}
    (h : encIndex n F = encIndex m G) : n = m ∧ F = G := by
  have he := congrArg decodeIndex h
  simpa using he

def isD {T : Tree} (k F F' : Dom T) : Prop :=
  ∃ (code n n' : ℕ) (G G' H : Finset Node),
    k = .idx code ∧ F = .vec n G ∧ F' = .vec n' G' ∧
      n = n' ∧ code = encIndex n H ∧ (∀ σ ∈ H, σ ∈ level (STree T) n) ∧ G' = G ∆ H


end Paper19
