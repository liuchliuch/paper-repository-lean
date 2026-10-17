import Paper19.IsoChar
import Paper19.TupleOrbit

namespace Paper19
open scoped symmDiff

/-- The actual domain excludes all vectors outside the Boolean groups. -/
def GoodDom {T : Tree} : Dom T → Prop
  | .idx _ => True
  | .vec n F => GMem T n F

abbrev Carrier (T : Tree) := {x : Dom T // GoodDom x}

namespace Carrier
variable {T : Tree}
def idx (k : ℕ) : Carrier T := ⟨.idx k, trivial⟩
def vec (n : ℕ) (F : Finset Node) (h : GMem T n F) : Carrier T := ⟨.vec n F, h⟩
def zeroVec (n : ℕ) : Carrier T := vec n ∅ (GMem_empty T n)
def rootOne : Carrier T := vec 0 {[]} (GMem_singleton ⟨(STree T).mem_nil, rfl⟩)
def isIdx (x : Carrier T) : Prop := isIndex x.val

def succ (x : Carrier T) : Carrier T := ⟨Dom.succ x.val, by
  rcases x with ⟨x, hx⟩; cases x <;> exact hx⟩
def levelOf (x : Carrier T) : Carrier T := ⟨Dom.levelOf x.val, by
  rcases x with ⟨x, hx⟩; cases x <;> trivial⟩
def projD (x : Carrier T) : Carrier T := ⟨Dom.projD x.val, by
  rcases x with ⟨x, hx⟩
  cases x with
  | idx _ => trivial
  | vec n F => cases n with
    | zero => exact hx
    | succ n => exact GMem_proj hx⟩

def D (k x y : Carrier T) : Prop := isD k.val x.val y.val

def translate (c : ℕ → Finset Node) (hc : ∀ n, GMem T n (c n))
    (x : Carrier T) : Carrier T := ⟨translateDom c x.val, by
  rcases x with ⟨x, hx⟩
  cases x with
  | idx k => trivial
  | vec n F => exact GMem_symmDiff hx (hc n)⟩

@[simp] theorem translate_idx (c : ℕ → Finset Node) (hc : ∀ n, GMem T n (c n)) (k : ℕ) :
    translate c hc (idx k) = idx k := rfl

@[simp] theorem translate_vec (c : ℕ → Finset Node) (hc : ∀ n, GMem T n (c n))
    (n : ℕ) (F : Finset Node) (hF : GMem T n F) :
    translate c hc (vec n F hF) = vec n (F ∆ c n) (GMem_symmDiff hF (hc n)) := rfl

@[simp] theorem translate_self (c : ℕ → Finset Node) (hc : ∀ n, GMem T n (c n))
    (x : Carrier T) : translate c hc (translate c hc x) = x :=
  Subtype.ext (translateDom_self c x.val)

end Carrier

/-- Isomorphism in exactly the paper's fixed finite language I, 0, c, s, p,
ℓ, D. Fixing each index is derived below rather than supplied as a field. -/
structure PresentationIso (T : Tree) (a b : Carrier T) where
  map : Carrier T ≃ Carrier T
  index : ∀ x, Carrier.isIdx (map x) ↔ Carrier.isIdx x
  zero : map (Carrier.idx 0) = Carrier.idx 0
  succ : ∀ x, map (Carrier.succ x) = Carrier.succ (map x)
  proj : ∀ x, map (Carrier.projD x) = Carrier.projD (map x)
  level : ∀ x, map (Carrier.levelOf x) = Carrier.levelOf (map x)
  rel : ∀ k x y, Carrier.D (map k) (map x) (map y) ↔ Carrier.D k x y
  named : map a = b

namespace PresentationIso
variable {T : Tree} {a b : Carrier T}

theorem fixes_index (f : PresentationIso T a b) (k : ℕ) :
    f.map (Carrier.idx k) = Carrier.idx k := by
  induction k with
  | zero => exact f.zero
  | succ k ih => exact (f.succ (Carrier.idx k)).trans (congrArg Carrier.succ ih)

/-- The level map and index predicate force every group to be preserved. -/
theorem preserves_level (f : PresentationIso T a b) (n : ℕ) (F : Finset Node)
    (hF : GMem T n F) :
    ∃ (H : Finset Node) (hH : GMem T n H), f.map (Carrier.vec n F hF) = Carrier.vec n H hH := by
  cases he : (f.map (Carrier.vec n F hF)).val with
  | idx k =>
    have hi : Carrier.isIdx (f.map (Carrier.vec n F hF)) := by
      unfold Carrier.isIdx; rw [he]; trivial
    exact False.elim ((f.index _).mp hi)
  | vec m H =>
    have hH : GMem T m H := by
      have hh := (f.map (Carrier.vec n F hF)).property
      simpa [he, GoodDom] using hh
    have hlevel := congrArg Subtype.val (f.level (Carrier.vec n F hF))
    change (f.map (Carrier.idx n)).val = Dom.levelOf (f.map (Carrier.vec n F hF)).val at hlevel
    rw [f.fixes_index n, he] at hlevel
    have hmn : n = m := Dom.idx.inj hlevel
    subst m
    exact ⟨H, hH, Subtype.ext he⟩

def translation (f : PresentationIso T a b) (n : ℕ) : Finset Node :=
  match (f.map (Carrier.zeroVec n)).val with
  | .vec _ H => H
  | .idx _ => ∅

theorem translation_good (f : PresentationIso T a b) (n : ℕ) :
    GMem T n (f.translation n) := by
  obtain ⟨H, hH, he⟩ := f.preserves_level n ∅ (GMem_empty T n)
  have hv : (f.map (Carrier.zeroVec n)).val = Dom.vec n H := congrArg Subtype.val he
  simpa only [translation, hv] using hH

theorem on_zero (f : PresentationIso T a b) (n : ℕ) :
    f.map (Carrier.zeroVec n) = Carrier.vec n (f.translation n) (f.translation_good n) := by
  obtain ⟨H, hH, he⟩ := f.preserves_level n ∅ (GMem_empty T n)
  apply Subtype.ext
  have hv : (f.map (Carrier.zeroVec n)).val = Dom.vec n H := congrArg Subtype.val he
  change (f.map (Carrier.zeroVec n)).val = Dom.vec n (f.translation n)
  simp only [translation, hv]

/-- Each named translation relation forces the image of F to be F △ h_n. -/
theorem on_vector (f : PresentationIso T a b) (n : ℕ) (F : Finset Node) (hF : GMem T n F) :
    (f.map (Carrier.vec n F hF)).val = Dom.vec n (F ∆ f.translation n) := by
  have hd : Carrier.D (Carrier.idx (encIndex n F)) (Carrier.zeroVec n) (Carrier.vec n F hF) := by
    exact ⟨encIndex n F, n, n, ∅, F, F, rfl, rfl, rfl, rfl, rfl, hF,
      (empty_symmDiff_fin F).symm⟩
  have hi := (f.rel _ _ _).mpr hd
  change isD _ _ _ at hi
  rw [f.fixes_index, f.on_zero] at hi
  obtain ⟨H, hH, he⟩ := f.preserves_level n F hF
  rw [he] at hi
  obtain ⟨code, m, m', A, B, K, hk, hx, hy, hmm, hc, hK, hdiff⟩ := hi
  have hidx := Dom.idx.inj hk
  obtain ⟨hn, hA⟩ := Dom.vec.inj hx
  obtain ⟨hn', hB⟩ := Dom.vec.inj hy
  subst m; subst m'; subst A; subst B
  have hK : K = F := (encIndex_injective (hidx.trans hc).symm).2
  subst K
  rw [he]
  change Dom.vec n H = Dom.vec n (F ∆ f.translation n)
  rw [hdiff, symmDiff_comm]

theorem coherent (f : PresentationIso T a b) (n : ℕ) :
    Paper19.proj T n (f.translation (n + 1)) = f.translation n := by
  have h := congrArg Subtype.val (f.proj (Carrier.zeroVec (n + 1)))
  have hz : Carrier.projD (Carrier.zeroVec (n + 1) : Carrier T) = Carrier.zeroVec n :=
    Subtype.ext (by simp [Carrier.projD, Carrier.zeroVec, Carrier.vec, Dom.projD, proj_empty])
  rw [hz, f.on_zero, f.on_zero] at h
  exact (Dom.vec.inj h).2.symm

end PresentationIso
/-- Construct the finite-language isomorphism from a valid coherent translation. -/
def translationIso {T : Tree} (h : ℕ → Finset Node) (hG : ∀ n, GMem T n (h n))
    (hp : ∀ n, proj T n (h (n + 1)) = h n) (a b : Carrier T)
    (hnamed : Carrier.translate h hG a = b) : PresentationIso T a b where
  map :=
    { toFun := Carrier.translate h hG
      invFun := Carrier.translate h hG
      left_inv := Carrier.translate_self h hG
      right_inv := Carrier.translate_self h hG }
  index := by
    intro ⟨x, hx⟩
    cases x <;> rfl
  zero := rfl
  succ := fun x => Subtype.ext (translateDom_succ h x.val)
  proj := by
    intro ⟨x, hx⟩
    apply Subtype.ext
    cases x with
    | idx k => rfl
    | vec n F =>
      cases n with
      | zero => rfl
      | succ n =>
        change Dom.vec n (proj T n F ∆ h n) = Dom.vec n (proj T n (F ∆ h (n + 1)))
        rw [proj_hom (GMem_len_succ hx) (GMem_len_succ (hG (n + 1))), hp]
  level := fun x => Subtype.ext (translateDom_levelOf h x.val)
  rel := fun k x y => (isD_translate h k.val x.val y.val).symm
  named := hnamed

def validIsoToPresentation {T : Tree} (c : ValidIso T) :
    PresentationIso T (Carrier.zeroVec 0) Carrier.rootOne :=
  translationIso c.val.h c.property c.val.coherence _ _ (Subtype.ext (by
    change Dom.vec 0 (∅ ∆ c.val.h 0) = Dom.vec 0 {[]}
    rw [c.val.root, empty_symmDiff_fin]))

def PresentationIso.toValidIso {T : Tree}
    (f : PresentationIso T (Carrier.zeroVec 0) Carrier.rootOne) : ValidIso T :=
  ⟨{ h := f.translation
     coherence := f.coherent
     root := by
       have h := congrArg Subtype.val (f.on_zero 0).symm
       have hn := congrArg Subtype.val f.named
       exact (Dom.vec.inj (h.trans hn)).2 }, f.translation_good⟩

/-- Exact isomorphism existence for the genuine structures, rather than a
coherence record without group membership. -/
theorem presentation_iff_validIso (T : Tree) :
    Nonempty (PresentationIso T (Carrier.zeroVec 0) Carrier.rootOne) ↔ Nonempty (ValidIso T) :=
  ⟨fun ⟨f⟩ => ⟨f.toValidIso⟩, fun ⟨c⟩ => ⟨validIsoToPresentation c⟩⟩

def namedRoot (T : Tree) (tag : Bool) : Carrier T :=
  if tag then Carrier.rootOne else Carrier.zeroVec 0

def validAutToPresentation {T : Tree} (c : ValidAut T) (tag : Bool) :
    PresentationIso T (namedRoot T tag) (namedRoot T tag) :=
  translationIso c.val.h c.property c.val.coherence _ _ (by
    apply Subtype.ext
    cases tag <;> simp [namedRoot, Carrier.translate, Carrier.rootOne,
      Carrier.zeroVec, Carrier.vec, translateDom, c.val.root])

def PresentationIso.toValidAut {T : Tree} {tag : Bool}
    (f : PresentationIso T (namedRoot T tag) (namedRoot T tag)) : ValidAut T := by
  refine ⟨⟨f.translation, f.coherent, ?_⟩, f.translation_good⟩
  cases tag with
  | false =>
    have hn := congrArg Subtype.val f.named
    have hz := congrArg Subtype.val (f.on_zero 0)
    exact (Dom.vec.inj (hz.symm.trans hn)).2
  | true =>
    have hF : GMem T 0 ({[]} : Finset Node) := GMem_singleton ⟨(STree T).mem_nil, rfl⟩
    have hz := f.on_vector 0 {[]} hF
    have hn := congrArg Subtype.val f.named
    change (f.map (Carrier.vec 0 {[]} hF)).val = Dom.vec 0 {[]} at hn
    have he : ({[]} : Finset Node) ∆ f.translation 0 = {[]} := (Dom.vec.inj (hz.symm.trans hn)).2
    have hh := congrArg (fun H : Finset Node => ({[]} : Finset Node) ∆ H) he
    simpa [symmDiff_assoc] using hh

theorem PresentationIso.translation_action {T : Tree} {a b : Carrier T}
    (f : PresentationIso T a b) (x : Carrier T) :
    f.map x = Carrier.translate f.translation f.translation_good x := by
  rcases x with ⟨x, hx⟩
  cases x with
  | idx k => exact f.fixes_index k
  | vec n F => exact Subtype.ext (f.on_vector n F hx)

end Paper19
