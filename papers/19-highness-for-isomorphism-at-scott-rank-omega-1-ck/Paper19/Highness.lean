import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Corollary 7 reductions (Section 5)

Self-contained formalization of the injection-tree argument of [S5.p3]:
finite nested injections `C → D` covering initial segments of the
enumerations and preserving initial segments of the atomic diagram, with
a path through this tree exactly an isomorphism `C ≅ D`.

External inputs ([1 Prop 2.6], [4 Def 2 / padding], [5 existence of a
rank-κ structure]) are not assumed as axioms and are not proved here.
-/

namespace Paper19.Highness

/-! ## Languages and structures -/

/-- A language of atomic formulas: atom `i` has arity `ar i`. -/
structure Lang where
  ar : ℕ → ℕ

/-- A structure in language `L` with decidable equality on the carrier. -/
structure Struct (L : Lang) where
  carrier : Type
  [decEq : DecidableEq carrier]
  atom : (i : ℕ) → (Fin (L.ar i) → carrier) → Prop

attribute [instance] Struct.decEq

/-- A presentation of `L`: a structure plus a surjective enumeration. -/
structure Pres (L : Lang) extends Struct L where
  enum : ℕ → carrier
  enum_surj : Function.Surjective enum

/-- Isomorphisms of `L`-structures. -/
structure Iso {L : Lang} (C D : Struct L) where
  toFun : C.carrier → D.carrier
  invFun : D.carrier → C.carrier
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  map_atom : ∀ (i : ℕ) (t : Fin (L.ar i) → C.carrier),
    C.atom i t ↔ D.atom i (fun j => toFun (t j))

/-- Identity isomorphism. -/
def Iso.refl {L : Lang} (C : Struct L) : Iso C C where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_atom := fun _ _ => Iff.rfl

/-- Inverse isomorphism. -/
def Iso.symm {L : Lang} {C D : Struct L} (φ : Iso C D) : Iso D C where
  toFun := φ.invFun
  invFun := φ.toFun
  left_inv := φ.right_inv
  right_inv := φ.left_inv
  map_atom := fun i t => by
    set u : Fin (L.ar i) → C.carrier := fun j => φ.invFun (t j) with hu
    have key : (fun j => φ.toFun (u j)) = t := funext fun j => φ.right_inv (t j)
    constructor
    · intro hD
      exact (φ.map_atom i u).2 (key.symm ▸ hD)
    · intro hC
      exact key ▸ (φ.map_atom i u).1 hC

/-- Forward maps of isomorphisms are injective. -/
theorem Iso.toFun_injective {L : Lang} {C D : Struct L} (φ : Iso C D) :
    Function.Injective φ.toFun := by
  intro a a' h
  calc a = φ.invFun (φ.toFun a) := (φ.left_inv a).symm
    _ = φ.invFun (φ.toFun a') := congrArg φ.invFun h
    _ = a' := φ.left_inv a'

/-! ## Finite injections -/

/-- A finite injection `A → B`: a finite functional injective relation. -/
structure FinInj (A B : Type) where
  rel : Finset (A × B)
  functional : ∀ ⦃a : A⦄ ⦃b b' : B⦄, (a, b) ∈ rel → (a, b') ∈ rel → b = b'
  injective : ∀ ⦃a a' : A⦄ ⦃b : B⦄, (a, b) ∈ rel → (a', b) ∈ rel → a = a'

namespace FinInj

variable {A B : Type} [DecidableEq A] [DecidableEq B]

/-- Pair membership. -/
def Mem (ι : FinInj A B) (a : A) (b : B) : Prop := (a, b) ∈ ι.rel

/-- Extension of finite injections. -/
def Extends (ι ι' : FinInj A B) : Prop :=
  ∀ ⦃a : A⦄ ⦃b : B⦄, (a, b) ∈ ι.rel → (a, b) ∈ ι'.rel

theorem extends_refl (ι : FinInj A B) : Extends ι ι := fun _ _ h => h

theorem extends_trans {ι₁ ι₂ ι₃ : FinInj A B}
    (h12 : Extends ι₁ ι₂) (h23 : Extends ι₂ ι₃) : Extends ι₁ ι₃ :=
  fun _ _ h => h23 (h12 h)

theorem mem_graph_image {f : A → B} {s : Finset A} {a : A} {b : B} :
    (a, b) ∈ s.image (fun x => (x, f x)) ↔ a ∈ s ∧ b = f a := by
  constructor
  · intro h
    obtain ⟨x, hx, hp⟩ := Finset.mem_image.1 h
    cases hp
    exact ⟨hx, rfl⟩
  · intro ⟨ha, hb⟩
    refine Finset.mem_image.2 ⟨a, ha, ?_⟩
    rw [hb]

/-- The finite injection given by an injective function on a finite set. -/
def ofFnOn (f : A → B) (s : Finset A)
    (injOn : ∀ ⦃a a' : A⦄, a ∈ s → a' ∈ s → f a = f a' → a = a') :
    FinInj A B where
  rel := s.image (fun x => (x, f x))
  functional := by
    intro a b b' hb hb'
    have h1 : a ∈ s ∧ b = f a := mem_graph_image.1 hb
    have h2 : a ∈ s ∧ b' = f a := mem_graph_image.1 hb'
    rw [h1.2, h2.2]
  injective := by
    intro a a' b hb hb'
    have h1 : a ∈ s ∧ b = f a := mem_graph_image.1 hb
    have h2 : a' ∈ s ∧ b = f a' := mem_graph_image.1 hb'
    exact injOn h1.1 h2.1 (h1.2.symm.trans h2.2)

theorem ofFnOn_mem {f : A → B} {s : Finset A}
    {injOn : ∀ ⦃a a' : A⦄, a ∈ s → a' ∈ s → f a = f a' → a = a'}
    {a : A} (ha : a ∈ s) :
    (a, f a) ∈ (ofFnOn f s injOn).rel :=
  mem_graph_image.2 ⟨ha, rfl⟩

theorem ofFnOn_extends {f : A → B} {s t : Finset A} (hst : s ⊆ t)
    (injs : ∀ ⦃a a' : A⦄, a ∈ s → a' ∈ s → f a = f a' → a = a')
    (injt : ∀ ⦃a a' : A⦄, a ∈ t → a' ∈ t → f a = f a' → a = a') :
    Extends (ofFnOn f s injs) (ofFnOn f t injt) := by
  intro a b hab
  have h : a ∈ s ∧ b = f a := mem_graph_image.1 hab
  exact mem_graph_image.2 ⟨hst h.1, h.2⟩

end FinInj

/-! ## Stage conditions and the injection tree (paper S5.p3) -/

variable {L : Lang}

/-- Stage-`j` conditions on a finite injection `ι` between `C` and `D`. -/
def StageOK (C D : Pres L) (ι : FinInj C.carrier D.carrier) (j : ℕ) : Prop :=
  (∀ k < j, ∃ y, ι.Mem (C.enum k) y) ∧
  (∀ k < j, ∃ x, ι.Mem x (D.enum k)) ∧
  (∀ i < j, ∀ t : Fin (L.ar i) → C.carrier, ∀ u : Fin (L.ar i) → D.carrier,
    (∀ m, ι.Mem (t m) (u m)) → (C.atom i t ↔ D.atom i u))

/-- A path through the injection tree of [S5.p3]. -/
structure InjPath (C D : Pres L) where
  stages : ℕ → FinInj C.carrier D.carrier
  nestedMono : ∀ j, (stages j).Extends (stages (j + 1))
  stage_ok : ∀ j, StageOK C D (stages j) j

/-- Stages along a path are monotone. -/
theorem InjPath.mono {C D : Pres L} (p : InjPath C D) (i : ℕ) :
    ∀ j, i ≤ j → (p.stages i).Extends (p.stages j) := by
  intro j hij
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    subst hi
    exact FinInj.extends_refl _
  | succ j ih =>
    by_cases h : i ≤ j
    · exact FinInj.extends_trans (ih h) (p.nestedMono j)
    · have hi : i = j + 1 := by omega
      subst hi
      exact FinInj.extends_refl _

/-! ## Isomorphism ⇒ path -/

/-- Stage-`j` domain of the path induced by `φ`. -/
def isoDom (C D : Pres L) (φ : Iso C.toStruct D.toStruct) (j : ℕ) : Finset C.carrier :=
  (Finset.range j).biUnion fun k => ({C.enum k, φ.invFun (D.enum k)} : Finset C.carrier)

theorem mem_isoDom {C D : Pres L} {φ : Iso C.toStruct D.toStruct} {j : ℕ} {a : C.carrier} :
    a ∈ isoDom C D φ j ↔ ∃ k < j, a = C.enum k ∨ a = φ.invFun (D.enum k) := by
  simp [isoDom, Finset.mem_biUnion, Finset.mem_range]

theorem isoDom_injOn (C D : Pres L) (φ : Iso C.toStruct D.toStruct) (j : ℕ) :
    ∀ ⦃a a' : C.carrier⦄, a ∈ isoDom C D φ j → a' ∈ isoDom C D φ j →
      φ.toFun a = φ.toFun a' → a = a' := by
  intro a a' ha ha' hfa
  obtain ⟨k, -, ha⟩ := mem_isoDom.1 ha
  obtain ⟨k', -, ha'⟩ := mem_isoDom.1 ha'
  rcases ha with ha | ha <;> rcases ha' with ha' | ha' <;>
    rw [ha, ha'] at hfa ⊢ <;> exact φ.toFun_injective hfa

/-- Stage `j` of the path induced by `φ : C ≅ D`. -/
def isoStages (C D : Pres L) (φ : Iso C.toStruct D.toStruct) (j : ℕ) :
    FinInj C.carrier D.carrier :=
  FinInj.ofFnOn φ.toFun (isoDom C D φ j) (isoDom_injOn C D φ j)

theorem isoStages_stageOK (C D : Pres L) (φ : Iso C.toStruct D.toStruct) :
    ∀ j, StageOK C D (isoStages C D φ j) j := by
  intro j
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    refine ⟨φ.toFun (C.enum k), ?_⟩
    refine FinInj.ofFnOn_mem (s := isoDom C D φ j) ?_
    exact mem_isoDom.2 ⟨k, hk, Or.inl rfl⟩
  · intro k hk
    refine ⟨φ.invFun (D.enum k), ?_⟩
    have mem : (φ.invFun (D.enum k), φ.toFun (φ.invFun (D.enum k)))
        ∈ (isoStages C D φ j).rel :=
      FinInj.ofFnOn_mem (s := isoDom C D φ j)
        (mem_isoDom.2 ⟨k, hk, Or.inr rfl⟩)
    have h : φ.toFun (φ.invFun (D.enum k)) = D.enum k := φ.right_inv _
    rw [h] at mem
    exact mem
  · intro i hi t u htu
    have key : ∀ m, u m = φ.toFun (t m) := by
      intro m
      have hm : (t m, u m) ∈ (isoStages C D φ j).rel := htu m
      have hm' : (t m, u m) ∈
          (isoDom C D φ j).image (fun x => (x, φ.toFun x)) := hm
      have h := FinInj.mem_graph_image.1 hm'
      exact h.2
    constructor
    · intro hC
      have hD : D.atom i (fun m => φ.toFun (t m)) := (φ.map_atom i t).1 hC
      have heq : (fun m => φ.toFun (t m)) = u := funext fun m => (key m).symm
      rw [← heq]
      exact hD
    · intro hD
      have heq : (fun m => φ.toFun (t m)) = u := funext fun m => (key m).symm
      have hD' : D.atom i (fun m => φ.toFun (t m)) := by
        rw [heq]
        exact hD
      exact (φ.map_atom i t).2 hD'

theorem isoStages_nested (C D : Pres L) (φ : Iso C.toStruct D.toStruct) :
    ∀ j, (isoStages C D φ j).Extends (isoStages C D φ (j + 1)) := by
  intro j
  refine FinInj.ofFnOn_extends (f := φ.toFun) (s := isoDom C D φ j)
    (t := isoDom C D φ (j + 1)) ?_ _ _
  intro x hx
  obtain ⟨k, hk, hx⟩ := mem_isoDom.1 hx
  exact mem_isoDom.2 ⟨k, Nat.lt_succ_of_lt hk, hx⟩

/-- An isomorphism yields a path through the injection tree. -/
def isoToInjPath (C D : Pres L) (φ : Iso C.toStruct D.toStruct) : InjPath C D where
  stages := isoStages C D φ
  nestedMono := isoStages_nested C D φ
  stage_ok := isoStages_stageOK C D φ

/-! ## Path ⇒ isomorphism -/

/-- `foldl max` dominates its starting value. -/
theorem foldl_max_ge (l : List ℕ) (a b : ℕ) (hab : a ≤ b) : a ≤ l.foldl max b := by
  induction l generalizing b with
  | nil => simpa using hab
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact ih (max b hd) (le_trans hab (le_max_left _ _))

/-- Every entry of a list is dominated by `foldl max` of the list. -/
theorem mem_le_foldl_max (l : List ℕ) (a : ℕ) : ∀ x ∈ l, x ≤ l.foldl max a := by
  intro x hx
  induction l generalizing a with
  | nil => simp at hx
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.mem_cons] at hx
    rcases hx with h | h
    · rw [h]
      exact foldl_max_ge tl hd (max a hd) (le_max_right a hd)
    · exact ih (max a hd) h

/-- The union of a path is the relation `∃ j, (stages j).Mem x y`. -/
def InjPath.Rel {C D : Pres L} (p : InjPath C D) (x : C.carrier) (y : D.carrier) : Prop :=
  ∃ j, (p.stages j).Mem x y

theorem InjPath.rel_exists {C D : Pres L} (p : InjPath C D) (x : C.carrier) :
    ∃ y, p.Rel x y := by
  obtain ⟨k, hk⟩ := C.enum_surj x
  obtain ⟨y, hy⟩ := (p.stage_ok (k + 1)).1 k (Nat.lt_succ_self k)
  exact ⟨y, k + 1, hk ▸ hy⟩

theorem InjPath.rel_unique {C D : Pres L} (p : InjPath C D) (x : C.carrier)
    (y y' : D.carrier) : p.Rel x y → p.Rel x y' → y = y' := by
  intro hy hy'
  obtain ⟨j, hj⟩ := hy
  obtain ⟨j', hj'⟩ := hy'
  have h1 : (p.stages (max j j')).Mem x y := p.mono j _ (le_max_left _ _) hj
  have h2 : (p.stages (max j j')).Mem x y' := p.mono j' _ (le_max_right _ _) hj'
  exact (p.stages (max j j')).functional (a := x) (b := y) (b' := y') h1 h2

theorem InjPath.rel_injective {C D : Pres L} (p : InjPath C D) (x x' : C.carrier)
    (y : D.carrier) : p.Rel x y → p.Rel x' y → x = x' := by
  intro hy hy'
  obtain ⟨j, hj⟩ := hy
  obtain ⟨j', hj'⟩ := hy'
  have h1 : (p.stages (max j j')).Mem x y := p.mono j _ (le_max_left _ _) hj
  have h2 : (p.stages (max j j')).Mem x' y := p.mono j' _ (le_max_right _ _) hj'
  exact (p.stages (max j j')).injective (a := x) (a' := x') (b := y) h1 h2

theorem InjPath.rel_functional {C D : Pres L} (p : InjPath C D) (x : C.carrier) :
    ∃! y, p.Rel x y := by
  obtain ⟨y, hy⟩ := p.rel_exists x
  exact ⟨y, hy, fun y' hy' => p.rel_unique x y' y hy' hy⟩

theorem InjPath.rel_surjective {C D : Pres L} (p : InjPath C D) (y : D.carrier) :
    ∃ x, p.Rel x y := by
  obtain ⟨k, hk⟩ := D.enum_surj y
  -- hk : D.enum k = y
  obtain ⟨x, hx⟩ := (p.stage_ok (k + 1)).2.1 k (Nat.lt_succ_self k)
  exact ⟨x, k + 1, hk ▸ hx⟩

/-- Atomic formulas are preserved along the union of a path. -/
theorem InjPath.map_atom {C D : Pres L} (p : InjPath C D)
    (i : ℕ) (t : Fin (L.ar i) → C.carrier) :
    C.atom i t ↔ D.atom i (fun j => Classical.choose (p.rel_exists (t j))) := by
  classical
  set u : Fin (L.ar i) → D.carrier :=
    fun m => Classical.choose (p.rel_exists (t m)) with hu
  have hex : ∀ m : Fin (L.ar i), p.Rel (t m) (u m) := by
    intro m
    simp only [u]
    exact Classical.choose_spec (p.rel_exists (t m))
  set js : Fin (L.ar i) → ℕ := fun m => Classical.choose (hex m) with hjs
  have hjs_mem : ∀ m : Fin (L.ar i), (p.stages (js m)).Mem (t m) (u m) := by
    intro m
    simp only [js]
    exact Classical.choose_spec (hex m)
  refine (p.stage_ok ((List.ofFn js).foldl max 0 + i + 1)).2.2 i (by omega) t u ?_
  intro m
  have hjm : js m ≤ (List.ofFn js).foldl max 0 + i + 1 := by
    have hmem : js m ∈ List.ofFn js := List.mem_ofFn.2 ⟨m, rfl⟩
    have := mem_le_foldl_max (List.ofFn js) 0 _ hmem
    omega
  exact p.mono (js m) _ hjm (hjs_mem m)

/-- The union of a path is an isomorphism. -/
noncomputable def InjPath.toIso {C D : Pres L} (p : InjPath C D) : Iso C.toStruct D.toStruct where
  toFun := fun x => Classical.choose (p.rel_exists x)
  invFun := fun y => Classical.choose (p.rel_surjective y)
  left_inv := fun x => by
    have hxfx : p.Rel x (Classical.choose (p.rel_exists x)) :=
      Classical.choose_spec (p.rel_exists x)
    have hex := p.rel_surjective (Classical.choose (p.rel_exists x))
    have hfxgy : p.Rel (Classical.choose hex) (Classical.choose (p.rel_exists x)) :=
      Classical.choose_spec hex
    exact (p.rel_injective x (Classical.choose hex) _ hxfx hfxgy).symm
  right_inv := fun y => by
    have hy : p.Rel (Classical.choose (p.rel_surjective y)) y :=
      Classical.choose_spec (p.rel_surjective y)
    have hex : ∃ b, p.Rel (Classical.choose (p.rel_surjective y)) b :=
      p.rel_exists (Classical.choose (p.rel_surjective y))
    have hgz : p.Rel (Classical.choose (p.rel_surjective y)) (Classical.choose hex) :=
      Classical.choose_spec hex
    exact (p.rel_unique _ y _ hy hgz).symm
  map_atom := fun i t => p.map_atom i t

/-- **S5.p3 path ↔ isomorphism.**  The injection tree has a path
exactly when the two presentations are isomorphic. -/
theorem injPath_iff_iso (C D : Pres L) :
    Nonempty (InjPath C D) ↔ Nonempty (Iso C.toStruct D.toStruct) := by
  constructor
  · intro ⟨p⟩
    exact ⟨p.toIso⟩
  · intro ⟨φ⟩
    exact ⟨isoToInjPath C D φ⟩

/-- Uniform conversion: isomorphism → path of the injection tree. -/
def isoToInjPath_conv (C D : Pres L) : Iso C.toStruct D.toStruct → InjPath C D :=
  isoToInjPath C D

/-- Uniform conversion: path of the injection tree → isomorphism. -/
noncomputable def injPathToIso_conv (C D : Pres L) : InjPath C D → Iso C.toStruct D.toStruct :=
  fun p => p.toIso

/-- Highness for paths ↔ highness for isomorphism at the level of the
S5.p3 conversion: the injection tree identifies the two solution sets. -/
theorem highForPaths_iff_highForIso (C D : Pres L) :
    Nonempty (InjPath C D) ↔ Nonempty (Iso C.toStruct D.toStruct) :=
  injPath_iff_iso C D

end Paper19.Highness
