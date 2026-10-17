/-
Copyright (c) 2026. Counter-Free Higher-Dimensional Automata formalisation.
Finite categories with ordered hom-sets, lower sets and their action
(Lemma 2.2).
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Basic
import Mathlib.Tactic

/-!
# Ordered recognisers and lower sets

Following Lemma 2.1, an ordered recogniser is a finite category `C` whose
hom-sets are partially ordered, with monotone composition.  For a fixed source
object `S`, the coefficient sets are the lower sets `ℐ_S(U) = Down(C(S,U))`.
Lemma 2.2 records the laws of the action `I · P = ↓{a · F(P) | a ∈ I}`.
-/

namespace CounterFreeHDA

universe u v w

/-- A finite typed category. -/
structure FinCat (Obj : Type u) where
  Hom : Obj → Obj → Type v
  [homFintype : ∀ a b, Fintype (Hom a b)]
  [homDecEq : ∀ a b, DecidableEq (Hom a b)]
  id : ∀ a, Hom a a
  comp : ∀ {a b c}, Hom a b → Hom b c → Hom a c
  id_comp : ∀ {a b} (f : Hom a b), comp (id a) f = f
  comp_id : ∀ {a b} (f : Hom a b), comp f (id b) = f
  assoc : ∀ {a b c d} (f : Hom a b) (g : Hom b c) (h : Hom c d),
    comp (comp f g) h = comp f (comp g h)

attribute [instance] FinCat.homFintype
attribute [instance] FinCat.homDecEq

namespace FinCat

variable {Obj : Type u}

/-- Order on hom-sets, monotone with composition. -/
structure IsOrdered (C : FinCat Obj) where
  homLE : ∀ {a b}, C.Hom a b → C.Hom a b → Prop
  homLE_refl : ∀ {a b} (f : C.Hom a b), homLE f f
  homLE_trans : ∀ {a b} {f g h : C.Hom a b}, homLE f g → homLE g h → homLE f h
  homLE_antisymm : ∀ {a b} {f g : C.Hom a b}, homLE f g → homLE g f → f = g
  comp_mono_left : ∀ {a b c} (f f' : C.Hom a b) (g : C.Hom b c),
    homLE f f' → homLE (C.comp f g) (C.comp f' g)
  comp_mono_right : ∀ {a b c} (f : C.Hom a b) (g g' : C.Hom b c),
    homLE g g' → homLE (C.comp f g) (C.comp f g')

/-- Power of an endomorphism. -/
def pow {C : FinCat Obj} {a : Obj} (c : C.Hom a a) : ℕ → C.Hom a a
  | 0 => C.id a
  | n + 1 => C.comp (pow c n) c

@[simp] theorem pow_zero {C : FinCat Obj} {a : Obj} (c : C.Hom a a) :
    pow c 0 = C.id a := rfl

theorem pow_succ {C : FinCat Obj} {a : Obj} (c : C.Hom a a) (n : ℕ) :
    pow c (n + 1) = C.comp (pow c n) c := rfl

theorem pow_one {C : FinCat Obj} {a : Obj} (c : C.Hom a a) :
    pow c 1 = c := by
  show C.comp (C.id a) c = c
  exact C.id_comp c

/-- Aperiodicity exponent `h`: every endomorphism satisfies `c^h = c^{h+1}`. -/
def AperiodicExponent (C : FinCat Obj) (h : ℕ) : Prop :=
  ∀ (a : Obj) (c : C.Hom a a), pow c h = pow c (h + 1)

end FinCat

/-! ## Lower sets (explicit relation, no typeclass) -/

/-- `s` is a lower set of the relation `le`. -/
def IsLowerSet {α : Type u} (le : α → α → Prop) (s : Set α) : Prop :=
  ∀ ⦃a b : α⦄, a ∈ s → le b a → b ∈ s

theorem IsLowerSet.empty {α : Type u} {le : α → α → Prop} :
    IsLowerSet le (∅ : Set α) :=
  fun _ _ ha _ => absurd ha (Set.notMem_empty _)

theorem IsLowerSet.univ {α : Type u} {le : α → α → Prop} :
    IsLowerSet le (Set.univ : Set α) :=
  fun _ _ _ _ => trivial

theorem IsLowerSet.union {α : Type u} {le : α → α → Prop} {s t : Set α}
    (hs : IsLowerSet le s) (ht : IsLowerSet le t) : IsLowerSet le (s ∪ t) := by
  intro a b ha hle
  rcases ha with ha | ha
  · exact Or.inl (hs ha hle)
  · exact Or.inr (ht ha hle)

theorem IsLowerSet.inter {α : Type u} {le : α → α → Prop} {s t : Set α}
    (hs : IsLowerSet le s) (ht : IsLowerSet le t) : IsLowerSet le (s ∩ t) := by
  intro a b ha hle
  exact ⟨hs ha.1 hle, ht ha.2 hle⟩

theorem IsLowerSet.iUnion {α : Type u} {le : α → α → Prop} {ι : Type*} {f : ι → Set α}
    (h : ∀ i, IsLowerSet le (f i)) : IsLowerSet le (⋃ i, f i) := by
  intro a b ha hle
  obtain ⟨i, hai⟩ := Set.mem_iUnion.mp ha
  exact Set.mem_iUnion.mpr ⟨i, h i hai hle⟩

/-- Downward closure of a set along `le`. -/
def down {α : Type u} (le : α → α → Prop) (s : Set α) : Set α :=
  {b | ∃ a ∈ s, le b a}

theorem mem_down {α : Type u} {le : α → α → Prop} {s : Set α} {a : α} :
    a ∈ down le s ↔ ∃ b ∈ s, le a b := Iff.rfl

theorem isLowerSet_down {α : Type u} {le : α → α → Prop}
    (htrans : ∀ a b c, le a b → le b c → le a c) (s : Set α) :
    IsLowerSet le (down le s) := by
  intro x y hx hy
  obtain ⟨a, ha, hax⟩ := hx
  exact ⟨a, ha, htrans y x a hy hax⟩

theorem down_eq_of_isLowerSet {α : Type u} {le : α → α → Prop}
    (hrefl : ∀ a, le a a) {s : Set α} (h : IsLowerSet le s) :
    down le s = s := by
  apply Set.Subset.antisymm
  · intro a ha
    obtain ⟨b, hb, hle⟩ := ha
    exact h hb hle
  · intro a ha
    exact ⟨a, ha, hrefl a⟩

theorem down_mono {α : Type u} {le : α → α → Prop} {s t : Set α} (h : s ⊆ t) :
    down le s ⊆ down le t := by
  intro a ha
  obtain ⟨b, hb, hle⟩ := ha
  exact ⟨b, h hb, hle⟩

/-! ## Action of arrows on lower sets (Lemma 2.2) -/

namespace LowerSetAction

variable {Obj : Type u} {C : FinCat Obj} (ord : C.IsOrdered)

/-- `I · P = ↓{a · P | a ∈ I}`. -/
def act {S U V : Obj} (I : Set (C.Hom S U)) (P : C.Hom U V) :
    Set (C.Hom S V) :=
  down (fun x y => ord.homLE x y) ((fun a => C.comp a P) '' I)

theorem mem_act {S U V : Obj} {I : Set (C.Hom S U)} {P : C.Hom U V}
    {b : C.Hom S V} :
    b ∈ act ord I P ↔ ∃ a ∈ I, ord.homLE b (C.comp a P) := by
  constructor
  · intro hb
    obtain ⟨c, hc, hle⟩ := hb
    obtain ⟨a, ha, rfl⟩ := (Set.mem_image _ _ _).mp hc
    exact ⟨a, ha, hle⟩
  · intro h
    obtain ⟨a, ha, hle⟩ := h
    exact ⟨C.comp a P, Set.mem_image_of_mem (fun a => C.comp a P) ha, hle⟩

theorem act_isLowerSet {S U V : Obj} {I : Set (C.Hom S U)} {P : C.Hom U V} :
    IsLowerSet (fun x y => ord.homLE x y) (act ord I P) := by
  intro b c hb hcb
  obtain ⟨a, ha, hba⟩ := mem_act ord |>.mp hb
  exact mem_act ord |>.mpr ⟨a, ha, ord.homLE_trans hcb hba⟩

/-- Lemma 2.2: `I · id = I` for lower sets `I`. -/
theorem act_id {S U : Obj} {I : Set (C.Hom S U)}
    (hI : IsLowerSet (fun x y => ord.homLE x y) I) :
    act ord I (C.id U) = I := by
  apply Set.Subset.antisymm
  · intro b hb
    obtain ⟨a, ha, hle⟩ := mem_act ord |>.mp hb
    have hle' : ord.homLE b a := by
      rwa [C.comp_id a] at hle
    exact hI ha hle'
  · intro b hb
    refine mem_act ord |>.mpr ⟨b, hb, ?_⟩
    rw [C.comp_id b]
    exact ord.homLE_refl b

/-- Lemma 2.2: `(I · P) · Q = I · (P ∘ Q)` for lower sets `I`
(the proof does not need the lower-set hypothesis, but Lemma 2.2 is stated
for lower sets). -/
theorem act_comp {S U V W : Obj} {I : Set (C.Hom S U)}
    (_hI : IsLowerSet (fun x y => ord.homLE x y) I)
    (P : C.Hom U V) (Q : C.Hom V W) :
    act ord (act ord I P) Q = act ord I (C.comp P Q) := by
  apply Set.Subset.antisymm
  · intro b hb
    obtain ⟨a', ha', hle⟩ := mem_act ord |>.mp hb
    obtain ⟨a, ha, haa'⟩ := mem_act ord |>.mp ha'
    refine mem_act ord |>.mpr ⟨a, ha, ?_⟩
    have h1 : ord.homLE (C.comp a' Q) (C.comp (C.comp a P) Q) :=
      ord.comp_mono_left a' (C.comp a P) Q haa'
    rw [C.assoc a P Q] at h1
    exact ord.homLE_trans hle h1
  · intro b hb
    obtain ⟨a, ha, hle⟩ := mem_act ord |>.mp hb
    refine mem_act ord |>.mpr ⟨C.comp a P, ?_, ?_⟩
    · exact mem_act ord |>.mpr ⟨a, ha, ord.homLE_refl _⟩
    · rwa [C.assoc a P Q]

/-- Lemma 2.2: the action preserves unions of lower sets. -/
theorem act_iUnion {S U V : Obj} {ι : Type*} {f : ι → Set (C.Hom S U)}
    (P : C.Hom U V) :
    act ord (⋃ i, f i) P = ⋃ i, act ord (f i) P := by
  apply Set.Subset.antisymm
  · intro b hb
    obtain ⟨a, ha, hle⟩ := mem_act ord |>.mp hb
    obtain ⟨i, hai⟩ := Set.mem_iUnion.mp ha
    exact Set.mem_iUnion.mpr ⟨i, mem_act ord |>.mpr ⟨a, hai, hle⟩⟩
  · intro b hb
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hb
    obtain ⟨a, ha, hle⟩ := mem_act ord |>.mp hi
    exact mem_act ord |>.mpr ⟨a, Set.mem_iUnion.mpr ⟨i, ha⟩, hle⟩

/-- Lemma 2.2: monotonicity in the arrow (`P ≤ Q` implies `I · P ⊆ I · Q`). -/
theorem act_mono_arrow {S U V : Obj} (I : Set (C.Hom S U))
    {P Q : C.Hom U V} (hPQ : ord.homLE P Q) :
    act ord I P ⊆ act ord I Q := by
  intro b hb
  obtain ⟨a, ha, hle⟩ := mem_act ord |>.mp hb
  exact mem_act ord |>.mpr ⟨a, ha,
    ord.homLE_trans hle (ord.comp_mono_right a P Q hPQ)⟩

end LowerSetAction

end CounterFreeHDA
