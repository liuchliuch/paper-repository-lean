import CounterFreeHDA.Basic
import CounterFreeHDA.Recognizer

/-! Labelled cubes and their face category.  A face is a substitution of
ordered variables and Boolean constants; substitution composition gives all
precubical identities, including mixed lower/upper faces. -/

namespace CounterFreeHDA.Cubical

universe u v w

abbrev Cube (Lab : Type u) (k : ℕ) := Σ n : Fin (k + 1), (Fin n.val → Lab)

namespace Cube
abbrev dim {Lab : Type u} {k} (U : Cube Lab k) := U.1.val
abbrev lab {Lab : Type u} {k} (U : Cube Lab k) := U.2
end Cube

variable {Lab : Type u} {k : ℕ}

/-- A face `U → V` of a labelled cube: every variable of `U` occurs exactly
once, in order; other coordinates of `V` are fixed at a lower or upper face. -/
@[ext] structure Face (U V : Cube Lab k) where
  sub : Fin V.dim → Fin U.dim ⊕ Bool
  vars : ∀ i, ∃! j, sub j = Sum.inl i
  ordered : ∀ {a b i j}, a < b → sub a = Sum.inl i → sub b = Sum.inl j → i < j
  labels : ∀ {j i}, sub j = Sum.inl i → V.lab j = U.lab i

namespace Face

def ident (U : Cube Lab k) : Face U U where
  sub := Sum.inl
  vars i := ⟨i, rfl, fun j h => Sum.inl.inj h⟩
  ordered := by intro a b i j hab hi hj; cases hi; cases hj; exact hab
  labels := by intro j i h; cases h; rfl

def comp {U V W : Cube Lab k} (f : Face U V) (g : Face V W) : Face U W where
  sub j := match g.sub j with
    | .inl i => f.sub i
    | .inr b => .inr b
  vars i := by
    obtain ⟨v, hv, huv⟩ := f.vars i
    obtain ⟨w, hw, huw⟩ := g.vars v
    refine ⟨w, ?_, ?_⟩
    · simp only [hw]; exact hv
    · intro j hj
      cases hgj : g.sub j with
      | inl v' =>
        simp only [hgj] at hj
        have hv' : v' = v := huv v' hj
        exact huw j (hgj.trans (congrArg Sum.inl hv'))
      | inr b => simp only [hgj] at hj; cases hj
  ordered := by
    intro a b i j hab hi hj
    cases hga : g.sub a with
    | inr c => simp only [hga] at hi; cases hi
    | inl x =>
      cases hgb : g.sub b with
      | inr c => simp only [hgb] at hj; cases hj
      | inl y =>
        simp only [hga] at hi
        simp only [hgb] at hj
        exact f.ordered (g.ordered hab hga hgb) hi hj
  labels := by
    intro j i hi
    cases hg : g.sub j with
    | inr b => simp only [hg] at hi; cases hi
    | inl v =>
      simp only [hg] at hi
      exact (g.labels hg).trans (f.labels hi)

@[simp] theorem comp_sub {U V W : Cube Lab k} (f : Face U V) (g : Face V W) (j) :
    (f.comp g).sub j = Sum.elim f.sub Sum.inr (g.sub j) := by
  change (match g.sub j with | .inl i => f.sub i | .inr b => .inr b) = _
  cases g.sub j <;> rfl

@[simp] theorem ident_comp {U V : Cube Lab k} (f : Face U V) : (ident U).comp f = f := by
  ext j
  change (match f.sub j with | .inl i => Sum.inl i | .inr b => Sum.inr b) = _
  cases f.sub j <;> rfl

@[simp] theorem comp_ident {U V : Cube Lab k} (f : Face U V) : f.comp (ident V) = f := by
  ext j; rfl

@[simp] theorem assoc {U V W Z : Cube Lab k} (f : Face U V) (g : Face V W) (h : Face W Z) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  ext j
  cases hh : h.sub j with
  | inr b => simp [comp, hh]
  | inl i => cases hg : g.sub i <;> simp [comp, hh, hg]

instance (U V : Cube Lab k) : Finite (Face U V) :=
  Finite.of_injective Face.sub (fun _ _ h => Face.ext h)

noncomputable instance (U V : Cube Lab k) : Fintype (Face U V) := Fintype.ofFinite _

def Lower {U V : Cube Lab k} (f : Face U V) : Prop :=
  ∀ j b, f.sub j = Sum.inr b → b = false

def Upper {U V : Cube Lab k} (f : Face U V) : Prop :=
  ∀ j b, f.sub j = Sum.inr b → b = true

/-- The standard cube face indexed by `θ` has exactly these constant statuses. -/
def status {U V : Cube Lab k} (f : Face U V) (j : Fin V.dim) : Status :=
  match f.sub j with
  | .inl _ => Status.star
  | .inr false => Status.zero
  | .inr true => Status.one

end Face

/-- A presheaf on the labelled cube face category, with all face identities. -/
structure Precubical (Lab : Type u) (k : ℕ) where
  Cell : Cube Lab k → Type v
  face : ∀ {U V}, Face U V → Cell V → Cell U
  face_ident : ∀ {U} (x : Cell U), face (Face.ident U) x = x
  face_comp : ∀ {U V W} (f : Face U V) (g : Face V W) (x : Cell W),
    face f (face g x) = face (f.comp g) x

@[ext] structure Map (X : Precubical.{u,v} Lab k) (Y : Precubical.{u,w} Lab k) where
  app : ∀ {U}, X.Cell U → Y.Cell U
  natural : ∀ {U V} (f : Face U V) (x : X.Cell V),
    app (X.face f x) = Y.face f (app x)

structure HDA (Lab : Type u) (k : ℕ) extends Precubical.{u,v} Lab k where
  initial : ∀ {U}, Cell U → Prop
  accepting : ∀ {U}, Cell U → Prop

/-- Typed elementary starters and terminators. -/
inductive Step : Cube Lab k → Cube Lab k → Type u where
  | start {U V} (f : Face U V) (lower : f.Lower) (dim : V.dim = U.dim + 1) : Step U V
  | stop {U V} (f : Face V U) (upper : f.Upper) (dim : U.dim = V.dim + 1) : Step U V

/-- An explicit elementary ST-decomposition. -/
inductive Word : Cube Lab k → Cube Lab k → Type u where
  | nil (U) : Word U U
  | cons {U V W} (s : Step U V) (p : Word V W) : Word U W

namespace Word

def append {U V W : Cube Lab k} (p : Word U V) (q : Word V W) : Word U W :=
  match p with
  | .nil _ => q
  | .cons s p => .cons s (p.append q)

def pow {U : Cube Lab k} (p : Word U U) : ℕ → Word U U
  | 0 => .nil U
  | n + 1 => (pow p n).append p
end Word

namespace Precubical

variable (X : Precubical.{u,v} Lab k)

/-- A run records its actual typed elementary label, rather than only interface
lengths.  Different words can label the same interval pomset; that quotient
is handled by the decomposition invariance lemmas. -/
inductive Run : ∀ {U V}, Word U V → X.Cell U → X.Cell V → Prop where
  | nil {U} (x : X.Cell U) : Run (.nil U) x x
  | start {U V W} (f : Face U V) (hl : f.Lower) (hd : V.dim = U.dim + 1)
      {p : Word V W} {x : X.Cell V} {y : X.Cell W} (r : Run p x y) :
      Run (.cons (.start f hl hd) p) (X.face f x) y
  | stop {U V W} (f : Face V U) (hu : f.Upper) (hd : U.dim = V.dim + 1)
      {p : Word V W} {x : X.Cell U} {y : X.Cell W} (r : Run p (X.face f x) y) :
      Run (.cons (.stop f hu hd) p) x y

def d {U V} (x : X.Cell U) (p : Word U V) : Set (X.Cell V) := {y | X.Run p x y}

theorem run_nil_iff {U} (x y : X.Cell U) : X.Run (.nil U) x y ↔ x = y := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact Run.nil x

theorem run_start_iff {U V W : Cube Lab k} (f : Face U V) (hl : f.Lower)
    (hd : V.dim = U.dim + 1) (p : Word V W) (x : X.Cell U) (y : X.Cell W) :
    X.Run (.cons (.start f hl hd) p) x y ↔ ∃ z, x = X.face f z ∧ X.Run p z y := by
  constructor
  · intro r
    cases r with
    | start _ _ _ h => exact ⟨_, rfl, h⟩
  · rintro ⟨z, rfl, h⟩
    exact Run.start f hl hd h

theorem run_stop_iff {U V W : Cube Lab k} (f : Face V U) (hu : f.Upper)
    (hd : U.dim = V.dim + 1) (p : Word V W) (x : X.Cell U) (y : X.Cell W) :
    X.Run (.cons (.stop f hu hd) p) x y ↔ X.Run p (X.face f x) y := by
  constructor
  · intro r
    cases r with
    | stop _ _ _ h => exact h
  · exact Run.stop f hu hd

theorem run_append_iff {U V W} (p : Word U V) (q : Word V W)
    (x : X.Cell U) (z : X.Cell W) :
    X.Run (p.append q) x z ↔ ∃ y, X.Run p x y ∧ X.Run q y z := by
  induction p with
  | nil U => simp only [Word.append, run_nil_iff]; aesop
  | @cons U V Z s p ih =>
    cases s with
    | start f hl hd =>
      constructor
      · intro h; cases h with
        | start _ _ _ r =>
          obtain ⟨y, hy, hz⟩ := (ih _ _).mp r
          exact ⟨y, Run.start f hl hd hy, hz⟩
      · rintro ⟨y, hy, hz⟩; cases hy with
        | start _ _ _ r => exact Run.start f hl hd ((ih _ _).mpr ⟨y, r, hz⟩)
    | stop f hu hd =>
      constructor
      · intro h; cases h with
        | stop _ _ _ r =>
          obtain ⟨y, hy, hz⟩ := (ih _ _).mp r
          exact ⟨y, Run.stop f hu hd hy, hz⟩
      · rintro ⟨y, hy, hz⟩; cases hy with
        | stop _ _ _ r => exact Run.stop f hu hd ((ih _ _).mpr ⟨y, r, hz⟩)

/-- Equation (1) on explicit ST-decompositions, with genuine powers. -/
def CounterFree (N : ℕ) : Prop :=
  1 ≤ N ∧ ∀ U (x : X.Cell U) (p : Word U U), X.d x (p.pow N) = X.d x (p.pow (N+1))

end Precubical

namespace Map

variable {X : Precubical.{u,v} Lab k} {Y : Precubical.{u,w} Lab k}

/-- A cubical map preserves every actual typed labelled run. -/
theorem map_run (m : Map X Y) {U V : Cube Lab k} {p : Word U V}
    {x : X.Cell U} {y : X.Cell V} (r : X.Run p x y) :
    Y.Run p (m.app x) (m.app y) := by
  induction r with
  | nil x => exact .nil _
  | start f hl hd h ih =>
    rw [m.natural]
    exact .start f hl hd ih
  | stop f hu hd h ih =>
    apply Precubical.Run.stop f hu hd
    rwa [← m.natural]

end Map

namespace HDA

def Lang (X : HDA.{u,v} Lab k) {U V : Cube Lab k} (p : Word U V) : Prop :=
  ∃ (x : X.Cell U) (y : X.Cell V), X.initial x ∧ X.accepting y ∧ X.toPrecubical.Run p x y
end HDA

end CounterFreeHDA.Cubical
