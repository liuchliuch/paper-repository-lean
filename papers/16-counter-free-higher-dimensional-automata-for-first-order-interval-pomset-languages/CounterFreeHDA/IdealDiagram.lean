import CounterFreeHDA.Cubical

/-! Definition 2.3 and Lemma 3.3, with dependent coefficients at the actual
face type and the actual recognised starter/terminator on every arc. -/

namespace CounterFreeHDA.Cubical

universe u v w

variable {Lab : Type u} {k : ℕ} (C : FinCat.{u,v} (Cube Lab k)) (ord : C.IsOrdered)
variable (image : ∀ {U V}, Step U V → C.Hom U V)

@[ext] structure IdealDiagram (S U : Cube Lab k) where
  val : ∀ {V}, Face V U → Set (C.Hom S V)
  lower : ∀ {V} (f : Face V U), IsLowerSet ord.homLE (val f)
  start : ∀ {V W} (f : Face V W) (hl : f.Lower) (hd : W.dim = V.dim + 1)
      (g : Face W U),
    LowerSetAction.act ord (val (f.comp g)) (image (.start f hl hd)) ⊆ val g
  stop : ∀ {V W} (f : Face V W) (hu : f.Upper) (hd : W.dim = V.dim + 1)
      (g : Face W U),
    LowerSetAction.act ord (val g) (image (.stop f hu hd)) ⊆ val (f.comp g)

namespace IdealDiagram

variable {C ord image}

def restrict {S U V : Cube Lab k} (f : Face U V) (z : IdealDiagram C ord image S V) :
    IdealDiagram C ord image S U where
  val g := z.val (g.comp f)
  lower g := z.lower _
  start g hl hd h := by simpa only [Face.assoc] using z.start g hl hd (h.comp f)
  stop g hu hd h := by simpa only [Face.assoc] using z.stop g hu hd (h.comp f)

@[simp] theorem restrict_val {S U V W : Cube Lab k} (f : Face U V)
    (z : IdealDiagram C ord image S V) (g : Face W U) :
    (restrict f z).val g = z.val (g.comp f) := rfl

@[simp] theorem restrict_ident {S U : Cube Lab k} (z : IdealDiagram C ord image S U) :
    restrict (Face.ident U) z = z := by ext V f; simp

@[simp] theorem restrict_comp {S U V W : Cube Lab k} (f : Face U V) (g : Face V W)
    (z : IdealDiagram C ord image S W) :
    restrict f (restrict g z) = restrict (f.comp g) z := by ext Z h; simp

/-- The all-active entry, indexed by the identity face. -/
def top {S U : Cube Lab k} (z : IdealDiagram C ord image S U) : Set (C.Hom S U) :=
  z.val (Face.ident U)

end IdealDiagram

/-- The genuine precubical component `H_S`, with every admissible diagram. -/
def ideal (S : Cube Lab k) : Precubical Lab k where
  Cell := IdealDiagram C ord image S
  face := IdealDiagram.restrict
  face_ident := IdealDiagram.restrict_ident
  face_comp := IdealDiagram.restrict_comp

/-- All components, with the markings (5) and (6).  The initial type must be
exactly the coefficient source; interfaces may have positive dimension. -/
def idealHDA (J : ∀ {S U}, Set (C.Hom S U)) : HDA Lab k where
  Cell U := Σ S, IdealDiagram C ord image S U
  face f z := ⟨z.1, z.2.restrict f⟩
  face_ident z := by cases z; simp
  face_comp f g z := by cases z; simp
  initial := fun {U} z => ∃ h : z.1 = U,
    C.id U ∈ (h ▸ z.2).top
  accepting z := z.2.top ⊆ J

noncomputable instance idealDiagramFintype [Fintype Lab] (S U : Cube Lab k) :
    Fintype (IdealDiagram C ord image S U) := by
  letI : Finite (IdealDiagram C ord image S U) :=
    Finite.of_injective (fun z : IdealDiagram C ord image S U => @z.val)
      (fun _ _ h => IdealDiagram.ext h)
  exact Fintype.ofFinite _

/-- Definition 2.3 and Remark 2.4: all constructed cells, over all components
and types, form a finite set. -/
noncomputable instance idealHDAFintype [Fintype Lab] (J : ∀ {S U}, Set (C.Hom S U)) :
    Fintype (Σ U, (idealHDA C ord image J).Cell U) := by
  change Fintype (Σ U : Cube Lab k, Σ S : Cube Lab k, IdealDiagram C ord image S U)
  infer_instance

/-- A colouring assigns a lower ideal of the correct hom-set to each cell,
with equation (4) on every directed elementary face arc. -/
@[ext] structure Coloring (X : Precubical.{u,w} Lab k) (S : Cube Lab k) where
  val : ∀ {U}, X.Cell U → Set (C.Hom S U)
  lower : ∀ {U} (x : X.Cell U), IsLowerSet ord.homLE (val x)
  start : ∀ {U V} (f : Face U V) (hl : f.Lower) (hd : V.dim = U.dim + 1) (x : X.Cell V),
    LowerSetAction.act ord (val (X.face f x)) (image (.start f hl hd)) ⊆ val x
  stop : ∀ {U V} (f : Face U V) (hu : f.Upper) (hd : V.dim = U.dim + 1) (x : X.Cell V),
    LowerSetAction.act ord (val x) (image (.stop f hu hd)) ⊆ val (X.face f x)

namespace Coloring
variable {C ord image} {X : Precubical.{u,w} Lab k} {S : Cube Lab k}

/-- Construct each image diagram from the colours of all its actual faces. -/
def toMap (a : Coloring C ord image X S) : Map X (ideal C ord image S) where
  app x := {
    val f := a.val (X.face f x)
    lower f := a.lower _
    start f hl hd g := by simpa only [X.face_comp] using a.start f hl hd (X.face g x)
    stop f hu hd g := by simpa only [X.face_comp] using a.stop f hu hd (X.face g x) }
  natural f x := by
    apply IdealDiagram.ext
    funext W g
    exact congrArg a.val (X.face_comp g f x)

/-- Recover colours from the all-active entries of a cubical map. -/
def ofMap (m : Map X (ideal C ord image S)) : Coloring C ord image X S where
  val x := (m.app x).top
  lower x := (m.app x).lower _
  start f hl hd x := by
    have hm := m.natural f x
    change m.app (X.face f x) = (m.app x).restrict f at hm
    have h := (m.app x).start f hl hd (Face.ident _)
    simpa only [hm, IdealDiagram.top, IdealDiagram.restrict_val, Face.ident_comp,
      Face.comp_ident] using h
  stop f hu hd x := by
    have hm := m.natural f x
    change m.app (X.face f x) = (m.app x).restrict f at hm
    have h := (m.app x).stop f hu hd (Face.ident _)
    simpa only [hm, IdealDiagram.top, IdealDiagram.restrict_val, Face.ident_comp,
      Face.comp_ident] using h

@[simp] theorem ofMap_toMap (a : Coloring C ord image X S) : ofMap a.toMap = a := by
  apply Coloring.ext
  funext U x
  change a.val (X.face (Face.ident U) x) = a.val x
  rw [X.face_ident]

@[simp] theorem toMap_ofMap (m : Map X (ideal C ord image S)) : (ofMap m).toMap = m := by
  apply Map.ext
  funext U x
  apply IdealDiagram.ext
  funext V f
  change (m.app (X.face f x)).top = (m.app x).val f
  rw [m.natural f x]
  change (m.app x).val ((Face.ident V).comp f) = _
  rw [Face.ident_comp]

end Coloring

/-- **Lemma 3.3.** A cubical map to the actual ideal-diagram HDA is equivalent
to an arc-compatible colouring.  This holds for any precubical source. -/
def lemma_3_3 (X : Precubical.{u,w} Lab k) (S : Cube Lab k) :
    Map X (ideal C ord image S) ≃ Coloring C ord image X S where
  toFun := Coloring.ofMap
  invFun := Coloring.toMap
  left_inv := Coloring.toMap_ofMap
  right_inv := Coloring.ofMap_toMap

/-- Prescribing a cell image prescribes exactly all of its face colours. -/
theorem prescribed_image_iff (X : Precubical.{u,w} Lab k) (S U : Cube Lab k)
    (m : Map X (ideal C ord image S)) (x : X.Cell U) (z : IdealDiagram C ord image S U) :
    m.app x = z ↔ ∀ V (f : Face V U), (Coloring.ofMap m).val (X.face f x) = z.val f := by
  constructor
  · intro h V f
    change (m.app (X.face f x)).top = _
    rw [m.natural, h]
    change z.val ((Face.ident V).comp f) = _
    rw [Face.ident_comp]
  · intro h
    apply IdealDiagram.ext
    funext V f
    have hh := h V f
    change (m.app (X.face f x)).top = z.val f at hh
    rw [m.natural] at hh
    simpa only [ideal, IdealDiagram.top, IdealDiagram.restrict_val, Face.ident_comp] using hh

end CounterFreeHDA.Cubical
