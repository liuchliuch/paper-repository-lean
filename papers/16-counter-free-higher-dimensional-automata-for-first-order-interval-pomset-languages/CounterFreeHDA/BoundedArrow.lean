import CounterFreeHDA.STCategory

namespace CounterFreeHDA.Cubical
universe u v
variable {Lab : Type u} {k : ℕ}

/-- The actual bounded interval-pomset source, retaining all event/order data. -/
structure BoundedArrow (U V : Cube Lab k) extends Arrow U V where
  width : pom.val.WidthLE k

namespace BoundedArrow

def ident (U : Cube Lab k) : BoundedArrow U U where
  toArrow := Arrow.ident U
  width := PomsetData.widthLE_of_size_le _ (Nat.le_of_lt_succ U.1.isLt)

noncomputable def comp {U V W : Cube Lab k} (A : BoundedArrow U V) (B : BoundedArrow V W) :
    BoundedArrow U W where
  toArrow := A.toArrow.comp B.toArrow
  width := TrackGlue.width_glue _ A.pom.property B.pom.property A.width B.width

noncomputable def ofStep {U V : Cube Lab k} (s : Step U V) : BoundedArrow U V where
  toArrow := s.label
  width := s.label_width

noncomputable def ofWord {U V : Cube Lab k} (p : Word U V) : BoundedArrow U V where
  toArrow := p.label
  width := p.label_width

@[simp] theorem ofWord_nil (U : Cube Lab k) : ofWord (.nil U) = ident U := rfl
@[simp] theorem ofWord_cons {U V W : Cube Lab k} (s : Step U V) (p : Word V W) :
    ofWord (.cons s p) = (ofStep s).comp (ofWord p) := rfl

noncomputable def representative {U V : Cube Lab k} (A : BoundedArrow U V) : Word U V :=
  Classical.choose ((st_representation A.pom.val A.pom.property A.width).typed A.toArrow)

noncomputable def representativeIso {U V : Cube Lab k} (A : BoundedArrow U V) :
    PomsetIso A.representative.label.pom.val A.pom.val :=
  Classical.choice (Classical.choose_spec ((st_representation A.pom.val A.pom.property A.width).typed A.toArrow))

end BoundedArrow

/-- A finite recognizing functor on actual bounded interval pomsets. The
identity, composition and isomorphism laws are the original recognizer data,
not assumptions about the ideal-diagram HDA to be constructed. -/
structure FinitePomsetRecognizer (L : Set (IntervalPom Lab)) (h : ℕ) where
  D : FinCat.{u,v} (Cube Lab k)
  map : ∀ {U V}, BoundedArrow U V → D.Hom U V
  map_id : ∀ U, map (BoundedArrow.ident U) = D.id U
  map_comp : ∀ {U V W} (A : BoundedArrow U V) (B : BoundedArrow V W),
    map (A.comp B) = D.comp (map A) (map B)
  map_iso : ∀ {U V} (A B : BoundedArrow U V), PomsetIso A.pom.val B.pom.val → map A = map B
  K : ∀ {U V}, Set (D.Hom U V)
  recognises : ∀ {U V} (A : BoundedArrow U V), A.pom ∈ L ↔ map A ∈ K
  aperiodic : D.AperiodicExponent h

namespace FinitePomsetRecognizer
variable {L : Set (IntervalPom Lab)} {h : ℕ} (G : FinitePomsetRecognizer.{u,v} (k := k) L h)

noncomputable def stepImage {U V : Cube Lab k} (s : Step U V) : G.D.Hom U V :=
  G.map (BoundedArrow.ofStep s)

theorem wordImage_eq {U V : Cube Lab k} (p : Word U V) :
    wordImage G.D G.stepImage p = G.map (BoundedArrow.ofWord p) := by
  induction p with
  | nil U => exact (G.map_id U).symm
  | cons s p ih =>
    change G.D.comp (G.stepImage s) (wordImage G.D G.stepImage p) = _
    rw [ih]
    exact (G.map_comp (BoundedArrow.ofStep s) (BoundedArrow.ofWord p)).symm

/-- Evaluation of the chosen actual ST representation recovers the original
recognizer's value on every bounded pomset. -/
theorem representative_image {U V : Cube Lab k} (A : BoundedArrow U V) :
    wordImage G.D G.stepImage A.representative = G.map A :=
  (G.wordImage_eq A.representative).trans
    (G.map_iso (BoundedArrow.ofWord A.representative) A A.representativeIso)

end FinitePomsetRecognizer
end CounterFreeHDA.Cubical
