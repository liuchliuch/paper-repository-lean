import Paper18.Category.PicardAssociatorObstructionAssociahedron
import Mathlib.CategoryTheory.Products.Associator

/-! # Actual associator comparisons without pentagon coherence

A bifunctor and an actual natural isomorphism between its two triple
composites determine the five-input diagram. Its three square faces commute
by naturality alone, even when its pentagonal faces do not commute.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category
universe v u
namespace Paper18.Category.PicardAssociatorObstruction
variable {E : Type u} [Category.{v} E]

def tripleLeft (T : E × E ⥤ E) : (E × E) × E ⥤ E :=
  T.prod (𝟭 E) ⋙ T

def tripleRight (T : E × E ⥤ E) : (E × E) × E ⥤ E :=
  CategoryTheory.prod.associator E E E ⋙ (𝟭 E).prod T ⋙ T

/-- Actual binary product and triple comparison. There is deliberately no
pentagon field: its scalar failure is the obstruction under construction. -/
structure AssociatorSystem (E : Type u) [Category.{v} E] where
  tensor : E × E ⥤ E
  associator : tripleLeft tensor ≅ tripleRight tensor

namespace AssociatorSystem
variable (A : AssociatorSystem E)

def left (X : E) : E ⥤ E := CategoryTheory.Prod.sectR X E ⋙ A.tensor
def right (X : E) : E ⥤ E := CategoryTheory.Prod.sectL E X ⋙ A.tensor

abbrev product (X Y : E) : E := A.tensor.obj (X, Y)
abbrev assoc (X Y Z : E) : A.product (A.product X Y) Z ≅ A.product X (A.product Y Z) :=
  A.associator.app ((X, Y), Z)

/-- All actual bracketings and associator moves for five objects. -/
def diagram (a b c d e : E) : AssociahedronDiagram E where
  obj := ![A.product (A.product (A.product (A.product a b) c) d) e,
    A.product (A.product (A.product a (A.product b c)) d) e,
    A.product (A.product (A.product a b) (A.product c d)) e,
    A.product (A.product a (A.product (A.product b c) d)) e,
    A.product (A.product a (A.product b (A.product c d))) e,
    A.product (A.product (A.product a b) c) (A.product d e),
    A.product (A.product a (A.product b c)) (A.product d e),
    A.product (A.product a b) (A.product (A.product c d) e),
    A.product (A.product a b) (A.product c (A.product d e)),
    A.product a (A.product (A.product (A.product b c) d) e),
    A.product a (A.product (A.product b (A.product c d)) e),
    A.product a (A.product (A.product b c) (A.product d e)),
    A.product a (A.product b (A.product (A.product c d) e)),
    A.product a (A.product b (A.product c (A.product d e)))]
  a := (A.right e).mapIso ((A.right d).mapIso (A.assoc a b c))
  b := (A.right e).mapIso (A.assoc (A.product a b) c d)
  c := A.assoc (A.product (A.product a b) c) d e
  d := (A.right e).mapIso (A.assoc a (A.product b c) d)
  e := A.assoc (A.product a (A.product b c)) d e
  f := (A.right e).mapIso (A.assoc a b (A.product c d))
  g := A.assoc (A.product a b) (A.product c d) e
  h := (A.right e).mapIso ((A.left a).mapIso (A.assoc b c d))
  i := A.assoc a (A.product (A.product b c) d) e
  j := A.assoc a (A.product b (A.product c d)) e
  k := (A.right (A.product d e)).mapIso (A.assoc a b c)
  l := A.assoc (A.product a b) c (A.product d e)
  m := A.assoc a (A.product b c) (A.product d e)
  n := (A.left (A.product a b)).mapIso (A.assoc c d e)
  o := A.assoc a b (A.product (A.product c d) e)
  p := A.assoc a b (A.product c (A.product d e))
  q := (A.left a).mapIso ((A.right e).mapIso (A.assoc b c d))
  r := (A.left a).mapIso (A.assoc (A.product b c) d e)
  s := (A.left a).mapIso (A.assoc b (A.product c d) e)
  t := (A.left a).mapIso (A.assoc b c (A.product d e))
  z := (A.left a).mapIso ((A.left b).mapIso (A.assoc c d e))

theorem diagram_square₁ (a b c d e : E) :
    (A.diagram a b c d e).a.hom ≫ (A.diagram a b c d e).e.hom =
      (A.diagram a b c d e).c.hom ≫ (A.diagram a b c d e).k.hom := by
  have h := A.associator.hom.naturality (CategoryTheory.Prod.mkHom (CategoryTheory.Prod.mkHom (A.assoc a b c).hom (𝟙 d)) (𝟙 e))
  change A.tensor.map (CategoryTheory.Prod.mkHom (A.tensor.map (CategoryTheory.Prod.mkHom (A.assoc a b c).hom (𝟙 d))) (𝟙 e)) ≫ _ =
    _ ≫ A.tensor.map (CategoryTheory.Prod.mkHom (A.assoc a b c).hom (𝟙 (A.product d e)))
  change A.tensor.map (CategoryTheory.Prod.mkHom
      (A.tensor.map (CategoryTheory.Prod.mkHom (A.assoc a b c).hom (𝟙 d))) (𝟙 e)) ≫
      (A.assoc (A.product a (A.product b c)) d e).hom =
    (A.assoc (A.product (A.product a b) c) d e).hom ≫
      A.tensor.map (CategoryTheory.Prod.mkHom (A.assoc a b c).hom
        (A.tensor.map (CategoryTheory.Prod.mkHom (𝟙 d) (𝟙 e)))) at h
  rw [show A.tensor.map (CategoryTheory.Prod.mkHom (𝟙 d) (𝟙 e)) =
    𝟙 (A.product d e) from A.tensor.map_id (d, e)] at h
  exact h

theorem diagram_square₂ (a b c d e : E) :
    (A.diagram a b c d e).h.hom ≫ (A.diagram a b c d e).j.hom =
      (A.diagram a b c d e).i.hom ≫ (A.diagram a b c d e).q.hom := by
  have h := A.associator.hom.naturality (CategoryTheory.Prod.mkHom (CategoryTheory.Prod.mkHom (𝟙 a) (A.assoc b c d).hom) (𝟙 e))
  exact h

theorem diagram_square₃ (a b c d e : E) :
    (A.diagram a b c d e).n.hom ≫ (A.diagram a b c d e).p.hom =
      (A.diagram a b c d e).o.hom ≫ (A.diagram a b c d e).z.hom := by
  have h := A.associator.hom.naturality (CategoryTheory.Prod.mkHom (CategoryTheory.Prod.mkHom (𝟙 a) (𝟙 b)) (A.assoc c d e).hom)
  change A.tensor.map (CategoryTheory.Prod.mkHom (𝟙 (A.product a b)) (A.assoc c d e).hom) ≫ _ =
    _ ≫ A.tensor.map (CategoryTheory.Prod.mkHom (𝟙 a) (A.tensor.map (CategoryTheory.Prod.mkHom (𝟙 b) (A.assoc c d e).hom)))
  change A.tensor.map (CategoryTheory.Prod.mkHom
      (A.tensor.map (CategoryTheory.Prod.mkHom (𝟙 a) (𝟙 b))) (A.assoc c d e).hom) ≫
      (A.assoc a b (A.product c (A.product d e))).hom =
    (A.assoc a b (A.product (A.product c d) e)).hom ≫
      A.tensor.map (CategoryTheory.Prod.mkHom (𝟙 a)
        (A.tensor.map (CategoryTheory.Prod.mkHom (𝟙 b) (A.assoc c d e).hom))) at h
  rw [show A.tensor.map (CategoryTheory.Prod.mkHom (𝟙 a) (𝟙 b)) =
    𝟙 (A.product a b) from A.tensor.map_id (a, b)] at h
  exact h

end AssociatorSystem
end Paper18.Category.PicardAssociatorObstruction
