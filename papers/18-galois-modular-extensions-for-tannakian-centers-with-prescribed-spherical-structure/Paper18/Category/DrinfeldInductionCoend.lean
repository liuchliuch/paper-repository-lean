import Paper18.Category.DrinfeldInductionBasic
import Paper18.Category.SemisimpleCoend
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# The actual finite central-induction coend

Existence of the coend is derived from the proved finite semisimple cowedge.
It is canonically isomorphic to the actual simple-diagonal direct sum.
The preservation helpers allow tensor functors to consume its universal property.
-/
noncomputable section
universe v u v' u' v'' u''
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Opposite

section Preservation
variable {J : Type u} [Category.{v} J]
  {C : Type u'} [Category.{v'} C] {D : Type u''} [Category.{v''} D]
  (H : Jᵒᵖ ⥤ J ⥤ C) [HasCoend H] (G : C ⥤ D)
  [PreservesColimit (multispanIndexCoend H).multispan G]

/-- A preserved coend retains its actual universal multicofork. -/
def mappedCoendIsColimit : IsColimit
    ((Multicoequalizer.multicofork (multispanIndexCoend H)).map G) :=
  Multicofork.isColimitMapOfPreserves _ G (colimit.isColimit _)

/-- Descending an actual dinatural family after a coend-preserving functor. -/
def mappedCoendDesc {T : D}
    (k : ∀ X : J, G.obj ((H.obj (op X)).obj X) ⟶ T)
    (hk : ∀ {X Y : J} (f : X ⟶ Y),
      G.map ((H.map f.op).app X) ≫ k X = G.map ((H.obj (op Y)).map f) ≫ k Y) :
    G.obj (coend H) ⟶ T :=
  Multicofork.IsColimit.desc (mappedCoendIsColimit H G) k (fun a => hk a.hom)

@[reassoc (attr := simp)]
lemma mappedCoendDesc_ι {T : D}
    (k : ∀ X : J, G.obj ((H.obj (op X)).obj X) ⟶ T)
    (hk : ∀ {X Y : J} (f : X ⟶ Y),
      G.map ((H.map f.op).app X) ≫ k X = G.map ((H.obj (op Y)).map f) ≫ k Y)
    (X : J) : G.map (coend.ι H X) ≫ mappedCoendDesc H G k hk = k X :=
  Multicofork.IsColimit.fac (mappedCoendIsColimit H G) k (fun a => hk a.hom) X

/-- A preserved coend's maps are determined by all actual dinatural components. -/
lemma mappedCoend_hom_ext {T : D} {f g : G.obj (coend H) ⟶ T}
    (h : ∀ X : J, G.map (coend.ι H X) ≫ f = G.map (coend.ι H X) ≫ g) : f = g :=
  Multicofork.IsColimit.hom_ext (mappedCoendIsColimit H G) h

end Preservation

section Induction
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type u'} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- Actual existence of the central-induction coend follows from semisimplicity. -/
def inductionHasCoend (X : C) : HasCoend (inductionDiagram X) :=
  S.semisimpleHasCoend (inductionDiagram X)

/-- The actual induction object in the underlying category. -/
def inductionUnderlying (X : C) : C :=
  letI := inductionHasCoend S X
  coend (inductionDiagram X)

/-- Its actual universal dinatural inclusion. -/
def inductionι (X T : C) : (T ⊗ X) ⊗ Tᘁ ⟶ inductionUnderlying S X :=
  letI := inductionHasCoend S X
  coend.ι (inductionDiagram X) T

@[reassoc]
lemma inductionι_dinatural (X : C) {T U : C} (f : T ⟶ U) :
    ((T ⊗ X) ◁ rightAdjointMate f) ≫ inductionι S X T =
      ((f ▷ X) ▷ Uᘁ) ≫ inductionι S X U := by
  letI := inductionHasCoend S X
  exact coend.condition (inductionDiagram X) f

/-- The underlying induction object is canonically the actual finite direct
sum of `Si ⊗ X ⊗ Si*`, with no coend-existence input. -/
def inductionUnderlyingIso (X : C) :
    inductionUnderlying S X ≅ ⨁ fun i =>
      (S.simpleObject i ⊗ X) ⊗ (S.simpleObject i)ᘁ :=
  S.semisimpleCoendIso (inductionDiagram X)

end Induction
end Paper18.Category.Drinfeld
