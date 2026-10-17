import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.CategoryTheory.Retract

/-! # Epimorphisms onto actual coends from retract-dominant generators

Every target diagonal inclusion factors through the diagonal inclusion of
an actual retract generator. Consequently an actual coend comparison is
epimorphic as soon as the source-image diagonal generators lift through it.
No pivotal or semisimplicity assumption is needed for this universal argument.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite
universe v u v' u' v'' u''
namespace Paper18.Category.CoendMap
variable {D : Type u} [Category.{v} D] {E : Type u'} [Category.{v'} E]
  (H : Dᵒᵖ ⥤ D ⥤ E) [HasCoend H]

/-- The actual bifunctor diagonal map associated to a two-sided retract. -/
def retractDiagonal {X Y : D} (r : Retract X Y) :
    (H.obj (op X)).obj X ⟶ (H.obj (op Y)).obj Y :=
  (H.map r.r.op).app X ≫ (H.obj (op Y)).map r.i

/-- Dinaturality turns the retract diagonal map into an actual factorization
of the smaller object's canonical coend inclusion. -/
@[reassoc]
lemma retractDiagonal_ι {X Y : D} (r : Retract X Y) :
    retractDiagonal H r ≫ coend.ι H Y = coend.ι H X := by
  dsimp only [retractDiagonal]
  rw [Category.assoc, ← coend.condition H r.i]
  rw [← Category.assoc, ← NatTrans.comp_app, ← H.map_comp, ← op_comp, r.retract]
  simp

variable {C : Type u''} [Category.{v''} C] (F : C ⥤ D)

/-- An actual coend comparison is epi if the translating functor is
retract-dominant and every actual source-image diagonal generator factors
through that comparison. The factorization equations refer only to the
given concrete maps, and epimorphy is proved by the coend universal property. -/
theorem epi_of_retract_dominant
    (hdom : ∀ Y : D, ∃ X : C, Nonempty (Retract Y (F.obj X)))
    {Q : E} (q : Q ⟶ coend H)
    (g : ∀ X : C, (H.obj (op (F.obj X))).obj (F.obj X) ⟶ Q)
    (hg : ∀ X, g X ≫ q = coend.ι H (F.obj X)) : Epi q where
  left_cancellation {Z} u v h := by
    apply coend.hom_ext
    intro Y
    obtain ⟨X, ⟨r⟩⟩ := hdom Y
    have hx : coend.ι H (F.obj X) ≫ u = coend.ι H (F.obj X) ≫ v := by
      rw [← hg X]
      simp only [Category.assoc]
      rw [h]
    rw [← retractDiagonal_ι H r, Category.assoc, Category.assoc, hx]

/-- The same result for a concrete target identified with the actual coend,
such as an actual adjoint diagonal algebra. -/
theorem epi_of_retract_dominant_iso
    (hdom : ∀ Y : D, ∃ X : C, Nonempty (Retract Y (F.obj X)))
    {Q R : E} (e : R ≅ coend H) (q : Q ⟶ R)
    (g : ∀ X : C, (H.obj (op (F.obj X))).obj (F.obj X) ⟶ Q)
    (hg : ∀ X, g X ≫ q ≫ e.hom = coend.ι H (F.obj X)) : Epi q := by
  letI : Epi (q ≫ e.hom) := epi_of_retract_dominant H F hdom (q ≫ e.hom) g hg
  have he : Epi ((q ≫ e.hom) ≫ e.inv) := inferInstance
  simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using he

end Paper18.Category.CoendMap
