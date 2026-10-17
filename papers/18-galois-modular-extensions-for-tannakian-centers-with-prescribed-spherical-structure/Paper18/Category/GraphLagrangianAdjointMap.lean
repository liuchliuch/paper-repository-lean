import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Actual algebra maps between right-adjoint unit algebras

An actual monoidal commuting square of strong tensor functors induces an
actual morphism of right-adjoint unit algebras. The proof uses the genuine
lifted adjunction on monoid objects, rather than assuming the algebra laws.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
open CategoryTheory.Functor.Monoidal
open scoped MonObj
universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄
namespace Paper18.Category.GraphLagrangian.AdjointMap

section Unit
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal]

/-- The actual strong unit comparison is an isomorphism of actual monoids. -/
def unitMonIso : Mon.mk (𝟙_ D) ≅ F.mapMon.obj (Mon.mk (𝟙_ C)) :=
  Mon.mkIso (εIso F) (by simp) (by
    change (λ_ (𝟙_ D)).hom ≫ ε F =
      (ε F ⊗ₘ ε F) ≫ Functor.LaxMonoidal.μ F (𝟙_ C) (𝟙_ C) ≫ F.map (λ_ (𝟙_ C)).hom
    rw [← tensorUnit_whiskerLeft_comp_leftUnitor_hom]
    exact (leftUnitor_naturality (ε F)).symm)

end Unit

section Square
variable {C₁ : Type u₁} [Category.{v₁} C₁] [MonoidalCategory C₁]
  {D₁ : Type u₂} [Category.{v₂} D₁] [MonoidalCategory D₁]
  {C₂ : Type u₃} [Category.{v₃} C₂] [MonoidalCategory C₂]
  {D₂ : Type u₄} [Category.{v₄} D₂] [MonoidalCategory D₂]
  (F₁ : C₁ ⥤ D₁) [F₁.Monoidal] (R₁ : D₁ ⥤ C₁) (a₁ : F₁ ⊣ R₁)
  (F₂ : C₂ ⥤ D₂) [F₂.Monoidal] (R₂ : D₂ ⥤ C₂) (a₂ : F₂ ⊣ R₂)
  (P : C₁ ⥤ C₂) [P.Monoidal] (Q : D₁ ⥤ D₂) [Q.Monoidal]
  (e : P ⋙ F₂ ≅ F₁ ⋙ Q) [NatTrans.IsMonoidal e.hom]

/-- The actual right-adjoint unit monoid with the canonical lax monoidal
structure constructed by the actual adjunction. -/
def unitAlgebra : Mon C₁ := by
  letI := a₁.rightAdjointLaxMonoidal
  exact R₁.mapMon.obj (Mon.mk (𝟙_ D₁))

/-- The actual counit square, already a morphism of actual monoid objects. -/
def inputMonHom : F₂.mapMon.obj (P.mapMon.obj (unitAlgebra F₁ R₁ a₁)) ⟶ Mon.mk (𝟙_ D₂) := by
  letI := a₁.rightAdjointLaxMonoidal
  exact (Functor.mapMonCompIso (F := P) (G := F₂)).inv.app (unitAlgebra F₁ R₁ a₁) ≫
    (Functor.mapMonNatTrans e.hom).app (unitAlgebra F₁ R₁ a₁) ≫
      (Functor.mapMonCompIso (F := F₁) (G := Q)).hom.app (unitAlgebra F₁ R₁ a₁) ≫
        Q.mapMon.map (a₁.mapMon.counit.app (Mon.mk (𝟙_ D₁))) ≫ (unitMonIso Q).inv

/-- The actual map between right-adjoint unit algebras is the transpose in
the genuine adjunction on actual monoid objects. -/
def comparison : P.mapMon.obj (unitAlgebra F₁ R₁ a₁) ⟶ unitAlgebra F₂ R₂ a₂ := by
  letI := a₂.rightAdjointLaxMonoidal
  exact a₂.mapMon.homEquiv _ _ (inputMonHom F₁ R₁ a₁ F₂ P Q e)

/-- The underlying actual algebra map. Its unit and multiplication laws
are supplied by the proved lifted adjunction, not extra comparison data. -/
def hom : P.obj (R₁.obj (𝟙_ D₁)) ⟶ R₂.obj (𝟙_ D₂) :=
  (comparison F₁ R₁ a₁ F₂ R₂ a₂ P Q e).hom

/-- The underlying comparison obeys the actual unit and multiplication
laws for the canonical actual right-adjoint unit algebra structures. -/
lemma hom_isMonHom :
    letI : MonObj (R₁.obj (𝟙_ D₁)) := (unitAlgebra F₁ R₁ a₁).mon
    letI : MonObj (R₂.obj (𝟙_ D₂)) := (unitAlgebra F₂ R₂ a₂).mon
    letI : MonObj (P.obj (R₁.obj (𝟙_ D₁))) := Functor.monObjObj (F := P) _
    IsMonHom (hom F₁ R₁ a₁ F₂ R₂ a₂ P Q e) :=
  (comparison F₁ R₁ a₁ F₂ R₂ a₂ P Q e).isMonHom_hom

/-- The actual untransposed counit square underlying the monoid morphism. -/
lemma inputMonHom_hom :
    (inputMonHom F₁ R₁ a₁ F₂ P Q e).hom =
      e.hom.app (R₁.obj (𝟙_ D₁)) ≫ Q.map (a₁.counit.app (𝟙_ D₁)) ≫ Functor.OplaxMonoidal.η Q := by
  simp [inputMonHom, unitMonIso, Adjunction.mapMon, unitAlgebra]

/-- The algebra map is exactly the expected actual adjunction transpose. -/
lemma hom_eq : hom F₁ R₁ a₁ F₂ R₂ a₂ P Q e =
    a₂.homEquiv _ _ (e.hom.app (R₁.obj (𝟙_ D₁)) ≫
      Q.map (a₁.counit.app (𝟙_ D₁)) ≫ Functor.OplaxMonoidal.η Q) := by
  rw [← inputMonHom_hom F₁ R₁ a₁ F₂ P Q e]
  simp [hom, comparison, Adjunction.homEquiv_apply, Adjunction.mapMon, unitAlgebra]

/-- The actual transpose equation characterizes the algebra comparison. -/
lemma hom_counit : F₂.map (hom F₁ R₁ a₁ F₂ R₂ a₂ P Q e) ≫
    a₂.counit.app (𝟙_ D₂) =
      e.hom.app (R₁.obj (𝟙_ D₁)) ≫ Q.map (a₁.counit.app (𝟙_ D₁)) ≫ Functor.OplaxMonoidal.η Q := by
  rw [hom_eq]
  exact (a₂.homEquiv_counit _ _ _).symm.trans
    ((a₂.homEquiv _ _).symm_apply_apply _)

end Square
end Paper18.Category.GraphLagrangian.AdjointMap
