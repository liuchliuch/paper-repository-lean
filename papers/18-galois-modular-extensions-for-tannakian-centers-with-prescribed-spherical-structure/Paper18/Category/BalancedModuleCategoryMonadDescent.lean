import Mathlib.CategoryTheory.Monad.Algebra
import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
import Mathlib.CategoryTheory.Whiskering

/-! # Actual coequalizer descent of a functor with a right monad action

This is a construction from ordinary functor and natural-transformation
data satisfying the two actual monad-action equations. No extension or
universal-property statement is a field. The extension to actual monad
algebras is defined by actual coequalizers, and its free-object comparison
is an explicitly proved isomorphism.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u vE uE
namespace Paper18.Category.BalancedModuleCategory
variable {C : Type u} [Category.{v} C] {E : Type uE} [Category.{vE} E]

/-- An actual functor carrying a right action of an actual monad. -/
structure RightMonadModule (T : Monad C) where
  toFunctor : C ⥤ E
  action : T.toFunctor ⋙ toFunctor ⟶ toFunctor
  unit : ∀ X, toFunctor.map (T.η.app X) ≫ action.app X = 𝟙 (toFunctor.obj X)
  assoc : ∀ X, toFunctor.map (T.μ.app X) ≫ action.app X = action.app (T.obj X) ≫ action.app X

namespace RightMonadModule
variable {T : Monad C} (H : RightMonadModule (E := E) T) [HasCoequalizers E]

def descentObj (P : Monad.Algebra T) : E :=
  coequalizer (H.action.app P.A) (H.toFunctor.map P.a)

def descentπ (P : Monad.Algebra T) : H.toFunctor.obj P.A ⟶ H.descentObj P :=
  coequalizer.π _ _

instance descentπ_epi (P : Monad.Algebra T) : Epi (H.descentπ P) := by
  unfold descentπ
  infer_instance

@[reassoc]
lemma descent_condition (P : Monad.Algebra T) :
    H.action.app P.A ≫ H.descentπ P = H.toFunctor.map P.a ≫ H.descentπ P :=
  coequalizer.condition _ _

def descentMap {P Q : Monad.Algebra T} (f : P ⟶ Q) : H.descentObj P ⟶ H.descentObj Q :=
  coequalizer.desc (H.toFunctor.map f.f ≫ H.descentπ Q) (by
    have hn := H.action.naturality f.f
    simp only [Functor.comp_map] at hn
    calc
      _ = H.toFunctor.map (T.map f.f) ≫ H.action.app Q.A ≫ H.descentπ Q := by
        rw [reassoc_of% hn]
      _ = H.toFunctor.map (T.map f.f) ≫ H.toFunctor.map Q.a ≫ H.descentπ Q := by
        rw [H.descent_condition]
      _ = _ := by rw [← H.toFunctor.map_comp_assoc, f.h, H.toFunctor.map_comp, Category.assoc])

@[reassoc (attr := simp)]
lemma descentπ_map {P Q : Monad.Algebra T} (f : P ⟶ Q) :
    H.descentπ P ≫ H.descentMap f = H.toFunctor.map f.f ≫ H.descentπ Q :=
  coequalizer.π_desc _ _

/-- The constructed functor on actual Eilenberg-Moore algebras. -/
def descent : Monad.Algebra T ⥤ E where
  obj := H.descentObj
  map := H.descentMap
  map_id P := by
    apply coequalizer.hom_ext
    change H.descentπ P ≫ H.descentMap (𝟙 P) = H.descentπ P ≫ 𝟙 _
    rw [descentπ_map]
    simp only [Monad.Algebra.id_f, H.toFunctor.map_id, id_comp, comp_id]
  map_comp {P Q R} f g := by
    apply coequalizer.hom_ext
    change H.descentπ P ≫ H.descentMap (f ≫ g) = H.descentπ P ≫ H.descentMap f ≫ H.descentMap g
    rw [descentπ_map, descentπ_map_assoc, descentπ_map]
    simp only [Monad.Algebra.comp_f, H.toFunctor.map_comp, Category.assoc]

/-- The comparison at a free algebra is an actual split coequalizer. -/
def freeSplitCoequalizer (X : C) : IsSplitCoequalizer
    (H.action.app (T.obj X)) (H.toFunctor.map (T.μ.app X)) (H.action.app X) where
  rightSection := H.toFunctor.map (T.η.app X)
  leftSection := H.toFunctor.map (T.map (T.η.app X))
  condition := (H.assoc X).symm
  rightSection_π := H.unit X
  leftSection_bottom := by
    rw [← H.toFunctor.map_comp, T.right_unit]
    exact H.toFunctor.map_id (T.obj X)
  leftSection_top := H.action.naturality (T.η.app X)

@[reassoc]
lemma freeπ_desc (X : C) :
    H.descentπ ((Monad.free T).obj X) ≫
      coequalizer.desc (H.action.app X) (H.assoc X).symm = H.action.app X :=
  coequalizer.π_desc _ _

/-- The actual extension agrees with its input functor on free algebras. -/
def freeIso (X : C) : H.descent.obj ((Monad.free T).obj X) ≅ H.toFunctor.obj X where
  hom := coequalizer.desc (H.action.app X) (H.assoc X).symm
  inv := H.toFunctor.map (T.η.app X) ≫ H.descentπ ((Monad.free T).obj X)
  hom_inv_id := by
    apply coequalizer.hom_ext
    change H.descentπ ((Monad.free T).obj X) ≫
        coequalizer.desc (H.action.app X) (H.assoc X).symm ≫
          H.toFunctor.map (T.η.app X) ≫ H.descentπ ((Monad.free T).obj X) = _
    calc
      _ = H.action.app X ≫ H.toFunctor.map (T.η.app X) ≫ H.descentπ ((Monad.free T).obj X) := by
        rw [freeπ_desc_assoc]
      _ = H.toFunctor.map (T.map (T.η.app X)) ≫ H.action.app (T.obj X) ≫
          H.descentπ ((Monad.free T).obj X) := by
        have hn := H.action.naturality (T.η.app X)
        simp only [Functor.comp_map] at hn
        simpa only [Category.assoc] using
          (congrArg (fun f => f ≫ H.descentπ ((Monad.free T).obj X)) hn).symm
      _ = H.toFunctor.map (T.map (T.η.app X)) ≫ H.toFunctor.map (T.μ.app X) ≫
          H.descentπ ((Monad.free T).obj X) :=
        congrArg (fun f => H.toFunctor.map (T.map (T.η.app X)) ≫ f)
          (H.descent_condition ((Monad.free T).obj X))
      _ = _ := by
        rw [← H.toFunctor.map_comp_assoc, T.right_unit, H.toFunctor.map_id, id_comp]
        exact (comp_id _).symm
  inv_hom_id := by
    calc
      _ = H.toFunctor.map (T.η.app X) ≫ H.action.app X :=
        (Category.assoc _ _ _).trans (congrArg (fun f => H.toFunctor.map (T.η.app X) ≫ f) (H.freeπ_desc X))
      _ = _ := H.unit X

@[reassoc (attr := simp)]
lemma descentπ_freeIso_hom (X : C) :
    H.descentπ ((Monad.free T).obj X) ≫ (H.freeIso X).hom = H.action.app X :=
  coequalizer.π_desc _ _

/-- The free-object comparison respects every actual ambient morphism. -/
def freeNatIso : Monad.free T ⋙ H.descent ≅ H.toFunctor :=
  NatIso.ofComponents H.freeIso (by
    intro X Y f
    apply (cancel_epi (H.descentπ ((Monad.free T).obj X))).mp
    change H.descentπ ((Monad.free T).obj X) ≫ H.descentMap ((Monad.free T).map f) ≫
        (H.freeIso Y).hom = H.descentπ ((Monad.free T).obj X) ≫ (H.freeIso X).hom ≫ H.toFunctor.map f
    rw [descentπ_map_assoc, descentπ_freeIso_hom,
      descentπ_freeIso_hom_assoc]
    exact H.action.naturality f)

end RightMonadModule
end Paper18.Category.BalancedModuleCategory
