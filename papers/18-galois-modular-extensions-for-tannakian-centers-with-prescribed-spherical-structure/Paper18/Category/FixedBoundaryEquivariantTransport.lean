import Paper18.Category.FixedBoundaryActionTransport
import Paper18.Category.EquivariantKernels

/-!
# Actual equivariantization of action intertwiners

The comparison isomorphisms of a weak-action intertwiner transport the
structure isomorphisms of each actual equivariant object. Compatible natural
transformations lift as actual natural transformations, with their original
underlying components.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category
universe v u v' u' w
namespace Paper18.Category.WeakAction.Intertwiner
variable {G : Type w} [Group G]
  {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {A : WeakAction G C} {B : WeakAction G D} (F : A.Intertwiner B)

/-- Transport the structure maps of an actual equivariant object. -/
def mapEquivariantObj (X : A.Equivariant) : B.Equivariant where
  obj := F.functor.obj X.obj
  structureIso g := ((F.comparison g).app X.obj).symm ≪≫
    F.functor.mapIso (X.structureIso g)
  unit := by
    change (F.comparison 1).inv.app X.obj ≫ F.functor.map (X.structureIso 1).hom = _
    rw [X.unit, ← F.unit, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  mul g h := by
    change (B.ρ g).map ((F.comparison h).inv.app X.obj ≫
        F.functor.map (X.structureIso h).hom) ≫
        (F.comparison g).inv.app X.obj ≫ F.functor.map (X.structureIso g).hom =
      (B.mulIso g h).hom.app (F.functor.obj X.obj) ≫
        (F.comparison (g*h)).inv.app X.obj ≫ F.functor.map (X.structureIso (g*h)).hom
    apply (cancel_epi ((F.comparison g).hom.app ((A.ρ h).obj X.obj) ≫
      (B.ρ g).map ((F.comparison h).hom.app X.obj))).mp
    rw [Functor.map_comp]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp]
    have hn := (F.comparison g).hom.naturality (X.structureIso h).hom
    change F.functor.map ((A.ρ g).map (X.structureIso h).hom) ≫
        (F.comparison g).hom.app X.obj =
      (F.comparison g).hom.app ((A.ρ h).obj X.obj) ≫
        (B.ρ g).map (F.functor.map (X.structureIso h).hom) at hn
    rw [← Category.assoc, ← Category.assoc, ← hn]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← F.functor.map_comp, X.mul, F.functor.map_comp]
    slice_rhs 1 3 => rw [← F.mul g h X.obj]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

/-- Apply the actual underlying functor to an equivariant morphism. -/
def mapEquivariantHom {X Y : A.Equivariant} (f : X ⟶ Y) :
    F.mapEquivariantObj X ⟶ F.mapEquivariantObj Y where
  hom := F.functor.map f.hom
  comm g := by
    change (B.ρ g).map (F.functor.map f.hom) ≫
        (F.comparison g).inv.app Y.obj ≫ F.functor.map (Y.structureIso g).hom =
      ((F.comparison g).inv.app X.obj ≫ F.functor.map (X.structureIso g).hom) ≫
        F.functor.map f.hom
    have hn := (F.comparison g).inv.naturality f.hom
    change (B.ρ g).map (F.functor.map f.hom) ≫ (F.comparison g).inv.app Y.obj =
      (F.comparison g).inv.app X.obj ≫ F.functor.map ((A.ρ g).map f.hom) at hn
    rw [← Category.assoc, hn]
    simp only [Category.assoc, ← F.functor.map_comp, f.comm g]

/-- The genuine induced functor between actual equivariantizations. -/
def equivariantFunctor : A.Equivariant ⥤ B.Equivariant where
  obj := F.mapEquivariantObj
  map := F.mapEquivariantHom
  map_id X := by apply Equivariant.Hom.ext; exact F.functor.map_id X.obj
  map_comp f g := by apply Equivariant.Hom.ext; exact F.functor.map_comp f.hom g.hom

@[simp] theorem equivariantFunctor_comp_forget :
    F.equivariantFunctor ⋙ B.forget = A.forget ⋙ F.functor := rfl

instance equivariantFunctorFaithful [F.functor.Faithful] : F.equivariantFunctor.Faithful where
  map_injective h := by
    apply Equivariant.Hom.ext
    exact F.functor.map_injective (congrArg Equivariant.Hom.hom h)


instance equivariantFunctorFull [F.functor.Full] [F.functor.Faithful] :
    F.equivariantFunctor.Full where
  map_surjective {X Y} f := by
    let a := F.functor.preimage f.hom
    have ha : F.functor.map a = f.hom := F.functor.map_preimage f.hom
    let a' : X ⟶ Y :=
      ⟨a, fun g => by
        apply F.functor.map_injective
        rw [F.functor.map_comp, F.functor.map_comp, ha]
        have hn := (F.comparison g).hom.naturality a
        change F.functor.map ((A.ρ g).map a) ≫ (F.comparison g).hom.app Y.obj =
          (F.comparison g).hom.app X.obj ≫ (B.ρ g).map (F.functor.map a) at hn
        rw [ha] at hn
        have hf := f.comm g
        change (B.ρ g).map f.hom ≫ (F.comparison g).inv.app Y.obj ≫
            F.functor.map (Y.structureIso g).hom =
          ((F.comparison g).inv.app X.obj ≫ F.functor.map (X.structureIso g).hom) ≫ f.hom at hf
        calc
          _ = F.functor.map ((A.ρ g).map a) ≫ (F.comparison g).hom.app Y.obj ≫
              (F.comparison g).inv.app Y.obj ≫ F.functor.map (Y.structureIso g).hom := by simp
          _ = (F.comparison g).hom.app X.obj ≫ (B.ρ g).map f.hom ≫
              (F.comparison g).inv.app Y.obj ≫ F.functor.map (Y.structureIso g).hom := by
            rw [← Category.assoc, hn, Category.assoc]
          _ = _ := by rw [hf]; simp⟩
    exact ⟨a', Equivariant.Hom.ext ha⟩

variable {F} {H : A.Intertwiner B}

/-- An actual natural transformation compatible with the specified action
comparisons. -/
structure Transformation (F H : A.Intertwiner B) where
  natTrans : F.functor ⟶ H.functor
  comm : ∀ g X, (F.comparison g).hom.app X ≫ (B.ρ g).map (natTrans.app X) =
    natTrans.app ((A.ρ g).obj X) ≫ (H.comparison g).hom.app X

/-- The component of the induced natural transformation is the original
component, now verified to respect the actual equivariant structures. -/
def Transformation.equivariantComponent (τ : Transformation F H) (X : A.Equivariant) :
    F.mapEquivariantObj X ⟶ H.mapEquivariantObj X where
  hom := τ.natTrans.app X.obj
  comm g := by
    change (B.ρ g).map (τ.natTrans.app X.obj) ≫
        (H.comparison g).inv.app X.obj ≫ H.functor.map (X.structureIso g).hom =
      ((F.comparison g).inv.app X.obj ≫ F.functor.map (X.structureIso g).hom) ≫
        τ.natTrans.app X.obj
    apply (cancel_epi ((F.comparison g).hom.app X.obj)).mp
    rw [← Category.assoc, ← Category.assoc, τ.comm]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    exact (τ.natTrans.naturality (X.structureIso g).hom).symm

/-- Compatible transformations induce actual natural transformations
between the genuine equivariantization functors. -/
def Transformation.equivariantNatTrans (τ : Transformation F H) :
    F.equivariantFunctor ⟶ H.equivariantFunctor where
  app := τ.equivariantComponent
  naturality {X Y} f := by apply Equivariant.Hom.ext; exact τ.natTrans.naturality f.hom

/-- Compatible natural isomorphisms lift to natural isomorphisms of actual
equivariantization functors. -/
def Transformation.equivariantNatIso (τ : Transformation F H) [IsIso τ.natTrans] :
    F.equivariantFunctor ≅ H.equivariantFunctor :=
  NatIso.ofComponents (fun X => by
    let f := τ.equivariantComponent X
    letI : IsIso (B.forget.map f) := inferInstanceAs (IsIso (τ.natTrans.app X.obj))
    letI : IsIso f := isIso_of_reflects_iso f B.forget
    exact asIso f) (fun {X Y} f => (τ.equivariantNatTrans).naturality f)

end Paper18.Category.WeakAction.Intertwiner
