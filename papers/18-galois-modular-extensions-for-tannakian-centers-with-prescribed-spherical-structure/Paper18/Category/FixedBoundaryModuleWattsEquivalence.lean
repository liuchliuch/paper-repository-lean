import Paper18.Category.FixedBoundaryModuleWatts

/-!
# The actual category of regular module functors is equivalent to C

Objects carry mathlib's genuine strong module-functor structures; morphisms
are actual module natural transformations. Evaluation at the unit and
right tensoring give explicit inverse equivalences.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.ModuleFunctor
variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- An actual endofunctor of the regular module category with its genuine
strong module lineator and all module-functor coherence laws. -/
structure RegularEnd where
  functor : C ⥤ C
  [moduleLinear : functor.LeftLinear C]

attribute [instance] RegularEnd.moduleLinear

instance regularEndCategory : Category (RegularEnd C) where
  Hom F H := {τ : F.functor ⟶ H.functor // IsModuleNatural C τ}
  id F := ⟨𝟙 F.functor, inferInstance⟩
  comp τ σ := ⟨τ.val ≫ σ.val, by
    letI := τ.property
    letI := σ.property
    infer_instance⟩
  id_comp τ := Subtype.ext (Category.id_comp τ.val)
  comp_id τ := Subtype.ext (Category.comp_id τ.val)
  assoc τ σ υ := Subtype.ext (Category.assoc τ.val σ.val υ.val)

/-- Evaluation takes actual module functors and transformations to their
actual value and component at the tensor unit. -/
def regularEvaluation : RegularEnd C ⥤ C where
  obj F := F.functor.obj (𝟙_ C)
  map τ := τ.val.app (𝟙_ C)

/-- The actual strong regular-module functor given by right tensoring. -/
def tensorRightEnd (U : C) : RegularEnd C := ⟨tensorRight U⟩

/-- Right tensoring also acts on actual morphisms, through module natural
transformations. -/
def rightTensorEmbedding : C ⥤ RegularEnd C where
  obj := tensorRightEnd C
  map f := ⟨tensorRightTransformation f, inferInstance⟩
  map_id U := by
    apply Subtype.ext
    ext X
    change X ◁ 𝟙 U = 𝟙 (X ⊗ U)
    simp
  map_comp f g := by
    apply Subtype.ext
    ext X
    change X ◁ (f ≫ g) = (X ◁ f) ≫ (X ◁ g)
    exact whiskerLeft_comp X f g

/-- The actual representing isomorphism is an isomorphism in the category
of module functors, including module compatibility of both directions. -/
def regularEndRepresentationIso (F : RegularEnd C) :
    F ≅ (rightTensorEmbedding C).obj ((regularEvaluation C).obj F) where
  hom := ⟨(regularRepresentationIso F.functor).hom, inferInstance⟩
  inv := ⟨(regularRepresentationIso F.functor).inv, inferInstance⟩
  hom_inv_id := Subtype.ext (regularRepresentationIso F.functor).hom_inv_id
  inv_hom_id := Subtype.ext (regularRepresentationIso F.functor).inv_hom_id

/-- An explicit categorical regular-module Eilenberg--Watts equivalence.
Its unit is the constructed module-natural representing isomorphism; its
counit is the actual ambient left unitor. -/
def regularModuleEquivalence : RegularEnd C ≌ C where
  functor := regularEvaluation C
  inverse := rightTensorEmbedding C
  unitIso := NatIso.ofComponents (regularEndRepresentationIso C) (fun {F H} τ => by
    apply Subtype.ext
    letI := τ.property
    ext X
    change τ.val.app X ≫ (regularRepresentationIso H.functor).hom.app X =
      (regularRepresentationIso F.functor).hom.app X ≫ (X ◁ τ.val.app (𝟙_ C))
    exact regularRepresentationIso_natural τ.val X)
  counitIso := NatIso.ofComponents (fun U => λ_ U) (fun {U V} f => by
    change (𝟙_ C ◁ f) ≫ (λ_ V).hom = (λ_ U).hom ≫ f
    exact leftUnitor_naturality f)
  functor_unitIso_comp F := by
    change (regularRepresentationIso F.functor).hom.app (𝟙_ C) ≫
      (λ_ (F.functor.obj (𝟙_ C))).hom = 𝟙 _
    rw [regularRepresentationIso_hom_unit, Iso.inv_hom_id]

end Paper18.Category.ModuleFunctor
