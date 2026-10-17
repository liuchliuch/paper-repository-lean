import Paper18.Category.ModuleFunctorSemisimpleCornerBasic
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Actual full faithful extension along a module coreflection -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u vM uM vN uN
namespace Paper18.Category.ModuleFunctor
open MonoidalLeftAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type uM} [Category.{vM} M] [MonoidalLeftAction C M]
  {N : Type uN} [Category.{vN} N] [MonoidalLeftAction C N]
  (I : M ⥤ N) [I.LeftLinear C] [I.Full] [I.Faithful]
  (P : N ⥤ M) [P.LeftLinear C] (adj : I ⊣ P)
  [IsModuleNatural C adj.unit] [IsModuleNatural C adj.counit]
  (F G : M ⥤ M) [F.LeftLinear C] [G.LeftLinear C]

/-- Restrict to the actual full subcategory and conjugate by the actual
adjunction unit. This is the genuine preimage under precomposition. -/
def cornerPrePreimage (τ : P ⋙ F ⟶ P ⋙ G) : F ⟶ G :=
  (Functor.leftUnitor F).inv ≫ Functor.whiskerRight adj.unit F ≫
    (Functor.associator I P F).hom ≫ Functor.whiskerLeft I τ ≫
      (Functor.associator I P G).inv ≫ Functor.whiskerRight (asIso adj.unit).inv G ≫
        (Functor.leftUnitor G).hom

instance cornerPrePreimage_moduleNatural (τ : P ⋙ F ⟶ P ⋙ G)
    [IsModuleNatural C τ] : IsModuleNatural C (cornerPrePreimage I P adj F G τ) := by
  letI : IsModuleNatural C (asIso adj.unit).hom :=
    inferInstanceAs (IsModuleNatural C adj.unit)
  letI : IsModuleNatural C (asIso adj.unit).inv := inferInstance
  dsimp only [cornerPrePreimage]
  infer_instance

@[simp]
lemma cornerPrePreimage_app (τ : P ⋙ F ⟶ P ⋙ G) (m : M) :
    (cornerPrePreimage I P adj F G τ).app m =
      F.map (adj.unit.app m) ≫ τ.app (I.obj m) ≫ G.map ((asIso adj.unit).inv.app m) := by
  simp only [cornerPrePreimage, NatTrans.comp_app, Functor.leftUnitor_hom_app,
    Functor.leftUnitor_inv_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, id_comp]
  erw [comp_id]

/-- The actual triangle identity identifies the unit inverse on an
actual projected object. -/
lemma corner_unit_inv (n : N) :
    (asIso adj.unit).inv.app (P.obj n) = P.map (adj.counit.app n) := by
  apply (cancel_epi (adj.unit.app (P.obj n))).mp
  have h := congrArg (fun t => t.app (P.obj n)) (asIso adj.unit).hom_inv_id
  exact h.trans (adj.right_triangle_components n).symm

@[simp]
lemma cornerPrePreimage_whisker (τ : P ⋙ F ⟶ P ⋙ G) :
    Functor.whiskerLeft P (cornerPrePreimage I P adj F G τ) = τ := by
  apply NatTrans.ext
  funext n
  rw [Functor.whiskerLeft_app, cornerPrePreimage_app, corner_unit_inv]
  erw [← τ.naturality]
  change F.map (adj.unit.app (P.obj n)) ≫ F.map (P.map (adj.counit.app n)) ≫ τ.app n = _
  rw [← F.map_comp_assoc, adj.right_triangle_components]
  erw [F.map_id, id_comp]

include I adj in
/-- Precomposition with the actual right adjoint is faithful, since
restriction to the actual inclusion recovers the original maps. -/
lemma cornerPreWhisker_injective (τ σ : F ⟶ G)
    (h : Functor.whiskerLeft P τ = Functor.whiskerLeft P σ) : τ = σ := by
  apply NatTrans.ext
  funext m
  have hh := congrArg (fun a => a.app (I.obj m)) h
  change τ.app (P.obj (I.obj m)) = σ.app (P.obj (I.obj m)) at hh
  apply (cancel_mono (G.map (adj.unit.app m))).mp
  rw [← τ.naturality, ← σ.naturality]
  erw [hh]
  rfl

end Paper18.Category.ModuleFunctor
