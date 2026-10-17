import Paper18.Category.ModuleFunctorAdjointStrong
import Paper18.Category.ModuleAlphaInductionComposition

/-! # The actual adjunction unit and counit are module natural -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u v' u' v'' u''
namespace Paper18.Category.ModuleFunctor
open MonoidalLeftAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type u'} [Category.{v'} M] [MonoidalLeftAction C M]
  {N : Type u''} [Category.{v''} N] [MonoidalLeftAction C N]
  (F : M ⥤ N) [F.LeftLinear C] {G : N ⥤ M} (adj : F ⊣ G)

/-- The actual adjunction unit intertwines the derived lineator. -/
lemma rightAdjointLineator_unit (c : C) (m : M) :
    (c ⊴ₗ adj.unit.app m) ≫ rightAdjointLineator adj c (F.obj m) ≫
      G.map (Functor.LaxLeftLinear.μₗ F c m) = adj.unit.app (c ⊙ₗ m) := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, F.map_comp, assoc]
  have hc := adj.counit.naturality (Functor.LaxLeftLinear.μₗ F c m)
  change F.map (G.map (Functor.LaxLeftLinear.μₗ F c m)) ≫
    adj.counit.app (F.obj (c ⊙ₗ m)) =
      adj.counit.app (c ⊙ₗ F.obj m) ≫ Functor.LaxLeftLinear.μₗ F c m at hc
  have hd := Functor.OplaxLeftLinear.δₗ_naturality_right F c (adj.unit.app m)
  change F.map (c ⊴ₗ adj.unit.app m) ≫
    Functor.OplaxLeftLinear.δₗ F c (G.obj (F.obj m)) =
      Functor.OplaxLeftLinear.δₗ F c m ≫ c ⊴ₗ F.map (adj.unit.app m) at hd
  rw [hc, rightAdjointLineator_counit_assoc, ← assoc, hd]
  simp only [assoc, adj.left_triangle_components]
  rw [← actionHomRight_comp_assoc, adj.left_triangle_components,
    actionHomRight_id, id_comp, Functor.LeftLinear.δₗ_comp_μₗ]

/-- The actual adjunction counit intertwines the derived lineator. -/
lemma rightAdjointLineator_counit_module (c : C) (n : N) :
    Functor.LaxLeftLinear.μₗ F c (G.obj n) ≫
      F.map (rightAdjointLineator adj c n) ≫ adj.counit.app (c ⊙ₗ n) =
        c ⊴ₗ adj.counit.app n := by
  rw [rightAdjointLineator_counit]
  simp

variable [RightRigidCategory C]

/-- With the actual derived strong structure, the ordinary adjunction
unit is an actual module natural transformation. -/
def rightAdjointUnit_moduleNatural :
    letI := rightAdjointLeftLinear (C := C) F adj
    IsModuleNatural C adj.unit := by
  letI := rightAdjointLeftLinear (C := C) F adj
  refine ⟨fun c m => ?_⟩
  change 𝟙 (c ⊙ₗ m) ≫ adj.unit.app (c ⊙ₗ m) =
    (c ⊴ₗ adj.unit.app m) ≫ rightAdjointLineator adj c (F.obj m) ≫
      G.map (Functor.LaxLeftLinear.μₗ F c m)
  simpa only [id_comp] using (rightAdjointLineator_unit F adj c m).symm

/-- With the actual derived strong structure, the ordinary adjunction
counit is an actual module natural transformation. -/
def rightAdjointCounit_moduleNatural :
    letI := rightAdjointLeftLinear (C := C) F adj
    IsModuleNatural C adj.counit := by
  letI := rightAdjointLeftLinear (C := C) F adj
  refine ⟨fun c n => ?_⟩
  change (Functor.LaxLeftLinear.μₗ F c (G.obj n) ≫
    F.map (rightAdjointLineator adj c n)) ≫ adj.counit.app (c ⊙ₗ n) =
      (c ⊴ₗ adj.counit.app n) ≫ 𝟙 (c ⊙ₗ n)
  exact (assoc _ _ _).trans
    ((rightAdjointLineator_counit_module F adj c n).trans (comp_id _).symm)

end Paper18.Category.ModuleFunctor
