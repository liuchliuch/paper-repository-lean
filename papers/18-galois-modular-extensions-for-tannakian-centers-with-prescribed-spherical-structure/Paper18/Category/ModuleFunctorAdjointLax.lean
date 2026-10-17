import Mathlib.CategoryTheory.Monoidal.Action.LinearFunctor
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # The actual lax module structure on an ordinary right adjoint -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u v' u' v'' u''
namespace Paper18.Category.ModuleFunctor
open MonoidalLeftAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type u'} [Category.{v'} M] [MonoidalLeftAction C M]
  {N : Type u''} [Category.{v''} N] [MonoidalLeftAction C N]
  {F : M ⥤ N} [F.OplaxLeftLinear C] {G : N ⥤ M} (adj : F ⊣ G)

/-- The lax comparison of the ordinary right adjoint, obtained by taking
the actual mate of the oplax comparison followed by the counit. -/
def rightAdjointLineator (c : C) (n : N) :
    c ⊙ₗ G.obj n ⟶ G.obj (c ⊙ₗ n) :=
  adj.homEquiv _ _ (Functor.OplaxLeftLinear.δₗ F c (G.obj n) ≫ c ⊴ₗ adj.counit.app n)

@[reassoc]
lemma rightAdjointLineator_counit (c : C) (n : N) :
    F.map (rightAdjointLineator adj c n) ≫ adj.counit.app (c ⊙ₗ n) =
      Functor.OplaxLeftLinear.δₗ F c (G.obj n) ≫ c ⊴ₗ adj.counit.app n := by
  exact (adj.homEquiv _ _).symm_apply_apply _

lemma rightAdjointLineator_naturality_left {c c' : C} (f : c ⟶ c') (n : N) :
    f ⊵ₗ G.obj n ≫ rightAdjointLineator adj c' n =
      rightAdjointLineator adj c n ≫ G.map (f ⊵ₗ n) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_right_symm]
  simp only [rightAdjointLineator, Equiv.symm_apply_apply]
  change F.map (f ⊵ₗ G.obj n) ≫
    (Functor.OplaxLeftLinear.δₗ F c' (G.obj n) ≫ c' ⊴ₗ adj.counit.app n) =
    (Functor.OplaxLeftLinear.δₗ F c (G.obj n) ≫ c ⊴ₗ adj.counit.app n) ≫ f ⊵ₗ n
  rw [← assoc, Functor.OplaxLeftLinear.δₗ_naturality_left, assoc, ← action_exchange]
  simp only [assoc]
  rfl

lemma rightAdjointLineator_naturality_right (c : C) {n n' : N} (f : n ⟶ n') :
    c ⊴ₗ G.map f ≫ rightAdjointLineator adj c n' =
      rightAdjointLineator adj c n ≫ G.map (c ⊴ₗ f) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_right_symm]
  simp only [rightAdjointLineator, Equiv.symm_apply_apply]
  change F.map (c ⊴ₗ G.map f) ≫
    (Functor.OplaxLeftLinear.δₗ F c (G.obj n') ≫ c ⊴ₗ adj.counit.app n') =
    (Functor.OplaxLeftLinear.δₗ F c (G.obj n) ≫ c ⊴ₗ adj.counit.app n) ≫ c ⊴ₗ f
  rw [← assoc, Functor.OplaxLeftLinear.δₗ_naturality_right]
  simp only [assoc, ← actionHomRight_comp]
  congr 2
  exact adj.counit.naturality f

lemma rightAdjointLineator_associativity (c d : C) (n : N) :
    rightAdjointLineator adj (c ⊗ d) n ≫ G.map (αₗ c d n).hom =
      (αₗ c d (G.obj n)).hom ≫ c ⊴ₗ rightAdjointLineator adj d n ≫
        rightAdjointLineator adj c (d ⊙ₗ n) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [adj.homEquiv_naturality_right_symm,
    adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_left_symm]
  simp only [rightAdjointLineator, Equiv.symm_apply_apply]
  change (Functor.OplaxLeftLinear.δₗ F (c ⊗ d) (G.obj n) ≫
    (c ⊗ d) ⊴ₗ adj.counit.app n) ≫ (αₗ c d n).hom =
      F.map (αₗ c d (G.obj n)).hom ≫ F.map (c ⊴ₗ rightAdjointLineator adj d n) ≫
        (Functor.OplaxLeftLinear.δₗ F c (G.obj (d ⊙ₗ n)) ≫
          c ⊴ₗ adj.counit.app (d ⊙ₗ n))
  rw [← assoc (F.map (c ⊴ₗ _)),
    Functor.OplaxLeftLinear.δₗ_naturality_right]
  simp only [assoc]
  rw [← actionHomRight_comp, rightAdjointLineator_counit, actionHomRight_comp]
  rw [← Functor.OplaxLeftLinear.δₗ_associativity_assoc]
  simp only [tensor_actionHomRight, Functor.id_obj, assoc, Iso.inv_hom_id, comp_id]

lemma rightAdjointLineator_unitality (n : N) :
    (λₗ[C] (G.obj n)).hom =
      rightAdjointLineator adj (𝟙_ C) n ≫ G.map (λₗ[C] n).hom := by
  apply (adj.homEquiv _ _).symm.injective
  rw [adj.homEquiv_naturality_right_symm]
  simp only [rightAdjointLineator, Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  change F.map (λₗ[C] (G.obj n)).hom ≫ adj.counit.app n =
    (Functor.OplaxLeftLinear.δₗ F (𝟙_ C) (G.obj n) ≫
      (𝟙_ C) ⊴ₗ adj.counit.app n) ≫ (λₗ[C] n).hom
  rw [← Functor.OplaxLeftLinear.δₗ_unitality_hom, assoc,
    actionUnitIso_hom_naturality]
  simp only [assoc]
  rfl

/-- The actual right adjoint of an actual oplax module functor is lax
module linear. All coherence follows from the ordinary adjunction. -/
def rightAdjointLaxLeftLinear : G.LaxLeftLinear C where
  μₗ := rightAdjointLineator adj
  μₗ_naturality_left := rightAdjointLineator_naturality_left adj
  μₗ_naturality_right := rightAdjointLineator_naturality_right adj
  μₗ_associativity := rightAdjointLineator_associativity adj
  μₗ_unitality := rightAdjointLineator_unitality adj

end Paper18.Category.ModuleFunctor
