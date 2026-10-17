import Paper18.Category.EquivariantAdjunction

/-! # The actual linear induction adjunction -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.WeakAction
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasFiniteBiproducts C] (A : WeakAction G C)
  [∀ g : G, (A.ρ g).Additive] [∀ g : G, (A.ρ g).Linear ℂ]

theorem inductionHom_identity (Z : C) :
    A.inductionHom (A.inductionRetract Z).i = 𝟙 (A.induction Z) := by
  apply Equivariant.Hom.ext
  apply biproduct.hom_ext'
  intro g
  dsimp only [inductionHom, inductionRetract, induction, Equivariant.id_hom]
  rw [biproduct.ι_desc, Functor.map_comp, Category.assoc, A.map_ι_inductionIso]
  have hu := A.mul_one g Z
  have hu' := hu =≫ biproduct.ι (fun k : G => (A.ρ k).obj Z) g
  rw [Category.assoc, biproduct.eqToHom_comp_ι (fun k : G => (A.ρ k).obj Z)
    (_root_.mul_one g)] at hu'
  rw [hu', ← Functor.map_comp_assoc]
  simp
  exact (Category.comp_id _).symm

def inductionHomLinearEquiv (Z : C) (Y : A.Equivariant) :
    (A.induction Z ⟶ Y) ≃ₗ[ℂ] (Z ⟶ Y.obj) where
  toFun h := (A.inductionRetract Z).i ≫ h.hom
  invFun f := A.inductionHom f
  left_inv h := by
    change A.inductionHom ((A.inductionRetract Z).i ≫ h.hom) = h
    rw [← A.inductionHom_comp, A.inductionHom_identity, Category.id_comp]
  right_inv f := A.inductionHom_inclusion f
  map_add' f g := by simp
  map_smul' r f := by simp

theorem finrank_induction_hom (Z : C) (Y : A.Equivariant) :
    Module.finrank ℂ (A.induction Z ⟶ Y) = Module.finrank ℂ (Z ⟶ Y.obj) :=
  (A.inductionHomLinearEquiv Z Y).finrank_eq

end Paper18.Category.WeakAction
