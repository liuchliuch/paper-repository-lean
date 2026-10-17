import Paper18.Category.SeparableAlgebraQuotient
import Paper18.Category.ModuleFunctorSemisimpleWattsAction

/-! # Actual algebra quotients from split regular-bimodule projections

The splitting is categorical data. Multiplication and the algebra laws are
constructed from the actual regular bimodule; no block-algebra existence or
separability conclusion is supplied as a field.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonObj
universe v u
namespace Paper18.Category.ModuleFunctor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  {R B : D} [MonObj R]

/-- Actual multiplicative descent along a split epimorphism gives a monoid.
The comparison is an equation of actual multiplication morphisms. -/
def monObjOfSplitMultiplication (p : R ⟶ B) (i : B ⟶ R) (hi : i ≫ p = 𝟙 B)
    (m : B ⊗ B ⟶ B) (hm : (p ⊗ₘ p) ≫ m = μ[R] ≫ p) : MonObj B where
  one := η[R] ≫ p
  mul := m
  one_mul := by
    letI : IsSplitEpi ((𝟙_ D) ◁ p) := IsSplitEpi.mk' ⟨(𝟙_ D) ◁ i, by
      rw [← whiskerLeft_comp, hi, whiskerLeft_id]⟩
    apply (cancel_epi ((𝟙_ D) ◁ p)).mp
    calc
      _ = (η[R] ▷ R) ≫ (p ⊗ₘ p) ≫ m := by
        simp only [← id_tensorHom, ← tensorHom_id, ← assoc,
          tensorHom_comp_tensorHom, id_comp, comp_id]
      _ = (λ_ R).hom ≫ p := by rw [hm, ← assoc, MonObj.one_mul]
      _ = _ := (leftUnitor_naturality p).symm
  mul_one := by
    letI : IsSplitEpi (p ▷ (𝟙_ D)) := IsSplitEpi.mk' ⟨i ▷ (𝟙_ D), by
      rw [← comp_whiskerRight, hi, id_whiskerRight]⟩
    apply (cancel_epi (p ▷ (𝟙_ D))).mp
    calc
      _ = (R ◁ η[R]) ≫ (p ⊗ₘ p) ≫ m := by
        simp only [← id_tensorHom, ← tensorHom_id, ← assoc,
          tensorHom_comp_tensorHom, id_comp, comp_id]
      _ = (ρ_ R).hom ≫ p := by rw [hm, ← assoc, MonObj.mul_one]
      _ = _ := (rightUnitor_naturality p).symm
  mul_assoc := by
    letI : IsSplitEpi ((p ⊗ₘ p) ⊗ₘ p) := IsSplitEpi.mk' ⟨(i ⊗ₘ i) ⊗ₘ i, by
      simp only [tensorHom_comp_tensorHom, hi, id_tensorHom_id]⟩
    apply (cancel_epi ((p ⊗ₘ p) ⊗ₘ p)).mp
    calc
      _ = (μ[R] ▷ R) ≫ (p ⊗ₘ p) ≫ m := by
        rw [← assoc, tensorHom_comp_whiskerRight, hm, ← whiskerRight_comp_tensorHom]
        simp only [assoc, hm]
      _ = (α_ R R R).hom ≫ (R ◁ μ[R]) ≫ μ[R] ≫ p := by
        rw [hm, ← assoc, MonObj.mul_assoc]
        simp only [assoc]
      _ = _ := by
        rw [associator_naturality_assoc, tensorHom_comp_whiskerLeft_assoc,
          hm, ← whiskerLeft_comp_tensorHom_assoc, hm]

open MonoidalOpposite
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

variable (Q : Bimodules R) (q : Retract Q (wattsRegular (R := R)))

/-- The actual quotient and section underlying the two-sided retract. -/
def blockProjection : R ⟶ Q.X.X := q.r.hom.hom
def blockInclusion : Q.X.X ⟶ R := q.i.hom.hom

@[reassoc] lemma blockInclusion_projection :
    blockInclusion Q q ≫ blockProjection Q q = 𝟙 Q.X.X :=
  congrArg (fun f : Q ⟶ Q => f.hom.hom) q.retract

/-- Multiplication is descended using the actual section. -/
def blockMultiplication : Q.X.X ⊗ Q.X.X ⟶ Q.X.X :=
  (blockInclusion Q q ⊗ₘ blockInclusion Q q) ≫ μ[R] ≫ blockProjection Q q

/-- Two-sided linearity of the actual projection proves multiplicative descent. -/
lemma blockProjection_mul :
    (blockProjection Q q ⊗ₘ blockProjection Q q) ≫ blockMultiplication Q q =
      μ[R] ≫ blockProjection Q q := by
  let e : R ⟶ R := blockProjection Q q ≫ blockInclusion Q q
  have hL : R ◁ e ≫ μ[R] = μ[R] ≫ e := by
    exact ((q.r ≫ q.i).hom.isMod_Hom.smul_hom).symm
  have hR : e ▷ R ≫ μ[R] = μ[R] ≫ e := by
    exact (congrArg Mod_.Hom.hom (q.r ≫ q.i).isMod_Hom.smul_hom).symm
  have hep : e ≫ blockProjection Q q = blockProjection Q q := by
    dsimp only [e]
    rw [assoc, blockInclusion_projection, comp_id]
  calc
    _ = (e ⊗ₘ e) ≫ μ[R] ≫ blockProjection Q q := by
      simp only [blockMultiplication, ← assoc, tensorHom_comp_tensorHom]
      rfl
    _ = _ := by
      rw [MonoidalCategory.tensorHom_def, assoc, reassoc_of% hL, reassoc_of% hR, assoc, hep]
      simp only [blockInclusion_projection, comp_id]

/-- Restricting the actual quotient's left multiplication returns the old left action. -/
lemma blockProjection_left_action :
    (blockProjection Q q ▷ Q.X.X) ≫ blockMultiplication Q q = γ[R,Q.X.X] := by
  letI : IsSplitEpi (R ◁ blockProjection Q q) := IsSplitEpi.mk'
    ⟨R ◁ blockInclusion Q q, by
      rw [← whiskerLeft_comp, blockInclusion_projection, whiskerLeft_id]⟩
  apply (cancel_epi (R ◁ blockProjection Q q)).mp
  calc
    _ = (blockProjection Q q ⊗ₘ blockProjection Q q) ≫ blockMultiplication Q q := by
      rw [← assoc, ← MonoidalCategory.tensorHom_def']
    _ = μ[R] ≫ blockProjection Q q := blockProjection_mul Q q
    _ = _ := q.r.hom.isMod_Hom.smul_hom

/-- Restricting actual right multiplication returns the old right action. -/
lemma blockProjection_right_action :
    (Q.X.X ◁ blockProjection Q q) ≫ blockMultiplication Q q = γ[mop R,Q.X].hom := by
  letI : IsSplitEpi (blockProjection Q q ▷ R) := IsSplitEpi.mk'
    ⟨blockInclusion Q q ▷ R, by
      rw [← comp_whiskerRight, blockInclusion_projection, id_whiskerRight]⟩
  apply (cancel_epi (blockProjection Q q ▷ R)).mp
  calc
    _ = (blockProjection Q q ⊗ₘ blockProjection Q q) ≫ blockMultiplication Q q := by
      rw [← assoc, ← MonoidalCategory.tensorHom_def]
    _ = μ[R] ≫ blockProjection Q q := blockProjection_mul Q q
    _ = _ := congrArg Mod_.Hom.hom q.r.isMod_Hom.smul_hom

/-- Every actual summand of the regular bimodule has a derived quotient algebra. -/
def blockMonObj : MonObj Q.X.X :=
  monObjOfSplitMultiplication (blockProjection Q q) (blockInclusion Q q)
    (blockInclusion_projection Q q) (blockMultiplication Q q) (blockProjection_mul Q q)

/-- Its actual projection is an actual algebra homomorphism. -/
def blockProjection_isMonHom : letI := blockMonObj Q q; IsMonHom (blockProjection Q q) := by
  letI := blockMonObj Q q
  exact ⟨rfl, (blockProjection_mul Q q).symm⟩

/-- Actual regular-bimodule retracts of separable algebras are separable
quotient algebras, without any pivotal assumption. -/
def blockSeparable (S : SeparableAlgebra R) : letI := blockMonObj Q q; SeparableAlgebra Q.X.X := by
  letI := blockMonObj Q q
  letI := blockProjection_isMonHom Q q
  letI : Epi (blockProjection Q q) := (SplitEpi.mk (blockInclusion Q q)
    (blockInclusion_projection Q q)).epi
  exact S.quotient (blockProjection Q q)

end Paper18.Category.ModuleFunctor
