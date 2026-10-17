import Paper18.Category.ModuleBalancingFunctor

/-!
# Nondegenerate multiplication pairings and actual module duality

The input is an actual exact pairing whose cap is multiplication followed
by a counit. It asserts neither pivotality nor sphericality of modules.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u
namespace Paper18.Category.ModuleBalancing
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A : C} [MonObj A]

/-- Actual nondegeneracy of an algebra's multiplication pairing, expressed
by actual cup, cap, and the two snake identities. -/
structure MultiplicationPairing (A : C) [MonObj A] where
  counit : A ⟶ 𝟙_ C
  pairing : ExactPairing A A
  evaluation : @ExactPairing.evaluation C _ _ A A pairing = μ[A] ≫ counit

namespace MultiplicationPairing
variable (P : MultiplicationPairing A)

/-- Commutativity makes the actual multiplication cap braided symmetric. -/
lemma evaluation_braiding [BraidedCategory C] [IsCommMonObj A] :
    (β_ A A).hom ≫ (@ExactPairing.evaluation C _ _ A A P.pairing) =
      @ExactPairing.evaluation C _ _ A A P.pairing := by
  rw [P.evaluation, ← assoc, IsCommMonObj.mul_comm]

/-- The actual multiplication pairing identifies maps to the algebra with
linear functionals on a free left algebra factor. -/
def pairingEquiv (X : C) : (X ⟶ A) ≃ (A ⊗ X ⟶ 𝟙_ C) := by
  letI := P.pairing
  let e : (X ⟶ A) ≃ (X ⟶ A ⊗ 𝟙_ C) :=
    { toFun := fun f => f ≫ (ρ_ A).inv
      invFun := fun f => f ≫ (ρ_ A).hom
      left_inv := by intro f; simp
      right_inv := by intro f; simp }
  exact e.trans (tensorLeftHomEquiv X A A (𝟙_ C)).symm

lemma pairingEquiv_apply {X : C} (f : X ⟶ A) :
    P.pairingEquiv X f = (A ◁ f) ≫ μ[A] ≫ P.counit := by
  change A ◁ (f ≫ (ρ_ A).inv) ≫ (α_ A A (𝟙_ C)).inv ≫
    (@ExactPairing.evaluation C _ _ A A P.pairing) ▷ (𝟙_ C) ≫ (λ_ (𝟙_ C)).hom = _
  rw [P.evaluation]
  monoidal

/-- The Frobenius transpose of an actual module functional. -/
def cofreeMap (M : Mod_ C A) (f : M.X ⟶ 𝟙_ C) : M.X ⟶ A :=
  (P.pairingEquiv M.X).symm (γ[A,M.X] ≫ f)

lemma cofreeMap_spec (M : Mod_ C A) (f : M.X ⟶ 𝟙_ C) :
    (A ◁ P.cofreeMap M f) ≫ μ[A] ≫ P.counit = γ[A,M.X] ≫ f := by
  rw [← P.pairingEquiv_apply]
  exact (P.pairingEquiv M.X).apply_symm_apply _

/-- The transpose is genuinely a module morphism. Its linearity is a
consequence of multiplication associativity and nondegeneracy. -/
lemma cofreeMap_linear (M : Mod_ C A) (f : M.X ⟶ 𝟙_ C) :
    γ[A,M.X] ≫ P.cofreeMap M f = (A ◁ P.cofreeMap M f) ≫ μ[A] := by
  apply (P.pairingEquiv (A ⊗ M.X)).injective
  simp only [P.pairingEquiv_apply, whiskerLeft_comp, assoc]
  rw [P.cofreeMap_spec]
  have ha : A ◁ μ[A] ≫ μ[A] ≫ P.counit =
      (α_ A A A).inv ≫ μ[A] ▷ A ≫ μ[A] ≫ P.counit := by
    simpa only [assoc] using congrArg (fun k => k ≫ P.counit) (MonObj.mul_assoc_flip A)
  rw [ha]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    P.cofreeMap_spec]
  rw [reassoc_of% (InternalModule.mul_smul M)]
  simp only [assoc, Iso.inv_hom_id_assoc]

def cofreeHom (M : Mod_ C A) (f : M.X ⟶ 𝟙_ C) : M ⟶ Mod_.regular A :=
  Mod_.Hom.mk' (P.cofreeMap M f) (P.cofreeMap_linear M f)

lemma cofreeMap_counit (M : Mod_ C A) (f : M.X ⟶ 𝟙_ C) :
    P.cofreeMap M f ≫ P.counit = f := by
  have hs := P.cofreeMap_spec M f
  rw [← assoc, ← P.cofreeMap_linear] at hs
  have hu : RelativeTensor.freeUnit (A := A) M.X ≫ γ[A,M.X] = 𝟙 M.X := by
    unfold RelativeTensor.freeUnit
    rw [assoc, InternalModule.one_smul, Iso.inv_hom_id]
  have hh := congrArg (fun k => RelativeTensor.freeUnit (A := A) M.X ≫ k) hs
  simpa only [← assoc, hu, id_comp] using hh

/-- Frobenius coinduction into the regular module is an actual Hom
equivalence, derived from the perfect multiplication pairing. -/
def homToRegularEquiv (M : Mod_ C A) : (M ⟶ Mod_.regular A) ≃ (M.X ⟶ 𝟙_ C) where
  toFun f := f.hom ≫ P.counit
  invFun := P.cofreeHom M
  left_inv f := by
    apply Mod_.Hom.ext
    apply (P.pairingEquiv M.X).injective
    change P.pairingEquiv M.X (P.cofreeMap M (f.hom ≫ P.counit)) =
      P.pairingEquiv M.X f.hom
    simp only [P.pairingEquiv_apply]
    rw [P.cofreeMap_spec]
    have hf := IsMod_Hom.smul_hom (A := A) (f := f.hom)
    simpa only [assoc] using congrArg (fun k => k ≫ P.counit) hf
  right_inv f := P.cofreeMap_counit M f

end MultiplicationPairing
end Paper18.Category.ModuleBalancing
