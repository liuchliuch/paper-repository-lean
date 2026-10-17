import Paper18.Category.RepresentationFunctionAlgebra
import Paper18.Category.SeparableModules
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Actual regular absorption for finite group representations

The change of variables `s(g) ↦ ρ(g⁻¹)s(g)` trivializes the representation
factor of the free `Fun(G)` module.  This is an equivariant, `Fun(G)`-linear
isomorphism of actual internal modules.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct MonObj
namespace Paper18.Category.Representation
variable {G : Type} [Group G] [Fintype G]

/-- The trivial representation on the actual underlying vector space. -/
def trivialUnderlying (V : FDRep ℂ G) : FDRep ℂ G :=
  FDRep.of (_root_.Representation.trivial ℂ G V)

/-- A tensor with the finite function space is an actual vector-valued function. -/
def tensorFunctionEquiv (V : FDRep ℂ G) :
    ((G → ℂ) ⊗[ℂ] V) ≃ₗ[ℂ] (G → V) :=
  (TensorProduct.comm ℂ (G → ℂ) V).trans
    (TensorProduct.piScalarRight ℂ ℂ V G)

@[simp] lemma tensorFunctionEquiv_tmul (V : FDRep ℂ G) (f : G → ℂ) (v : V) (g : G) :
    tensorFunctionEquiv V (f ⊗ₜ v) g = f g • v := by
  simp [tensorFunctionEquiv]

/-- Pointwise application of the inverse representation matrix. -/
def untwistFunctionEquiv (V : FDRep ℂ G) : (G → V) ≃ₗ[ℂ] (G → V) where
  toFun f g := V.ρ g⁻¹ (f g)
  invFun f g := V.ρ g (f g)
  left_inv f := by
    funext g
    change (V.ρ g * V.ρ g⁻¹) (f g) = f g
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  right_inv f := by
    funext g
    change (V.ρ g⁻¹ * V.ρ g) (f g) = f g
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  map_add' f h := by ext g; exact map_add _ _ _
  map_smul' c f := by ext g; exact map_smul _ _ _

/-- The underlying actual vector-space isomorphism of regular absorption. -/
def regularAbsorptionLinear (V : FDRep ℂ G) :
    ((G → ℂ) ⊗[ℂ] V) ≃ₗ[ℂ] ((G → ℂ) ⊗[ℂ] V) :=
  (tensorFunctionEquiv V).trans ((untwistFunctionEquiv V).trans
    (tensorFunctionEquiv V).symm)

@[simp] lemma tensorFunctionEquiv_regularAbsorption (V : FDRep ℂ G)
    (z : (G → ℂ) ⊗[ℂ] V) (g : G) :
    tensorFunctionEquiv V (regularAbsorptionLinear V z) g =
      V.ρ g⁻¹ (tensorFunctionEquiv V z g) := by
  simp [regularAbsorptionLinear, untwistFunctionEquiv]

lemma tensorFunctionEquiv_action (V : FDRep ℂ G) (g : G)
    (z : (G → ℂ) ⊗[ℂ] V) (h : G) :
    tensorFunctionEquiv V
      (TensorProduct.map (functionAction g) (V.ρ g) z) h =
      V.ρ g (tensorFunctionEquiv V z (g⁻¹ * h)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f v => simp
  | add x y hx hy => simp [hx, hy]

lemma tensorFunctionEquiv_trivialAction (V : FDRep ℂ G) (g : G)
    (z : (G → ℂ) ⊗[ℂ] V) (h : G) :
    tensorFunctionEquiv V
      (TensorProduct.map (functionAction g) LinearMap.id z) h =
      tensorFunctionEquiv V z (g⁻¹ * h) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f v => simp
  | add x y hx hy => simp [hx, hy]

/-- The regular absorption map is an actual representation morphism. -/
def regularAbsorptionHom (V : FDRep ℂ G) :
    functions (G := G) ⊗ V ⟶ functions (G := G) ⊗ trivialUnderlying V where
  hom := ModuleCat.ofHom (regularAbsorptionLinear V).toLinearMap
  comm g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply (tensorFunctionEquiv V).injective
    ext h
    change tensorFunctionEquiv V
        (regularAbsorptionLinear V (TensorProduct.map (functionAction g) (V.ρ g) z)) h =
      tensorFunctionEquiv V
        (TensorProduct.map (functionAction g) LinearMap.id (regularAbsorptionLinear V z)) h
    rw [tensorFunctionEquiv_regularAbsorption, tensorFunctionEquiv_action,
      tensorFunctionEquiv_trivialAction, tensorFunctionEquiv_regularAbsorption]
    change (V.ρ h⁻¹ * V.ρ g) _ = V.ρ (g⁻¹ * h)⁻¹ _
    rw [← map_mul, mul_inv_rev, inv_inv]

/-- Regular absorption is an actual isomorphism of representations. -/
def regularAbsorptionIso (V : FDRep ℂ G) :
    functions (G := G) ⊗ V ≅ functions (G := G) ⊗ trivialUnderlying V :=
  Action.mkIso (regularAbsorptionLinear V).toFGModuleCatIso
    (regularAbsorptionHom V).comm

lemma tensorFunctionEquiv_freeAction (V : FDRep ℂ G) (a : G → ℂ)
    (z : (G → ℂ) ⊗[ℂ] V) (g : G) :
    tensorFunctionEquiv V
      ((γ[functions (G := G),(InternalModule.free (functions (G := G)) V).X]).hom.hom
        (a ⊗ₜ z)) g = a g • tensorFunctionEquiv V z g := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, map_zero, Pi.zero_apply, smul_zero]
  | tmul f v =>
    change tensorFunctionEquiv V ((a * f) ⊗ₜ v) g = a g • tensorFunctionEquiv V (f ⊗ₜ v) g
    simp only [tensorFunctionEquiv_tmul, Pi.mul_apply, mul_smul]
  | add x y hx hy =>
    simp only [TensorProduct.tmul_add, map_add, Pi.add_apply, hx, hy, smul_add]

/-- The same change of variables commutes with the actual free-module action. -/
theorem regularAbsorption_linear (V : FDRep ℂ G) :
    γ[functions (G := G),(InternalModule.free (functions (G := G)) V).X] ≫
        (regularAbsorptionIso V).hom =
      (functions (G := G) ◁ (regularAbsorptionIso V).hom) ≫
        γ[functions (G := G),(InternalModule.free (functions (G := G)) (trivialUnderlying V)).X] := by
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro z
  apply (tensorFunctionEquiv V).injective
  ext g
  change tensorFunctionEquiv V
      (regularAbsorptionLinear V
        ((γ[functions (G := G),(InternalModule.free (functions (G := G)) V).X]).hom.hom
          (a ⊗ₜ z))) g =
    tensorFunctionEquiv V
      ((γ[functions (G := G),(InternalModule.free (functions (G := G)) V).X]).hom.hom
        (a ⊗ₜ regularAbsorptionLinear V z)) g
  rw [tensorFunctionEquiv_regularAbsorption, tensorFunctionEquiv_freeAction,
    tensorFunctionEquiv_freeAction, tensorFunctionEquiv_regularAbsorption]
  exact map_smul _ _ _

/-- An actual isomorphism of free internal modules over `Fun(G)`. -/
def regularAbsorptionModuleIso (V : FDRep ℂ G) :
    InternalModule.free (functions (G := G)) V ≅
      InternalModule.free (functions (G := G)) (trivialUnderlying V) := by
  letI : ModObj (functions (G := G)) (functions (G := G) ⊗ V) :=
    (InternalModule.free (functions (G := G)) V).mod
  letI : ModObj (functions (G := G)) (functions (G := G) ⊗ trivialUnderlying V) :=
    (InternalModule.free (functions (G := G)) (trivialUnderlying V)).mod
  letI : IsMod_Hom (functions (G := G)) (regularAbsorptionIso V).hom :=
    ⟨regularAbsorption_linear V⟩
  exact
    { hom := ⟨(regularAbsorptionIso V).hom⟩
      inv := ⟨(regularAbsorptionIso V).inv⟩
      hom_inv_id := Mod_.Hom.ext (regularAbsorptionIso V).hom_inv_id
      inv_hom_id := Mod_.Hom.ext (regularAbsorptionIso V).inv_hom_id }

end Paper18.Category.Representation
