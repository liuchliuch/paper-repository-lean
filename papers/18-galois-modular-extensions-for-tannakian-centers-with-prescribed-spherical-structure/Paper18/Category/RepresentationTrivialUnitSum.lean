import Paper18.Category.RepresentationRegularAbsorption
import Paper18.Category.NondegenerateBasic

/-! # Actual finite sums of trivial finite representations -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace Paper18.Category.Representation
variable {G : Type} [Group G] [Fintype G]

local instance : HasFiniteBiproducts (FGModuleCat ℂ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Trivial group action on actual finite-dimensional vector spaces. -/
def trivialFunctor : FGModuleCat ℂ ⥤ FDRep ℂ G where
  obj V := Action.trivial G V
  map f := { hom := f, comm := by intro g; simp [Action.trivial] }

instance trivialFunctorAdditive : (trivialFunctor (G := G)).Additive where
  map_add := by intros; rfl

/-- A choice of finite vector-space basis gives an actual categorical
biproduct isomorphism, transported through the fully faithful forgetful functor. -/
def vectorSpaceUnitSumIso (V : FGModuleCat ℂ) :
    V ≅ ⨁ fun _ : Fin (Module.finrank ℂ V) => (𝟙_ (FGModuleCat ℂ)) := by
  let F := forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)
  let e := (Module.finBasis ℂ V).equivFun
  exact F.preimageIso (e.toModuleIso ≪≫
    (ModuleCat.biproductIsoPi (fun _ : Fin (Module.finrank ℂ V) =>
      ModuleCat.of ℂ ℂ)).symm ≪≫
    (F.mapBiproduct (fun _ : Fin (Module.finrank ℂ V) => 𝟙_ (FGModuleCat ℂ))).symm)

omit [Fintype G] in
/-- A trivial representation is a genuine finite direct sum of tensor units. -/
theorem trivialUnderlying_isUnitSum (V : FDRep ℂ G) : IsUnitSum (trivialUnderlying V) := by
  refine ⟨Module.finrank ℂ V, ⟨?_⟩⟩
  exact (trivialFunctor (G := G)).mapIso (vectorSpaceUnitSumIso V.V) ≪≫
    (trivialFunctor (G := G)).mapBiproduct
      (fun _ : Fin (Module.finrank ℂ V) => 𝟙_ (FGModuleCat ℂ))

end Paper18.Category.Representation
