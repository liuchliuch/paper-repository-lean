import Paper18.Category.DiagonalAlgebraEtale
import Paper18.Category.DiagonalAlgebraFPdim
import Paper18.Category.DiagonalAlgebraPairingTransport
import Paper18.Category.TannakianDeequivariantization

/-! # Actual tensor transport of the canonical diagonal algebra

A genuine tensor embedding transports the constructed algebra, its actual
perfect multiplication pairing, and its proved separability section. Its
actual diagonal decomposition is transported through finite biproducts.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u w v' u' w'
namespace Paper18.Category.DiagonalAlgebra
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [HasFiniteBiproducts D]
  (H : DeligneProduct C C ⥤ D) [H.Monoidal] [H.Additive] [H.Linear ℂ]

/-- The actual canonical diagonal algebra embedded in an ambient tensor category. -/
def mappedCanonicalAlgebra : D := H.obj (canonicalAlgebra S)

instance mappedCanonicalAlgebraMonObj : MonObj (mappedCanonicalAlgebra S H) :=
  Functor.monObjObj (F := H) (canonicalAlgebra S)

/-- The actual diagonal decomposition survives tensor transport. -/
def mappedCanonicalAlgebraIso : mappedCanonicalAlgebra S H ≅
    ⨁ fun i : ι => H.obj (DeligneProduct.pairObject S S i (S.dualLabel i)) :=
  H.mapIso (canonicalAlgebraIso S) ≪≫
    mapFiniteBiproductIso H (fun i : ι => DeligneProduct.pairObject S S i (S.dualLabel i))

/-- The actual perfect multiplication pairing of the embedded algebra. -/
def mappedCanonicalMultiplicationPairing :
    ModuleBalancing.MultiplicationPairing (mappedCanonicalAlgebra S H) :=
  (canonicalMultiplicationPairing S).map H

/-- Its actual Frobenius counit is still normalized. -/
lemma mappedCanonicalPairing_one_counit :
    η[mappedCanonicalAlgebra S H] ≫ (mappedCanonicalMultiplicationPairing S H).counit = 𝟙 _ :=
  (canonicalMultiplicationPairing S).map_one_counit H (canonicalPairing_one_counit S)

/-- The proved actual bimodule separability section is transported. -/
def mappedCanonicalSeparable (J : PivotalStructure C) (hJ : J.Spherical) :
    SeparableAlgebra (mappedCanonicalAlgebra S H) :=
  (canonicalSeparable S J hJ).map H

/-- Full actual tensor embeddings preserve actual connectedness. -/
lemma mappedCanonicalAlgebra_connected [H.Full] [H.Faithful] :
    Module.finrank ℂ (𝟙_ D ⟶ mappedCanonicalAlgebra S H) = 1 :=
  connected_map H (canonicalAlgebra S) (canonicalAlgebra_connected S)

/-- The actual embedded algebra is commutative whenever the embedding
preserves the specified reverse-second braiding. -/
def mappedCanonicalAlgebra_commutative [BraidedCategory D]
    (hH : ∀ X Y : DeligneProduct C C,
      (letI : BraidedCategory (DeligneProduct C C) := Drinfeld.deligneReverseSecondBraiding C;
        Functor.LaxMonoidal.μ H X Y ≫ H.map (β_ X Y).hom) =
      (β_ (H.obj X) (H.obj Y)).hom ≫ Functor.LaxMonoidal.μ H Y X) :
    IsCommMonObj (mappedCanonicalAlgebra S H) := by
  letI : BraidedCategory (DeligneProduct C C) := Drinfeld.deligneReverseSecondBraiding C
  letI : H.LaxBraided := { braided := hH }
  letI := canonicalAlgebra_commutative S
  exact Functor.isCommMonObj_obj (F := H) (M := canonicalAlgebra S)

section Dimensions
variable [RightRigidCategory D] [HasKernels D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [Simple (𝟙_ D)]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)

/-- Intrinsic FP dimension of the actual embedded diagonal. -/
theorem mappedCanonicalAlgebra_fpdim :
    T.fpdim (mappedCanonicalAlgebra S H) = S.fusionBasis.totalFPdim := by
  letI := DeligneProduct.hasKernels S S
  letI := DeligneProduct.simpleUnit S S
  unfold mappedCanonicalAlgebra
  rw [(DeligneProduct.skeleton S S).fpdim_map T H]
  exact canonicalAlgebra_fpdim S

end Dimensions
end Paper18.Category.DiagonalAlgebra
