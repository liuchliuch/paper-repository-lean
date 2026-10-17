import Paper18.Category.ModuleFunctorCrossedTransparencyRegular
import Paper18.Category.ModuleFunctorCrossedTransparencyUnit
import Paper18.Category.FixedBoundaryNeutralNondegenerate

/-! # Actual odd boundary comparison from the actual regular-algebra representative

The representative, its two-sided inverse and its centrality are derived.
Nondegeneracy forces it to be the actual unit; genuine strong alpha
induction supplies the native module-natural comparison with the identity.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj MonoidalLeftAction
universe v u w v' u' w'
namespace Paper18.Category.FixedBoundary
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalPreadditive A] [MonoidalLinear ℂ A]
  [HasKernels A] [HasFiniteBiproducts A] [RightRigidCategory A] [HasCoequalizers A]
  [∀ X Y : A, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (SA : FiniteSemisimpleSkeleton A ι)
  (F0 : FDRep ℂ RepresentationZ2.H ⥤ A) [F0.Braided] [F0.Additive] [F0.Linear ℂ]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [RightRigidCategory N] [HasCoequalizers N] [HasKernels N] [HasFiniteBiproducts N]
  (i : A ⥤ N) [i.Braided] [i.Full] [i.Faithful] [i.Additive] [i.Linear ℂ]
  (P : BoundaryAutoequivalence i)
variable (R : A) [MonObj R] [IsCommMonObj R]
  (qR : R ≅ regularAlgebra F0) [IsMonHom qR.hom]
  (B : TensorInverse (i.obj (F0.obj RepresentationZ2.signRep)))
  (himage : ∀ X : A, Centralizes (i.obj (F0.obj RepresentationZ2.signRep)) (i.obj X))
  (s : SeparableAlgebra R)
  (hfull : ∀ Y : N, Centralizes (i.obj (F0.obj RepresentationZ2.signRep)) Y →
    ∃ X : A, Nonempty (i.obj X ≅ Y))
  (hR : R ∈ mugerCenter (C := A))
  (e : P.functor.obj (i.obj (F0.obj RepresentationZ2.signRep)) ≅
    i.obj (F0.obj RepresentationZ2.signRep))
  [modRigid : RightRigidCategory (Mod_ N (i.obj R))] [modUnit : Simple (𝟙_ (Mod_ N (i.obj R)))]
  [modFinite : ∀ X Y : Mod_ N (i.obj R), FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w'} [Fintype κ]
  (SD : FiniteSemisimpleSkeleton (Mod_ N (i.obj R)) κ)

local notation "chi" => neutralModuleCharacter i R B himage
local notation "Pos" => SignKernel.Positive chi
local notation "Odd" => HomogeneousCategory chi 1
local notation "G" => oddBoundaryModuleEnd SA i P R B himage s hfull e
local notation "Alpha" => ModuleAlphaInduction.negative Pos Odd


include SD hR qR modRigid modUnit modFinite in
/-- Every actual specified boundary pair has an actual comparison to the
identity on its odd component once the actual neutral component is
nondegenerate. The actual odd label follows from nontrivial monodromy. -/
theorem regularOddBoundaryComparison
    (q : i.obj (F0.obj RepresentationZ2.signRep) ⊗ i.obj (F0.obj RepresentationZ2.signRep) ≅ 𝟙_ N)
    (W : Mod_ N (i.obj R)) (hW : (chi).hom.app W ≠ 𝟙 W) :
    letI := neutralModuleBraided i R B himage s hfull hR
    IsNondegenerate (C := Pos) → Nonempty (G ≅ 𝟙_ (ModuleAlphaInduction.End Pos Odd)) := by
  letI := neutralModuleBraided i R B himage s hfull hR
  intro hC
  have hchi : ∀ X : Mod_ N (i.obj R), (chi).hom.app X ≫ (chi).hom.app X = 𝟙 X :=
    B.moduleMonodromy_involutive (i.obj R) (himage R) q
  obtain ⟨j, hj⟩ := SignKernel.exists_negative_label SD chi hchi W hW
  have hj' : Homogeneous chi 1 (SD.simpleObject (SD.label W j)) := by
    simpa only [Homogeneous, paritySign_one, neg_one_smul] using hj
  let n : Odd := ⟨SD.simpleObject (SD.label W j), hj'⟩
  letI : Simple n.obj := SD.simple _
  letI : (G).toFunctor.IsEquivalence :=
    (oddBoundaryModuleEquivalence i P R B himage s hfull e).isEquivalence_functor
  obtain ⟨Z, ⟨aZ⟩, ⟨b⟩⟩ := exists_invertible_homogeneous_representer SD chi 1
    (neutralCenterFunctor i R B himage s hfull hR) (Iso.refl _)
    (neutralNegativeCentralCompatibility i R B himage s hfull hR)
    (SD.label W j) hj' G
  have hZ := regularOddBoundaryRepresentative_transparent SA F0 i P R qR B himage s hfull hR e SD
    Z b n
  obtain ⟨qZ⟩ := invertible_transparent_unit SD chi hC Z aZ hZ
  exact ⟨negativeRepresenterComparison chi 1 G Z b qZ⟩

end Paper18.Category.FixedBoundary
