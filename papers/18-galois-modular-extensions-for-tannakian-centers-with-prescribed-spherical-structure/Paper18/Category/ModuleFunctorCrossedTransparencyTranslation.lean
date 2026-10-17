import Paper18.Category.ModuleFunctorCrossedTransparencyBoundary
import Paper18.Category.FixedBoundaryRestriction

/-! # Actual algebra translation is essentially surjective on the neutral component -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u w v' u' w'
namespace Paper18.Category.FixedBoundary
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalPreadditive A] [MonoidalLinear ℂ A]
  [HasKernels A] [HasFiniteBiproducts A] [RightRigidCategory A] [HasCoequalizers A]
  [∀ X Y : A, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (SA : FiniteSemisimpleSkeleton A ι)
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [RightRigidCategory N] [HasCoequalizers N] [HasKernels N] [HasFiniteBiproducts N]
  (i : A ⥤ N) [i.Braided] [i.Full] [i.Faithful] [i.Additive] [i.Linear ℂ]
  (P : BoundaryAutoequivalence i) (R : A) [MonObj R] [IsCommMonObj R]
  {T : N} (B : TensorInverse T)
  (himage : ∀ X : A, Centralizes T (i.obj X))
  (s : SeparableAlgebra R)
  (hfull : ∀ Y : N, Centralizes T Y → ∃ X : A, Nonempty (i.obj X ≅ Y))
  (hR : R ∈ mugerCenter (C := A)) (e : P.functor.obj T ≅ T)


/-- Restriction along an actual boundary algebra isomorphism is actually
essentially surjective on the neutral component. The inverse is restriction
along its actual inverse and the comparison has identity carrier map. -/
theorem neutralTranslationEssSurj (t : R ≅ R) [IsMonHom t.hom] :
    (neutralModuleComap i R B himage t.hom).EssSurj := by
  letI : IsMonHom (i.mapIso t).hom := inferInstanceAs (IsMonHom (i.map t.hom))
  refine ⟨fun X => ?_⟩
  refine ⟨(neutralModuleComap i R B himage t.inv).obj X, ⟨?_⟩⟩
  exact ObjectProperty.isoMk _ (InternalModule.comapCancelIso (i.mapIso t) X.obj)

local notation "chi" => neutralModuleCharacter i R B himage
local notation "Pos" => SignKernel.Positive chi
local notation "Odd" => HomogeneousCategory chi 1
local notation "G" => oddBoundaryModuleEnd SA i P R B himage s hfull e
local notation "Alpha" => ModuleAlphaInduction.negative Pos Odd
variable [RightRigidCategory (Mod_ N (i.obj R))] [Simple (𝟙_ (Mod_ N (i.obj R)))]
  [∀ X Y : Mod_ N (i.obj R), FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w'} [Fintype κ]
  (SD : FiniteSemisimpleSkeleton (Mod_ N (i.obj R)) κ)

include SD hR in
/-- The actual representative is transparent when the actual regular
algebra crosses the chosen odd simple by its actual translation. -/
theorem oddBoundaryRepresentative_mem_mugerCenter
    (t : R ≅ R) [IsMonHom t.hom] (Z : Pos) :
    letI := neutralModuleBraided i R B himage s hfull hR
    ∀ (b : (Alpha).obj Z ≅ G) (n : Odd) [Simple n.obj],
    (doubleBraiding (i.obj R) n.obj.X).hom = i.map t.hom ▷ n.obj.X →
    (doubleBraiding (i.obj R) (Z.obj ⊗ n.obj).X).hom =
      i.map t.hom ▷ (Z.obj ⊗ n.obj).X → Z ∈ mugerCenter := by
  letI := neutralModuleBraided i R B himage s hfull hR
  intro b n hSimple hn hZn
  letI := neutralTranslationEssSurj i R B himage t
  apply representative_mem_mugerCenter_of_translated_tests chi Z
    (neutralModuleComap i R B himage t.hom)
  intro X
  exact oddBoundaryRepresentative_centralizes_translated SA i P R B himage s hfull hR e SD
    t Z X b n hn hZn

end Paper18.Category.FixedBoundary
