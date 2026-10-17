import Paper18.Category.TannakianSignKernelRepresentation
import Paper18.Category.TannakianSignKernelPullback
import Paper18.Category.TannakianBasic

/-! # Actual Tannakian centers of positive sign kernels

The finite quotient group is constructed from the central element recovered
from the actual tensor character on the actual representation category.
Its actual representation inflation has exactly the required transparent image.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.TannakianSignKernel
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] [BraidedCategory C]
  [HasFiniteBiproducts C]
  {G : Type} [Group G] [Fintype G] (T : TannakianCenter C G)
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]

abbrev restrictedCharacter := pullbackCharacter T.inclusion χ
abbrev PositiveCenterGroup := KernelGroup (restrictedCharacter T χ)

def quotientInto : FDRep ℂ (PositiveCenterGroup T χ) ⥤ C :=
  inflate (annihilator (restrictedCharacter T χ)) ⋙ T.inclusion

instance quotientInto_additive : (quotientInto T χ).Additive := by
  dsimp [quotientInto]; infer_instance
instance quotientInto_linear : (quotientInto T χ).Linear ℂ := by
  dsimp [quotientInto]; infer_instance
instance quotientInto_braided : (quotientInto T χ).Braided := by
  dsimp [quotientInto]; infer_instance

lemma quotientInto_positive (V : FDRep ℂ (PositiveCenterGroup T χ)) :
    SignKernel.positiveProperty χ ((quotientInto T χ).obj V) := by
  have hp := (trivialOn_iff_component_id (restrictedCharacter T χ) _).mp
    (inflate_trivial (annihilator (restrictedCharacter T χ)) V)
  apply (SignKernel.mem_positive χ _).mpr
  change χ.hom.app (T.inclusion.obj ((inflate (annihilator (restrictedCharacter T χ))).obj V)) = _
  calc
    _ = T.inclusion.map ((restrictedCharacter T χ).hom.app
        ((inflate (annihilator (restrictedCharacter T χ))).obj V)) :=
      (map_pullbackCharacter T.inclusion χ _).symm
    _ = T.inclusion.map (𝟙 _) := congrArg T.inclusion.map hp
    _ = _ := T.inclusion.map_id _

/-- The actual quotient representation inclusion into the actual positive kernel. -/
def positiveCenterInclusion : FDRep ℂ (PositiveCenterGroup T χ) ⥤ SignKernel.Positive χ :=
  ObjectProperty.lift (SignKernel.positiveProperty χ) (quotientInto T χ)
    (quotientInto_positive T χ)

instance positiveCenterInclusion_full : (positiveCenterInclusion T χ).Full := by
  dsimp [positiveCenterInclusion, quotientInto]; infer_instance
instance positiveCenterInclusion_faithful : (positiveCenterInclusion T χ).Faithful := by
  dsimp [positiveCenterInclusion, quotientInto]; infer_instance
instance positiveCenterInclusion_additive : (positiveCenterInclusion T χ).Additive where
  map_add := by intros; exact (quotientInto T χ).map_add
instance positiveCenterInclusion_linear : (positiveCenterInclusion T χ).Linear ℂ where
  map_smul f r := (quotientInto T χ).map_smul r f

def positiveCenterInclusionCoreMonoidal : (positiveCenterInclusion T χ).CoreMonoidal where
  εIso := (SignKernel.positiveProperty χ).isoMk (Functor.Monoidal.εIso (quotientInto T χ))
  μIso X Y := (SignKernel.positiveProperty χ).isoMk (Functor.Monoidal.μIso (quotientInto T χ) X Y)
  μIso_hom_natural_left f X := Functor.LaxMonoidal.μ_natural_left (quotientInto T χ) f X
  μIso_hom_natural_right X f := Functor.LaxMonoidal.μ_natural_right (quotientInto T χ) X f
  associativity X Y Z := Functor.LaxMonoidal.associativity (quotientInto T χ) X Y Z
  left_unitality X := Functor.LaxMonoidal.left_unitality (quotientInto T χ) X
  right_unitality X := Functor.LaxMonoidal.right_unitality (quotientInto T χ) X

instance positiveCenterInclusion_monoidal : (positiveCenterInclusion T χ).Monoidal :=
  (positiveCenterInclusionCoreMonoidal T χ).toMonoidal
instance positiveCenterInclusion_braided : (positiveCenterInclusion T χ).Braided where
  braided X Y := Functor.LaxBraided.braided (F := quotientInto T χ) X Y

variable [HasKernels C] [RightRigidCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (hχ : ∀ X : C, χ.hom.app X ≫ χ.hom.app X = 𝟙 X)
  (X : C) (hZ : X ∈ mugerCenter) (hX : χ.hom.app X ≠ 𝟙 X)

include S hχ X hZ hX in
/-- The actual fully faithful braided tensor inclusion has exactly the actual
transparent objects of the actual positive fusion kernel as its essential image. -/
lemma positiveCenterInclusion_image_iff (Y : SignKernel.Positive χ) :
    (positiveCenterInclusion T χ).essImage Y ↔ Y ∈ mugerCenter := by
  have hcenter := SignKernel.transparent_iff_ambient_of_nontrivial_center χ S hχ X hZ hX
  constructor
  · rintro ⟨V, ⟨e⟩⟩
    have hV : (positiveCenterInclusion T χ).obj V ∈ mugerCenter :=
      (hcenter _).mpr (T.transparent _)
    intro Z _
    exact (hV Z (Set.mem_univ _)).of_iso_left e.symm
  · intro hY
    obtain ⟨V, ⟨e⟩⟩ := T.exists_representation Y.obj ((hcenter Y).mp hY)
    have hp : SignKernel.positiveProperty χ (T.inclusion.obj V) :=
      FixedBoundary.homogeneous_iso χ e Y.property
    have hv : (restrictedCharacter T χ).hom.app V = 𝟙 V := by
      apply T.inclusion.map_injective
      rw [map_pullbackCharacter]
      erw [T.inclusion.map_id]
      exact (SignKernel.mem_positive χ _).mp hp
    have hV := (trivialOn_iff_component_id (restrictedCharacter T χ) V).mpr hv
    refine ⟨quotientRepresentation (annihilator (restrictedCharacter T χ)) V hV, ⟨?_⟩⟩
    exact (SignKernel.positiveProperty χ).isoMk
      (T.inclusion.mapIso (inflateQuotientIso (annihilator (restrictedCharacter T χ)) V hV) ≪≫ e)

include S hχ X hZ hX in
/-- The positive sign kernel of a category whose actual center is Rep(G)
has the actual Tannakian center Rep(G/⟨z⟩), where z is recovered from χ. -/
def positiveTannakianCenter :
    TannakianCenter (SignKernel.Positive χ) (PositiveCenterGroup T χ) where
  finite_group := inferInstance
  inclusion := positiveCenterInclusion T χ
  braided := positiveCenterInclusion_braided T χ
  additive := positiveCenterInclusion_additive T χ
  linear := positiveCenterInclusion_linear T χ
  full := positiveCenterInclusion_full T χ
  faithful := positiveCenterInclusion_faithful T χ
  image_iff := positiveCenterInclusion_image_iff T χ S hχ X hZ hX

end Paper18.Category.TannakianSignKernel
