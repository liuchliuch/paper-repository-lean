import Paper18.Category.PointedRelativeCenterObstructionKernelAction
import Paper18.Category.PointedSkeleton
import Paper18.Category.FusionSubcategoryBasic
import Paper18.Category.PointedRelativeCenterObstructionNeutral

/-! # Actual finite semisimple coset categories with explicit homogeneous lines -/
noncomputable section
set_option quotPrecheck false
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped BigOperators
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G] (p : Γ →* G)
local notation "Vec" => PointedVec.{0} (Additive Γ)

lemma supported_of_retract {g : G} {X Y : Vec} (r : Retract X Y)
    (hY : Supported p g Y) : Supported p g X := by
  intro a ha
  apply (IsZero.iff_id_eq_zero _).mpr
  have hr := congrFun r.retract a
  change r.i a ≫ r.r a = 𝟙 (X a) at hr
  rw [← hr, (hY a ha).eq_of_tgt (r.i a) 0, zero_comp]

lemma supported_biproduct {g : G} {J : Type} [Fintype J]
    (f : J → Vec) (hf : ∀ j, Supported p g (f j)) : Supported p g (⨁ f) := by
  intro a ha
  apply (IsZero.iff_id_eq_zero _).mpr
  have ht := congrFun (biproduct.total (f := f)) a
  let ev : ((⨁ f) ⟶ (⨁ f)) →+ (((⨁ f) a) ⟶ ((⨁ f) a)) :=
    { toFun := fun q => q a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ j, biproduct.π f j ≫ biproduct.ι f j) = 𝟙 ((⨁ f) a) at ht
  rw [map_sum] at ht
  change (∑ j, (biproduct.π f j) a ≫ (biproduct.ι f j) a) = 𝟙 ((⨁ f) a) at ht
  rw [← ht]
  apply Finset.sum_eq_zero
  intro j _
  rw [(hf j a ha).eq_of_tgt ((biproduct.π f j) a) 0, zero_comp]

instance supported_isAdditive (g : G) : IsAdditiveFullProperty (Supported p g : ObjectProperty Vec) where
  of_retract := supported_of_retract p
  biproduct := supported_biproduct p

/-- The actual full category of graded vectors supported in one quotient coset. -/
abbrev CosetVec (g : G) := ObjectProperty.FullSubcategory (Supported p g : ObjectProperty Vec)

/-- The actual homogeneous line lies in exactly its actual quotient degree. -/
lemma supported_simple_iff (g : G) (a : Additive Γ) :
    Supported p g (PointedVec.simpleObject (Additive Γ) a) ↔ p a.toMul = g := by
  constructor
  · intro h
    by_contra ha
    have hz := h a ha
    have hz' : IsZero (FGModuleCat.of ℂ ℂ) :=
      hz.of_iso (PointedVec.simpleFiberIso (Additive Γ) a).symm
    letI := PointedVec.simple_complex_line
    exact Simple.not_isZero _ hz'
  · intro ha b hb
    apply PointedVec.simpleFiber_isZero
    intro he
    subst b
    exact hb ha

/-- Relabel a genuine finite semisimple skeleton along an actual index
bijection; the decompositions are transported by actual biproduct isos. -/
def kernelActionReindexSkeleton {C : Type*} [Category C] [Preadditive C]
    [HasFiniteBiproducts C] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : FiniteSemisimpleSkeleton C ι) (e : κ ≃ ι) : FiniteSemisimpleSkeleton C κ where
  simpleObject i := S.simpleObject (e i)
  simple i := S.simple (e i)
  iso_injective i j h := e.injective (S.iso_injective _ _ h)
  length := S.length
  label X i := e.symm (S.label X i)
  decomposition X := S.decomposition X ≪≫
    biproduct.mapIso (fun i => eqToIso
      (congrArg S.simpleObject (e.apply_symm_apply (S.label X i))).symm)

/-- The explicit homogeneous degree labels for the actual coset category. -/
def cosetSimpleIndex (g : G) := {a : Γ // p a = g}
instance cosetSimpleIndex_fintype (g : G) : Fintype (cosetSimpleIndex p g) := inferInstanceAs
  (Fintype {a : Γ // p a = g})

def cosetSimpleIndexEquiv (g : G) : cosetSimpleIndex p g ≃
    {a : Additive Γ // Supported p g (PointedVec.simpleObject (Additive Γ) a)} where
  toFun a := ⟨Additive.ofMul a.val, (supported_simple_iff p g _).mpr a.property⟩
  invFun a := ⟨a.val.toMul, (supported_simple_iff p g _).mp a.property⟩
  left_inv a := by apply Subtype.ext; rfl
  right_inv a := by apply Subtype.ext; rfl

/-- A real finite semisimple skeleton whose simple representatives are the
actual concentrated lines in the specified quotient coset. -/
def cosetSkeleton (g : G) : FiniteSemisimpleSkeleton (CosetVec p g) (cosetSimpleIndex p g) :=
  kernelActionReindexSkeleton
    ((PointedVec.skeleton (Additive Γ)).fullSubcategorySkeleton (Supported p g))
    (cosetSimpleIndexEquiv p g)

@[simp] lemma cosetSkeleton_simple_obj (g : G) (a : cosetSimpleIndex p g) :
    ((cosetSkeleton p g).simpleObject a).obj =
      PointedVec.simpleObject (Additive Γ) (Additive.ofMul a.val) := rfl

instance neutralSupport_isAdditive : IsAdditiveFullProperty (neutralSupport.{0} p) :=
  supported_isAdditive p 1

/-- The neutral skeleton has the actual kernel elements as labels and the
actual ambient homogeneous lines as simple representatives. -/
def neutralVectorSkeleton : FiniteSemisimpleSkeleton (NeutralVec.{0} p) p.ker :=
  kernelActionReindexSkeleton (cosetSkeleton p 1) (Equiv.refl p.ker)

@[simp] lemma neutralVectorSkeleton_simple_obj (k : p.ker) :
    ((neutralVectorSkeleton p).simpleObject k).obj =
      PointedVec.simpleObject (Additive Γ) (Additive.ofMul k.val) := rfl

end Paper18.Category.PointedRelativeCenterObstruction
