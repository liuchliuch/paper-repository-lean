import Paper18.Category.SphericalizationCentralizerDimensionBasic
import Paper18.Category.SphericalizationCentralizerIntegral
import Paper18.Category.SphericalizationFPdim

/-! # Actual dimension doubling for lifted centralizers under sphericalization

The original category is not given a pivotal structure. The canonical
double-dual action preserves every actual full fusion centralizer by its
proved dual closure. Actual induction proves dominance and the unit index;
the actual induction multiplicity identity computes the support dimension.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w v' u' w'
namespace Paper18.Category.Sphericalized
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

include S in
lemma action_property (P : ObjectProperty C) [IsAdditiveFullProperty P] [P.IsMonoidal]
    (g : SphericalizationGroup) (X : C) (hX : P X) :
    P (((sphericalizationAction C).ρ g).obj X) := by
  by_cases hg : g = 1
  · simpa [sphericalizationAction, sphericalizationRho, hg] using hX
  · change P ((sphericalizationRho C g).obj X)
    rw [sphericalizationRho, if_neg hg]
    change P ((Xᘁ)ᘁ)
    exact S.property_rightDual P (S.property_rightDual P hX)

/-- Every actual full fusion support doubles under the actual canonical
sphericalization preimage, without an ambient pivotal structure. -/
theorem supportFPdim_preimage_eq_twice (P : ObjectProperty C)
    [IsAdditiveFullProperty P] [P.IsMonoidal] :
    (skeleton S).supportFPdim (fun X => P (forget.obj X)) = 2 * S.supportFPdim P := by
  calc
    _ = ((sphericalizationAction C).equivariantSkeleton S).supportFPdim (fun X => P X.obj) := by
      unfold FiniteSemisimpleSkeleton.supportFPdim
      apply Finset.sum_congr rfl
      intro q _
      change (if P (((sphericalizationAction C).equivariantSkeleton S).simpleObject q).obj
        then (skeleton S).fusionBasis.fpdim q ^ 2 else 0) = _
      rw [simple_fpdim_equivariant S]
    _ = (Fintype.card SphericalizationGroup : ℝ) * S.supportFPdim P :=
      (sphericalizationAction C).equivariant_supportFPdim S P (action_property S P)
    _ = _ := by norm_num [SphericalizationGroup]

/-- The actual square object obtained from canonical finite induction. -/
def inductionObject (X : C) : Sphericalized C :=
  WeakAction.Equivariant.toSphericalized.obj ((sphericalizationAction C).induction X)

/-- The actual identity summand gives a retract of the underlying induction. -/
def inductionObjectRetract (X : C) : Retract X (forget.obj (inductionObject X)) :=
  (sphericalizationAction C).inductionRetract X

/-- The actual induction Hom equivalence, transported through the proved
actual square/equivariant equivalence. -/
def inductionObjectHomEquiv (X : C) (Y : Sphericalized C) :
    (inductionObject X ⟶ Y) ≃ₗ[ℂ] (X ⟶ forget.obj Y) := by
  let A := sphericalizationAction C
  let H := WeakAction.Equivariant.toSphericalized (C := C)
  let Z := toEquivariant.obj Y
  let e : Y ≅ H.obj Z := (equivariantEquivalence (C := C)).unitIso.app Y
  let h : (A.induction X ⟶ Z) ≃ₗ[ℂ] (H.obj (A.induction X) ⟶ H.obj Z) :=
    LinearEquiv.ofBijective (H.mapLinearMap ℂ) ⟨H.map_injective, H.map_surjective⟩
  exact (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) e) ≪≫ₗ h.symm ≪≫ₗ
    A.inductionHomLinearEquiv X Z

lemma inductionObject_fpdim (X : C) :
    (skeleton S).fpdim (inductionObject X) = 2 * S.fpdim X := by
  rw [← (skeleton S).fpdim_map S forget]
  change S.fpdim (⨁ fun g : SphericalizationGroup =>
    ((sphericalizationAction C).ρ g).obj X) = _
  rw [S.fpdim_biproduct]
  simp_rw [S.fpdim_map S]
  norm_num [SphericalizationGroup]

lemma inductionObject_unit_fpdim : (skeleton S).fpdim (inductionObject (𝟙_ C)) = 2 := by
  rw [inductionObject_fpdim S, S.fpdim_unit]
  norm_num

variable {B : Type u'} [Category.{v'} B]
  (F : B ⥤ C) (Fhat : B ⥤ Sphericalized C) (e : Fhat ⋙ forget ≅ F)

include S e in
lemma centralizerInduction_property (X : C) (hX : X ∈ centralizer (Set.range F.obj)) :
    inductionObject X ∈ centralizer (Set.range Fhat.obj) := by
  apply (centralizer_forget_iso_iff F Fhat e _).mpr
  exact (sphericalizationAction C).induction_property
    (centralizerProperty (Set.range F.obj)) (action_property S _) X hX

/-- The actual forgetful tensor functor restricted to the two actual centralizers. -/
def centralizerForget : CentralizerCategory (Set.range Fhat.obj) ⥤
    CentralizerCategory (Set.range F.obj) :=
  fullSubcategoryFunctor (centralizerProperty (Set.range Fhat.obj))
    (centralizerProperty (Set.range F.obj)) forget
    (fun X hX => (centralizer_forget_iso_iff F Fhat e X).mp hX)

instance centralizerForget_additive : (centralizerForget F Fhat e).Additive := by
  dsimp [centralizerForget]; infer_instance
instance centralizerForget_linear : (centralizerForget F Fhat e).Linear ℂ := by
  dsimp [centralizerForget]; infer_instance
instance centralizerForget_monoidal : (centralizerForget F Fhat e).Monoidal := by
  dsimp [centralizerForget]; infer_instance
instance centralizerForget_faithful : (centralizerForget F Fhat e).Faithful where
  map_injective {_X _Y} _f _g h := (forget (C := C)).map_injective h
instance centralizerForget_braided : (centralizerForget F Fhat e).Braided where
  braided X Y := Functor.LaxBraided.braided (F := forget (C := C)) X.obj Y.obj

/-- Actual induction restricted to the centralizer, at the level of objects. -/
def centralizerInductionObject (X : CentralizerCategory (Set.range F.obj)) :
    CentralizerCategory (Set.range Fhat.obj) :=
  ⟨inductionObject X.obj, centralizerInduction_property S F Fhat e X.obj X.property⟩

/-- The actual induction universal Hom equivalence inside the two full
centralizer categories. -/
def centralizerInductionHomEquiv (X : CentralizerCategory (Set.range F.obj))
    (Y : CentralizerCategory (Set.range Fhat.obj)) :
    (centralizerInductionObject S F Fhat e X ⟶ Y) ≃ₗ[ℂ]
      (X ⟶ (centralizerForget F Fhat e).obj Y) :=
  inductionObjectHomEquiv X.obj Y.obj

include S in
/-- The restricted actual forgetful functor is retract-dominant: actual
induction stays in the appropriate centralizer by double-dual closure. -/
theorem centralizerForget_retract_dominant
    (X : CentralizerCategory (Set.range F.obj)) :
    ∃ Y : CentralizerCategory (Set.range Fhat.obj),
      Nonempty (Retract X ((centralizerForget F Fhat e).obj Y)) := by
  let r := inductionObjectRetract X.obj
  exact ⟨centralizerInductionObject S F Fhat e X, ⟨⟨r.i, r.r, r.retract⟩⟩⟩

/-- The actual induction of the centralizer tensor unit. -/
def centralizerInducedUnit : CentralizerCategory (Set.range Fhat.obj) :=
  ⟨inductionObject (𝟙_ C), centralizerInduction_property S F Fhat e _
    (fun Y _ => centralizes_unit_left Y)⟩

/-- The actual unit index is two, computed intrinsically in the actual
lifted centralizer from its actual induced unit. -/
theorem centralizer_unit_index :
    (skeleton S).fullSubcategoryFPdim (centralizerProperty (Set.range Fhat.obj))
      (centralizerInducedUnit S F Fhat e) = 2 := by
  rw [FiniteSemisimpleSkeleton.fullSubcategoryFPdim_eq]
  exact inductionObject_unit_fpdim S

include e in
/-- Actual centralizer dimension doubles under canonical sphericalization,
without imposing any pivotal structure on the original category. -/
theorem centralizerFPdim_eq_twice :
    (skeleton S).centralizerFPdim (Set.range Fhat.obj) =
      2 * S.centralizerFPdim (Set.range F.obj) := by
  have he : centralizerProperty (Set.range Fhat.obj) =
      (fun X : Sphericalized C => forget.obj X ∈ centralizer (Set.range F.obj)) := by
    funext X
    exact propext (centralizer_forget_iso_iff F Fhat e X)
  change (skeleton S).supportFPdim (centralizerProperty (Set.range Fhat.obj)) = _
  rw [he]
  exact supportFPdim_preimage_eq_twice S (centralizerProperty (Set.range F.obj))

end Paper18.Category.Sphericalized
