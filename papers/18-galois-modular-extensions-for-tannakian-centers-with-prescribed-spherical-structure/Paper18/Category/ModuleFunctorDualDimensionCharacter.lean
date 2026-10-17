import Paper18.Category.ModuleFunctorDualDimensionScale
import Paper18.Category.ModuleAlphaInductionEnd

/-! # The derived scaling factor is intrinsic FP dimension

Actual evaluation, actual simple decompositions, and composition identify the
module weight scaling character with the unique positive fusion character.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators MonoidalLeftAction
universe v u vM uM w wM wE
namespace Paper18.Category.ModuleFunctor
open MonoidalLeftAction
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M]
  [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalLeftAction C M]
  [∀ c : C, (actionLeft M c).Additive]
  [∀ c : C, (actionLeft M c).Linear ℂ]
  [∀ X : M, (actionRight C X).Additive]
  {ι : Type w} [Fintype ι] (SC : FiniteSemisimpleSkeleton C ι)
  {κ : Type wM} [Fintype κ] (SM : FiniteSemisimpleSkeleton M κ)
  (r : κ → ℝ) (j₀ : κ)

/-- Actual evaluation of actual strong module endofunctors. -/
def moduleEndEvaluation (m : M) : ModuleAlphaInduction.End C M ⥤ M where
  obj F := F.toFunctor.obj m
  map τ := τ.val.app m

instance moduleEndEvaluation_additive (m : M) : (moduleEndEvaluation (C := C) m).Additive where
  map_add := by intros; rfl

instance moduleEndEvaluation_linear (m : M) : (moduleEndEvaluation (C := C) m).Linear ℂ where
  map_smul _ _ := rfl

variable [HasKernels (ModuleAlphaInduction.End C M)]
  [∀ F G : ModuleAlphaInduction.End C M, FiniteDimensional ℂ (F ⟶ G)]
  [RightRigidCategory (ModuleAlphaInduction.End C M)]
  [Simple (𝟙_ (ModuleAlphaInduction.End C M))]
  {ε : Type wE} [Fintype ε]
  (TE : FiniteSemisimpleSkeleton (ModuleAlphaInduction.End C M) ε)

omit [HasKernels C] [HasFiniteBiproducts C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [HasKernels M] [∀ X : M, (actionRight C X).Additive]
  [RightRigidCategory (ModuleAlphaInduction.End C M)]
  [Simple (𝟙_ (ModuleAlphaInduction.End C M))] in
omit [Preadditive C] [Linear ℂ C] in
/-- Actual evaluation and actual source decompositions compute the scaling
factor additively on actual End-simple multiplicities. -/
lemma moduleFunctorScale_decomposition (F : ModuleAlphaInduction.End C M) :
    moduleFunctorScale SM r j₀ F.toFunctor =
      ∑ e, (TE.multiplicity F e : ℝ) *
        moduleFunctorScale SM r j₀ (TE.simpleObject e).toFunctor := by
  have hh : moduleObjectWeight SM r ((moduleEndEvaluation (SM.simpleObject j₀)).obj F) =
      ∑ e, (TE.multiplicity F e : ℝ) * moduleObjectWeight SM r
        ((moduleEndEvaluation (SM.simpleObject j₀)).obj (TE.simpleObject e)) := by
    simp only [moduleObjectWeight,
      TE.multiplicity_map SM (moduleEndEvaluation (SM.simpleObject j₀)) F,
      Nat.cast_sum, Nat.cast_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  unfold moduleFunctorScale
  change moduleObjectWeight SM r ((moduleEndEvaluation (SM.simpleObject j₀)).obj F) / r j₀ = _
  rw [hh, Finset.sum_div]
  simp only [mul_div_assoc]
  rfl

variable
  (hconn : ∀ j k : κ, ∃ X : C, Nonempty (Retract (SM.simpleObject k) (X ⊙ₗ SM.simpleObject j)))
  (d : ι → ℝ) (hr : ∀ j, 0 < r j)
  (hR : ∀ a j, ∑ k, (moduleActionCoeff SC SM a j k : ℝ) * r k = d a * r j)

/-- A genuine positive normalized character, with every law derived from
actual module functors and their actual decompositions. -/
def moduleFunctorScalingCharacter : FusionBasis.PositiveDimension TE.fusionBasis where
  dim e := moduleFunctorScale SM r j₀ (TE.simpleObject e).toFunctor
  pos e := moduleFunctorScale_pos SM r j₀ SC hconn d hr hR _ (by
    intro h
    apply CategoryTheory.id_nonzero (TE.simpleObject e)
    exact Subtype.ext h)
  unit := by
    change moduleFunctorScale SM r j₀ (TE.simpleObject TE.unitLabel).toFunctor = 1
    erw [moduleFunctorScale_iso SM r j₀ ((forget (C := C)).mapIso TE.unitIso)]
    exact moduleFunctorScale_id SM r j₀ (hr j₀)
  tensor e f := by
    change (∑ k, (TE.multiplicity (TE.simpleObject e ⊗ TE.simpleObject f) k : ℝ) *
      moduleFunctorScale SM r j₀ (TE.simpleObject k).toFunctor) = _
    rw [← moduleFunctorScale_decomposition SM r j₀ TE]
    exact moduleFunctorScale_comp SM r j₀ SC hconn d hr hR
      (TE.simpleObject e).toFunctor (TE.simpleObject f).toFunctor

include hconn hr hR in
/-- The derived actual scaling factor equals the intrinsic actual End FP dimension. -/
theorem moduleFunctorScale_eq_fpdim (F : ModuleAlphaInduction.End C M) :
    moduleFunctorScale SM r j₀ F.toFunctor = TE.fpdim F := by
  rw [moduleFunctorScale_decomposition SM r j₀ TE]
  change (∑ e, (TE.multiplicity F e : ℝ) *
    (moduleFunctorScalingCharacter SC SM r j₀ TE hconn d hr hR).dim e) = _
  simp only [FusionBasis.PositiveDimension.eq_fpdim]
  rfl

include j₀ hconn hr hR in
/-- The actual End FP dimension is the actual object-weight multiplier. -/
theorem moduleFunctor_fpdim_scales_weight (F : ModuleAlphaInduction.End C M) (X : M) :
    moduleObjectWeight SM r (F.toFunctor.obj X) = TE.fpdim F * moduleObjectWeight SM r X := by
  rw [moduleFunctorScale_spec SM r j₀ SC hconn d hr hR F.toFunctor,
    moduleFunctorScale_eq_fpdim SC SM r j₀ TE hconn d hr hR]

end Paper18.Category.ModuleFunctor
