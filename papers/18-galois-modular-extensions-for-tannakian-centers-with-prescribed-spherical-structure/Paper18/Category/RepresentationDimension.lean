import Paper18.Category.RepresentationSkeleton
import Paper18.Category.FusionCategory

/-!
# FP dimensions of actual finite group representations

Ordinary vector-space dimension is positive on simple representations and
is additive and multiplicative for the actual categorical operations. The
proved positive-character uniqueness theorem identifies it with FP dimension.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace Paper18.Category.Representation
variable {G : Type} [Group G] [Fintype G]

/-- The ordinary vector-space dimension of an actual representation. -/
def dimension (V : FDRep ℂ G) : ℕ := Module.finrank ℂ V

omit [Fintype G] in
lemma dimension_iso {V W : FDRep ℂ G} (e : V ≅ W) : dimension V = dimension W :=
  (FDRep.isoToLinearEquiv e).finrank_eq

omit [Fintype G] in
@[simp] lemma dimension_unit : dimension (𝟙_ (FDRep ℂ G)) = 1 := Module.finrank_self ℂ

omit [Fintype G] in
lemma dimension_tensor (V W : FDRep ℂ G) :
    dimension (V ⊗ W) = dimension V * dimension W := Module.finrank_tensorProduct

omit [Fintype G] in
/-- Vector-space dimension is additive on actual categorical biproducts. -/
lemma dimension_biproduct {J : Type} [Fintype J] (V : J → FDRep ℂ G) :
    dimension (⨁ V) = ∑ j, dimension (V j) := by
  let F : FDRep ℂ G ⥤ ModuleCat ℂ :=
    forget₂ (FDRep ℂ G) (FGModuleCat ℂ) ⋙ forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)
  have h := ((F.mapBiproduct V) ≪≫ ModuleCat.biproductIsoPi (F.obj ∘ V)).toLinearEquiv.finrank_eq
  change Module.finrank ℂ (⨁ V : FDRep ℂ G) = Module.finrank ℂ (∀ j, V j) at h
  simpa only [dimension, Module.finrank_pi_fintype] using h

omit [Fintype G] in
lemma dimension_pos (V : FDRep ℂ G) [Simple V] : 0 < dimension V := by
  obtain ⟨v, hv⟩ := exists_nonzero_vector V
  letI := nontrivial_of_ne v 0 hv
  have h : 0 < Module.finrank ℂ (_root_.Representation.asModule V.ρ) := Module.finrank_pos
  simpa only [(_root_.Representation.asModuleEquiv V.ρ).finrank_eq] using h

variable {ι : Type} [Fintype ι] (S : FiniteSemisimpleSkeleton (FDRep ℂ G) ι)

omit [Fintype G] in
/-- The actual simple-object decomposition recovers ordinary vector-space
dimension with the derived categorical Hom multiplicities. -/
lemma dimension_eq_sum (V : FDRep ℂ G) :
    dimension V = ∑ i, S.multiplicity V i * dimension (S.simpleObject i) := by
  rw [S.sum_multiplicity]
  rw [dimension_iso (S.decomposition V), dimension_biproduct]

/-- Ordinary positive dimension is a normalized positive character of the
fusion rules derived from actual representation tensors. -/
def vectorDimensionCharacter : Paper18.FusionBasis.PositiveDimension S.fusionBasis where
  dim i := dimension (S.simpleObject i)
  pos i := by exact_mod_cast dimension_pos (S.simpleObject i)
  unit := by
    change (dimension (S.simpleObject S.unitLabel) : ℝ) = 1
    rw [dimension_iso S.unitIso, dimension_unit]
    norm_num
  tensor i j := by
    have h := dimension_eq_sum S (S.simpleObject i ⊗ S.simpleObject j)
    rw [dimension_tensor] at h
    change ∑ k, (S.multiplicity (S.simpleObject i ⊗ S.simpleObject j) k : ℝ) *
      (dimension (S.simpleObject k) : ℝ) =
      (dimension (S.simpleObject i) : ℝ) * (dimension (S.simpleObject j) : ℝ)
    exact_mod_cast h.symm

omit [Fintype G] in
/-- The actual Frobenius–Perron dimension of a finite representation is its
ordinary vector-space dimension. -/
theorem fpdim_eq_dimension (V : FDRep ℂ G) : S.fpdim V = (dimension V : ℝ) := by
  have h : ∀ i, S.fusionBasis.fpdim i = (dimension (S.simpleObject i) : ℝ) :=
    fun i => ((vectorDimensionCharacter S).eq_fpdim i).symm
  unfold FiniteSemisimpleSkeleton.fpdim
  simp_rw [h]
  exact_mod_cast (dimension_eq_sum S V).symm

omit [Fintype G] in
/-- The actual fusion category of finite-dimensional complex representations
of a finite group is integral. -/
theorem integral : S.Integral := by
  intro V _
  exact ⟨(dimension V : ℤ), by simpa using fpdim_eq_dimension S V⟩

/-- Integrality for the actual canonical finite representation skeleton,
whose existence was proved by Maschke's theorem and the regular module. -/
theorem skeleton_integral : (skeleton G).Integral := integral (skeleton G)

end Paper18.Category.Representation
