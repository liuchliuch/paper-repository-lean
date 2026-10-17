import Paper18.Category.RigidMultiplicity
import Paper18.Fusion.Rules
import Paper18.Fusion.TensorFunctor

/-!
# FP dimensions and integrality for actual fusion categories

The category has actual complex-linear Hom spaces, additive tensor product,
rigid duals, a simple unit, and a finite semisimple skeleton with actual
biproduct decompositions. Fusion rules and their positive FP dimension
character are derived, rather than supplied as a numerical model.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u w v' u' w'
namespace Paper18.Category
namespace FiniteSemisimpleSkeleton

attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- The fusion rules of actual simple objects, with all laws derived from
categorical unitors, associators and the two rigid Hom adjunctions. -/
def fusionRules : Paper18.FusionRules ι where
  one := S.unitLabel
  dual := S.dualLabel
  N := S.fusionCoeff
  dual_involutive := S.dualLabel_involutive
  dual_one := S.dualLabel_unit
  N_one_left := S.fusionCoeff_one_left S.unitLabel S.unitIso
  N_one_right := S.fusionCoeff_one_right S.unitLabel S.unitIso
  N_dual := S.fusionCoeff_dual
  N_right := S.fusionCoeff_right
  N_assoc := S.fusionCoeff_assoc

/-- The canonical FP dimension character, constructed from actual fusion
coefficients by the proved positive-matrix existence theorem. -/
def fusionBasis : Paper18.FusionBasis ι := S.fusionRules.toFusionBasis

@[simp] lemma fusionBasis_one : S.fusionBasis.one = S.unitLabel := rfl
@[simp] lemma fusionBasis_dual (i : ι) : S.fusionBasis.dual i = S.dualLabel i := rfl
@[simp] lemma fusionBasis_N (i j k : ι) : S.fusionBasis.N i j k = S.fusionCoeff i j k := rfl

/-- FP dimension of an actual object, extended additively from actual simple
multiplicities. -/
def fpdim (X : C) : ℝ := ∑ i, (S.multiplicity X i : ℝ) * S.fusionBasis.fpdim i

lemma fpdim_iso {X Y : C} (e : X ≅ Y) : S.fpdim X = S.fpdim Y := by
  simp only [fpdim, S.multiplicity_iso e]

@[simp] lemma fpdim_simple (i : ι) : S.fpdim (S.simpleObject i) = S.fusionBasis.fpdim i := by
  simp [fpdim, S.multiplicity_simple]

@[simp] lemma fpdim_unit : S.fpdim (𝟙_ C) = 1 := by
  rw [← S.fpdim_iso S.unitIso, S.fpdim_simple]
  exact S.fusionBasis.fpdim_one

lemma fpdim_nonneg (X : C) : 0 ≤ S.fpdim X :=
  Finset.sum_nonneg (fun i _ =>
    mul_nonneg (Nat.cast_nonneg _) (S.fusionBasis.fpdim_pos i).le)

/-- FP dimension detects precisely the actual zero objects. -/
lemma fpdim_eq_zero_iff (X : C) : S.fpdim X = 0 ↔ IsZero X := by
  constructor
  · intro h
    have hm (i : ι) : S.multiplicity X i = 0 := by
      by_contra hn
      have hp : 0 < (S.multiplicity X i : ℝ) * S.fusionBasis.fpdim i :=
        mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) (S.fusionBasis.fpdim_pos i)
      have hb := Finset.single_le_sum
        (s := Finset.univ)
        (f := fun j => (S.multiplicity X j : ℝ) * S.fusionBasis.fpdim j)
        (fun j _ => mul_nonneg (Nat.cast_nonneg _) (S.fusionBasis.fpdim_pos j).le)
        (Finset.mem_univ i)
      change _ ≤ S.fpdim X at hb
      rw [h] at hb
      linarith
    apply (IsZero.iff_id_eq_zero X).mpr
    by_contra hn
    have hp : 0 < Module.finrank ℂ (X ⟶ X) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨𝟙 X, hn⟩
    rw [S.finrank_hom_eq_sum X X] at hp
    simp [hm] at hp
  · intro h
    have hm (i : ι) : S.multiplicity X i = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hp
      let r := S.retractOfMultiplicityPos X i hp
      apply CategoryTheory.id_nonzero (S.simpleObject i)
      rw [← r.retract, h.eq_zero_of_tgt r.i, zero_comp]
    simp [fpdim, hm]

lemma fpdim_pos_of_not_isZero (X : C) (h : ¬ IsZero X) : 0 < S.fpdim X :=
  lt_of_le_of_ne (S.fpdim_nonneg X) (Ne.symm (fun hz => h ((S.fpdim_eq_zero_iff X).mp hz)))

/-- Additivity of FP dimension is induced by actual biproducts. -/
lemma fpdim_biproduct {J : Type*} [Fintype J] (f : J → C) :
    S.fpdim (⨁ f) = ∑ j, S.fpdim (f j) := by
  simp only [fpdim, S.multiplicity_biproduct, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Multiplicativity of FP dimension for actual tensor products. -/
lemma fpdim_tensor (X Y : C) : S.fpdim (X ⊗ Y) = S.fpdim X * S.fpdim Y := by
  calc
    _ = ∑ k, (∑ i, ∑ j, (S.multiplicity X i : ℝ) * (S.multiplicity Y j : ℝ) *
        (S.fusionCoeff i j k : ℝ)) * S.fusionBasis.fpdim k := by
      unfold fpdim
      apply Finset.sum_congr rfl
      intro k _
      rw [S.multiplicity_tensor X Y k]
      simp only [Nat.cast_sum, Nat.cast_mul]
    _ = ∑ i, ∑ j, (S.multiplicity X i : ℝ) * (S.multiplicity Y j : ℝ) *
        (∑ k, (S.fusionCoeff i j k : ℝ) * S.fusionBasis.fpdim k) := by
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, (S.multiplicity X i : ℝ) * (S.multiplicity Y j : ℝ) *
        (S.fusionBasis.fpdim i * S.fusionBasis.fpdim j) := by
      simp_rw [← S.fusionBasis_N, S.fusionBasis.fpdim_mul]
    _ = _ := by
      unfold fpdim
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Original integrality predicate, quantified over actual categorical simple
objects rather than over an arbitrary list of numerical labels. -/
def Integral : Prop := ∀ X : C, Simple X → ∃ n : ℤ, S.fpdim X = n

/-- The finite presentation is complete, so the simple-object definition of
integrality agrees with integral FP dimensions of the categorical fusion basis. -/
theorem integral_iff_basis : S.Integral ↔ S.fusionBasis.Integral := by
  constructor
  · intro h i
    simpa using h (S.simpleObject i) (S.simple i)
  · intro h X hX
    letI := hX
    obtain ⟨i, ⟨e⟩⟩ := S.simple_isomorphic_representative X
    obtain ⟨n, hn⟩ := h i
    refine ⟨n, ?_⟩
    rw [S.fpdim_iso e, S.fpdim_simple, hn]

/-- Every object of an integral actual fusion category has integer FP dimension. -/
theorem fpdim_integer (h : S.Integral) (X : C) : ∃ n : ℤ, S.fpdim X = n := by
  choose n hn using S.integral_iff_basis.mp h
  refine ⟨∑ i, (S.multiplicity X i : ℤ) * n i, ?_⟩
  simp [fpdim, hn]

section Functor
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  (F : C ⥤ D) [F.Additive] [F.Monoidal]

/-- An actual additive strong monoidal functor induces a unital fusion-rule
map; no dimension preservation or tensor multiplicity equation is assumed. -/
def fusionRuleMap : Paper18.FusionRuleMap S.fusionBasis T.fusionBasis where
  imageCoeff := S.imageCoeff T F
  image_one := by
    constructor
    · simpa using S.imageCoeff_one T F S.unitLabel T.unitLabel S.unitIso T.unitIso T.unitLabel
    · intro j hj
      change j ≠ T.unitLabel at hj
      simpa [hj] using S.imageCoeff_one T F S.unitLabel T.unitLabel S.unitIso T.unitIso j
  tensor_coeff := S.imageCoeff_tensor T F

/-- Dimension preservation by actual tensor functors, first on simples. -/
theorem fpdim_map_simple (i : ι) :
    T.fpdim (F.obj (S.simpleObject i)) = S.fpdim (S.simpleObject i) := by
  rw [S.fpdim_simple]
  exact (S.fusionRuleMap T F).fpdim_preserved i

/-- FP dimension preservation for every actual object. -/
theorem fpdim_map (X : C) : T.fpdim (F.obj X) = S.fpdim X := by
  have hd (i : ι) : (∑ j, (S.imageCoeff T F i j : ℝ) * T.fusionBasis.fpdim j) =
      S.fusionBasis.fpdim i := (S.fusionRuleMap T F).fpdim_preserved i
  calc
    _ = ∑ j, (∑ i, (S.multiplicity X i : ℝ) * (S.imageCoeff T F i j : ℝ)) *
        T.fusionBasis.fpdim j := by
      unfold fpdim
      apply Finset.sum_congr rfl; intro j _
      rw [S.multiplicity_map T F X j]
      simp only [Nat.cast_sum, Nat.cast_mul, imageCoeff]
    _ = ∑ i, (S.multiplicity X i : ℝ) *
        (∑ j, (S.imageCoeff T F i j : ℝ) * T.fusionBasis.fpdim j) := by
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [hd]
      rfl

/-- A dominant actual functor gives the dominant numerical map required by
the independently proved integrality theorem. -/
def fusionMap
    (hF : ∀ Y : D, ∃ X : C, Nonempty (Retract Y (F.obj X))) :
    Paper18.FusionMap S.fusionBasis T.fusionBasis where
  toFusionRuleMap := S.fusionRuleMap T F
  dominant := S.imageCoeff_dominant_of_retracts T F hF

/-- The paper's definition of dominance, expressed using actual simple
objects and their occurrences as direct summands. -/
def Dominant : Prop :=
  ∀ Y : D, Simple Y → ∃ X : C, Nonempty (Retract Y (F.obj X))

include S T in
/-- In finite semisimple categories, checking dominance on simples is
equivalent to every object being a retract of an image. -/
theorem dominant_iff_retracts : Dominant F ↔
    ∀ Y : D, ∃ X : C, Nonempty (Retract Y (F.obj X)) := by
  constructor
  · intro h
    apply (S.imageCoeff_dominant_iff_retracts T F).mp
    intro j
    obtain ⟨X, ⟨r⟩⟩ := h (T.simpleObject j) (T.simple j)
    have hp := (T.multiplicity_pos_iff_retract (F.obj X) j).mpr ⟨r⟩
    rw [S.multiplicity_map T F] at hp
    obtain ⟨i, _, hi⟩ := Finset.sum_pos_iff.mp hp
    exact ⟨i, pos_of_mul_pos_right hi (Nat.zero_le _)⟩
  · intro h Y _
    exact h Y

end Functor

/-- FP dimension is independent of the chosen complete family of simple
representatives and biproduct decompositions. -/
theorem fpdim_independent {κ : Type w'} [Fintype κ]
    (T : FiniteSemisimpleSkeleton C κ) (X : C) : S.fpdim X = T.fpdim X := by
  simpa using (T.fpdim_map S (𝟭 C) X)

/-- Consequently integrality is a property of the actual category. -/
theorem integral_independent {κ : Type w'} [Fintype κ]
    (T : FiniteSemisimpleSkeleton C κ) : S.Integral ↔ T.Integral := by
  simp only [Integral, S.fpdim_independent T]
end FiniteSemisimpleSkeleton
end Paper18.Category
