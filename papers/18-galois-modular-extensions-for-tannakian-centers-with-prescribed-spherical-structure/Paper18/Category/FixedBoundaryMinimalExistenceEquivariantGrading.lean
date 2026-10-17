import Paper18.Category.FixedBoundaryMinimalExistenceGrading
import Paper18.Category.EquivariantFPdim

/-! # The actual C₂ grading lifts to actual equivariant objects -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open Paper18.Category.CrossedBraidedGauging
universe v u t
namespace Paper18.Category.FixedBoundary.MinimalExistence
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasKernels C] [HasFiniteBiproducts C]
  {P : Grading C2 C} {A : WeakAction C2 C}
  [∀ g : C2, (A.ρ g).Monoidal] [A.IsMonoidal]
  [∀ g : C2, (A.ρ g).Additive] [∀ g : C2, (A.ρ g).Linear ℂ]
  (Q : GradedAction P A)

def equivariantDegreeEnd (g : C2) (E : A.Equivariant) : E ⟶ E where
  hom := (P.projection g).app E.obj
  comm a := by
    rw [Q.map_projection]
    have hg : a * g * a⁻¹ = g := by simp [mul_assoc, mul_comm a g]
    rw [hg]
    exact (P.projection_naturality g (E.structureIso a).hom).symm

def equivariantDegreeProjection (g : C2) : 𝟭 A.Equivariant ⟶ 𝟭 A.Equivariant where
  app := equivariantDegreeEnd Q g
  naturality {E F} f := by
    apply WeakAction.Equivariant.Hom.ext
    exact P.projection_naturality g f.hom

/-- Abelian conjugation fixes every actual degree, so its actual
projectors are equivariant and give a genuine grading after gauging. -/
def equivariantGrading : Grading C2 A.Equivariant where
  projection := equivariantDegreeProjection Q
  orthogonal g h E := by
    apply WeakAction.Equivariant.Hom.ext
    by_cases hgh : g = h
    · subst h
      simpa only [if_pos rfl] using P.projection_idempotent g E.obj
    · simpa only [if_neg hgh] using P.projection_comp_of_ne hgh E.obj
  total E := by
    apply A.forget.map_injective
    rw [A.forget.map_sum]
    change ∑ g : C2, (P.projection g).app E.obj = 𝟙 E.obj
    exact P.total E.obj
  unit g := by
    apply WeakAction.Equivariant.Hom.ext
    by_cases hg : g = 1
    · subst g
      simpa only [if_pos rfl] using P.homogeneous_unit
    · simpa only [if_neg hg] using P.projection_eq_zero_of_homogeneous hg P.homogeneous_unit
  tensor k E F := by
    apply A.forget.map_injective
    simp only [Functor.map_sum, apply_ite, Functor.map_zero]
    change (P.projection k).app (E.obj ⊗ F.obj) = _
    rw [P.tensor]
    apply Finset.sum_congr rfl
    intro g _
    apply Finset.sum_congr rfl
    intro h _
    by_cases hgh : g * h = k
    · simp only [if_pos hgh]
      rfl
    · simp only [if_neg hgh]

@[simp] theorem equivariantGrading_homogeneous (g : C2) (E : A.Equivariant) :
    (equivariantGrading Q).Homogeneous g E ↔ P.Homogeneous g E.obj := by
  constructor
  · intro h
    exact congrArg WeakAction.Equivariant.Hom.hom h
  · intro h
    exact WeakAction.Equivariant.Hom.ext h

/-- Genuine induction of an actual nonzero degree-g object is an actual
nonzero equivariant object of the same degree. -/
theorem equivariantGrading_faithful (hf : P.Faithful) : (equivariantGrading Q).Faithful := by
  intro g
  obtain ⟨X, hX, hnX⟩ := hf g
  refine ⟨A.induction X, (equivariantGrading_homogeneous Q g _).mpr ?_, ?_⟩
  · change P.Homogeneous g (⨁ fun a : C2 => (A.ρ a).obj X)
    apply P.homogeneous_biproduct
    intro a
    simpa only [mul_assoc, mul_comm a g, mul_inv_cancel, mul_one] using Q.homogeneous_map a hX
  · intro hz
    have h := congrArg WeakAction.Equivariant.Hom.hom ((IsZero.iff_id_eq_zero _).mp hz)
    change 𝟙 (A.induction X).obj = 0 at h
    let r := A.inductionRetract X
    have hh := congrArg (fun q => r.i ≫ q ≫ r.r) h
    have hx : 𝟙 X = 0 := by
      dsimp only at hh
      erw [Category.id_comp, r.retract] at hh
      simpa only [comp_zero, zero_comp] using hh
    exact hnX ((IsZero.iff_id_eq_zero X).mpr hx)

end Paper18.Category.FixedBoundary.MinimalExistence
