import Paper18.Category.TannakianDescentFullyFaithful
import Paper18.Category.RepresentationFunctionTorsor
import Paper18.Category.EquivariantAveraging

/-! # Actual regular-algebra torsor identities for descent -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators MonObj Obj
universe v u v' u'
namespace Paper18.Category
namespace SeparableAlgebra
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  {A : C} [MonObj A] (S : SeparableAlgebra A) (F : C ⥤ D) [F.Monoidal]

theorem map_element : (S.map F).element =
    Functor.LaxMonoidal.ε F ≫ F.map S.element ≫ Functor.OplaxMonoidal.δ F A A := by
  change (Functor.LaxMonoidal.ε F ≫ F.map η[A]) ≫
      (F.map S.section_ ≫ Functor.OplaxMonoidal.δ F A A) = _
  simp only [SeparableAlgebra.element, F.map_comp, Category.assoc]

theorem map_element_translation (t : A ⟶ A) :
    (S.map F).element ≫ (F.obj A ◁ F.map t) ≫ μ[F.obj A] =
      Functor.LaxMonoidal.ε F ≫ F.map (S.element ≫ (A ◁ t) ≫ μ[A]) := by
  rw [S.map_element]
  simp only [Category.assoc]
  change Functor.LaxMonoidal.ε F ≫ F.map S.element ≫
      Functor.OplaxMonoidal.δ F A A ≫ (F.obj A ◁ F.map t) ≫
        Functor.LaxMonoidal.μ F A A ≫ F.map μ[A] = _
  rw [Functor.LaxMonoidal.μ_natural_right_assoc, Functor.Monoidal.δ_μ_assoc]
  simp only [F.map_comp]

end SeparableAlgebra

namespace SeparableAlgebra
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A : C} [MonObj A] (S : SeparableAlgebra A) (M : Mod_ C A)

/-- Separability averages a semilinear endomorphism by the twisted product
of its actual separability element. -/
theorem moduleSection_semilinear (t : A ⟶ A) (u : M.X ⟶ M.X)
    (hu : γ[A,M.X] ≫ u = (t ▷ M.X) ≫ (A ◁ u) ≫ γ[A,M.X]) :
    S.moduleSection M ≫ (A ◁ u) ≫ γ[A,M.X] =
      (λ_ M.X).inv ≫ ((S.element ≫ (A ◁ t) ≫ μ[A]) ▷ M.X) ≫
        (A ◁ u) ≫ γ[A,M.X] := by
  unfold moduleSection
  calc
    _ = (λ_ M.X).inv ≫ ((S.element ≫ (A ◁ t)) ▷ M.X) ≫
        ((A ⊗ A) ◁ u) ≫ (α_ A A M.X).hom ≫
          (A ◁ γ[A,M.X]) ≫ γ[A,M.X] := by
      simp only [Category.assoc]
      rw [← whiskerLeft_comp_assoc, hu]
      monoidal
    _ = (λ_ M.X).inv ≫ ((S.element ≫ (A ◁ t)) ▷ M.X) ≫
        ((A ⊗ A) ◁ u) ≫ (μ[A] ▷ M.X) ≫ γ[A,M.X] := by
      rw [← InternalModule.mul_smul]
    _ = _ := by
      rw [whisker_exchange_assoc]
      simp only [comp_whiskerRight, Category.assoc]

end SeparableAlgebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {G : Type} [Group G] [Fintype G] (T : TannakianCenter C G)

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- The transported separability element retains the actual finite-group
torsor orthogonality relation. -/
theorem TannakianCenter.regular_element_translation (g : G) :
    T.regularAlgebraSeparable.element ≫ (T.regularAlgebra ◁ T.regularTranslation g) ≫
        μ[T.regularAlgebra] = if g = 1 then η[T.regularAlgebra] else 0 := by
  change (Representation.functionsSeparable.map T.inclusion).element ≫
    (T.inclusion.obj Representation.functions ◁ T.inclusion.map (Representation.rightTranslation g)) ≫
      μ[T.inclusion.obj Representation.functions] = _
  rw [SeparableAlgebra.map_element_translation, Representation.functions_element_translation]
  by_cases hg : g = 1
  · simp only [if_pos hg]
    rfl
  · simp only [if_neg hg, Functor.map_zero, comp_zero]

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- An actual equivariant structure is semilinear for the actual regular
right translation, as a consequence of its module morphism law. -/
theorem TannakianCenter.equivariantStructure_semilinear
    (M : T.deequivariantAction.Equivariant) (g : G) :
    γ[T.regularAlgebra,M.obj.X] ≫ (M.structureIso g).hom.hom =
      (T.regularTranslation g ▷ M.obj.X) ≫
        (T.regularAlgebra ◁ (M.structureIso g).hom.hom) ≫ γ[T.regularAlgebra,M.obj.X] := by
  have h := (M.structureIso g).hom.isMod_Hom.smul_hom
  change ((T.regularTranslation g⁻¹ ▷ M.obj.X) ≫ γ[T.regularAlgebra,M.obj.X]) ≫
      (M.structureIso g).hom.hom =
    (T.regularAlgebra ◁ (M.structureIso g).hom.hom) ≫ γ[T.regularAlgebra,M.obj.X] at h
  let e := T.regularTranslationIso g
  change ((e.inv ▷ M.obj.X) ≫ γ[T.regularAlgebra,M.obj.X]) ≫
      (M.structureIso g).hom.hom = _ at h
  have hh := congrArg (fun k => (e.hom ▷ M.obj.X) ≫ k) h
  simpa only [Category.assoc, hom_inv_whiskerRight_assoc] using hh

omit [MonoidalLinear ℂ C] in
/-- The regular separable section is orthogonal to every nontrivial
equivariant structure map. -/
theorem TannakianCenter.moduleSection_structure
    (M : T.deequivariantAction.Equivariant) (g : G) :
    T.regularAlgebraSeparable.moduleSection M.obj ≫
        (T.regularAlgebra ◁ (M.structureIso g).hom.hom) ≫ γ[T.regularAlgebra,M.obj.X] =
      if g = 1 then 𝟙 M.obj.X else 0 := by
  rw [T.regularAlgebraSeparable.moduleSection_semilinear M.obj
    (T.regularTranslation g) (M.structureIso g).hom.hom (T.equivariantStructure_semilinear M g),
    T.regular_element_translation]
  by_cases hg : g = 1
  · subst g
    have h := congrArg (fun k => k.hom) M.unit
    change (M.structureIso 1).hom.hom = 𝟙 M.obj.X at h
    simp only [ite_true, h, MonoidalCategory.whiskerLeft_id, Category.id_comp]
    rw [InternalModule.one_smul, Iso.inv_hom_id]
  · simp only [if_neg hg, MonoidalPreadditive.zero_whiskerRight, zero_comp, comp_zero]

/-- Conjugating the actual free-module action map has the explicit
semilinear form supplied by the actual equivariant structure. -/
theorem TannakianCenter.conjugate_actionHom_hom
    (M : T.deequivariantAction.Equivariant) (g : G) :
    (WeakAction.Equivariant.conjugate T.deequivariantAction
      (T.descentComparison.obj M.obj.X) M g (InternalModule.actionHom M.obj)).hom =
        (T.regularAlgebra ◁ (M.structureIso g).hom.hom) ≫ γ[T.regularAlgebra,M.obj.X] := by
  have h := (M.structureIso g).hom.isMod_Hom.smul_hom
  change ((T.regularTranslation g⁻¹ ▷ M.obj.X) ≫ γ[T.regularAlgebra,M.obj.X]) ≫
      (M.structureIso g).hom.hom = _ at h
  change (T.freeEquivariantIso M.obj.X g).inv.hom ≫ γ[T.regularAlgebra,M.obj.X] ≫
    (M.structureIso g).hom.hom = _
  rw [T.freeEquivariantIso_inv_hom]
  exact (Category.assoc _ _ _).symm.trans h

end Paper18.Category

namespace Paper18.Category.InternalModule
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {A : C} [MonObj A]

@[simp]
theorem sum_hom {I : Type*} (s : Finset I) {M N : Mod_ C A} (f : I → (M ⟶ N)) :
    (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom :=
  (Mod_.forget (D := C) A).map_sum f s

end Paper18.Category.InternalModule

namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {G : Type} [Group G] [Fintype G] (T : TannakianCenter C G)

/-- Average the actual free action map to produce an actual equivariant
cover from an object in the descent comparison image. -/
def TannakianCenter.descentCover (M : T.deequivariantAction.Equivariant) :
    T.descentComparison.obj M.obj.X ⟶ M :=
  WeakAction.Equivariant.average T.deequivariantAction (InternalModule.actionHom M.obj)

theorem TannakianCenter.descentCover_hom (M : T.deequivariantAction.Equivariant) :
    (T.descentCover M).hom.hom = (Fintype.card G : ℂ)⁻¹ •
      ∑ g : G, (T.regularAlgebra ◁ (M.structureIso g).hom.hom) ≫ γ[T.regularAlgebra,M.obj.X] := by
  change ((Fintype.card G : ℂ)⁻¹ •
    ∑ g : G, WeakAction.Equivariant.conjugate T.deequivariantAction
      (T.descentComparison.obj M.obj.X) M g (InternalModule.actionHom M.obj)).hom = _
  rw [InternalModule.smul_hom, InternalModule.sum_hom]
  simp only [T.conjugate_actionHom_hom]

/-- Diagonal orthogonality gives a genuine splitting identity for the
averaged actual free action map. -/
theorem TannakianCenter.moduleSection_descentCover (M : T.deequivariantAction.Equivariant) :
    T.regularAlgebraSeparable.moduleSection M.obj ≫ (T.descentCover M).hom.hom =
      (Fintype.card G : ℂ)⁻¹ • 𝟙 M.obj.X := by
  rw [T.descentCover_hom, Linear.comp_smul, Preadditive.comp_sum]
  simp only [T.moduleSection_structure]
  simp

/-- Every actual equivariant module is an actual retract of a free
equivariant module in the descent comparison image. -/
theorem TannakianCenter.descentComparison_retract_dominant
    (M : T.deequivariantAction.Equivariant) :
    Nonempty (Retract M (T.descentComparison.obj M.obj.X)) := by
  let s : M.obj ⟶ (T.descentComparison.obj M.obj.X).obj :=
    (Fintype.card G : ℂ) • T.regularAlgebraSeparable.moduleSectionHom M.obj
  have hs : s ≫ (T.descentCover M).hom = 𝟙 M.obj := by
    apply Mod_.Hom.ext
    change ((Fintype.card G : ℂ) • T.regularAlgebraSeparable.moduleSection M.obj) ≫
      (T.descentCover M).hom.hom = 𝟙 _
    rw [Linear.smul_comp, T.moduleSection_descentCover, smul_smul, mul_inv_cancel₀, one_smul]
    exact_mod_cast Fintype.card_ne_zero
  let E := WeakAction.Equivariant.splitEpiOfUnderlyingSection
    T.deequivariantAction (T.descentCover M) s hs
  exact ⟨⟨E.section_, T.descentCover M, E.id⟩⟩

end Paper18.Category
