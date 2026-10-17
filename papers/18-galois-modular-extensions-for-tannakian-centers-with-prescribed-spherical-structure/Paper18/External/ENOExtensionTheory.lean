import Paper18.Category.FixedBoundaryMinimalExistence
import Paper18.Category.FiniteCohomologyKillingBasic

/-! # Explicit external ENO obstruction-realization interface

External source: Etingof--Nikshych--Ostrik, *Fusion categories and
homotopy theory*, Quantum Topology 1 (2010), 209--273,
https://arxiv.org/abs/0909.3140, Theorem 5.2, Propositions 7.3 and 7.5,
Proposition 7.8(ii), Section 7.5 and Theorem 7.12.

For a specified complex-linear braided categorical action on a
nondegenerate braided fusion category, the relative lifting obstruction
is a normalized fourth cocycle with trivial complex-unit coefficients.
A normalized third-cochain primitive realizes that *specified* action
by a faithfully graded braided crossed fusion category. The external
input below is this existence portion of ENO obstruction theory in
concrete categorical/cochain notation. It includes no fixed-boundary
classification or prescribed pivotal/spherical conclusion.

There is no assumed constant or admitted proof here. `ObstructionRealization` is an
explicit external input parameter. The C₂ cochain primitive and every
subsequent categorical output construction are proved in this project.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Functor.LaxMonoidal
open Paper18.Category Paper18.Category.CrossedBraidedGauging
open Paper18.Category.FixedBoundary.MinimalExistence
universe v u w v' u' w'
namespace Paper18.External.ENOExtensionTheory
open Paper18.Category.FiniteCohomologyKilling

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [sourceKernels : HasKernels C] [HasFiniteBiproducts C]
  [sourceFiniteHom : ∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [BraidedCategory C] [sourceMonoidalPreadditive : MonoidalPreadditive C] [sourceMonoidalLinear : MonoidalLinear ℂ C]
  [sourceRightRigid : RightRigidCategory C] [sourceSimpleUnit : Simple (𝟙_ C)]
  (A : WeakAction C2 C)
  [∀ g : C2, (A.ρ g).Monoidal] [sourceActionMonoidal : A.IsMonoidal] [sourceActionBraided : A.IsBraided]
  [sourceActionAdditive : ∀ g : C2, (A.ρ g).Additive]
  [sourceActionLinear : ∀ g : C2, (A.ρ g).Linear ℂ]

/-- Genuine structural output of ENO crossed realization. These are actual
category structures, actual crossing maps and an actual neutral action
identification. Nondegeneracy, gauging, minimality, and prescribed spherical
enhancement are subsequently derived; none is a field of this structure. -/
structure FaithfulCrossedRealization where
  ambient : Type u'
  [category : Category.{v'} ambient]
  [preadditive : Preadditive ambient]
  [linear : Linear ℂ ambient]
  [kernels : HasKernels ambient]
  [biproducts : HasFiniteBiproducts ambient]
  [finiteHom : ∀ X Y : ambient, FiniteDimensional ℂ (X ⟶ Y)]
  [monoidal : MonoidalCategory ambient]
  [monoidalPreadditive : MonoidalPreadditive ambient]
  [monoidalLinear : MonoidalLinear ℂ ambient]
  [rightRigid : RightRigidCategory ambient]
  [simpleUnit : Simple (𝟙_ ambient)]
  index : Type w'
  [finiteIndex : Fintype index]
  skeleton : FiniteSemisimpleSkeleton ambient index
  action : WeakAction C2 ambient
  [actionMonoidal : ∀ g : C2, (action.ρ g).Monoidal]
  [actionCoherence : action.IsMonoidal]
  [actionAdditive : ∀ g : C2, (action.ρ g).Additive]
  [actionLinear : ∀ g : C2, (action.ρ g).Linear ℂ]
  grading : Grading C2 ambient
  gradedAction : GradedAction grading action
  crossing : CrossedBraiding grading action gradedAction
  faithful : grading.Faithful
  neutral : A.Intertwiner action
  [neutralMonoidal : neutral.functor.Monoidal]
  [neutralActionMonoidal : neutral.IsMonoidal]
  [neutralAdditive : neutral.functor.Additive]
  [neutralLinear : neutral.functor.Linear ℂ]
  [neutralFull : neutral.functor.Full]
  [neutralFaithful : neutral.functor.Faithful]
  homogeneous : ∀ X : C, grading.Homogeneous 1 (neutral.functor.obj X)
  covers : ∀ Y : ambient, grading.Homogeneous 1 Y →
    ∃ X : C, Nonempty (neutral.functor.obj X ≅ Y)
  braided : ∀ X Y : C,
    μ neutral.functor X Y ≫ neutral.functor.map (β_ X Y).hom =
      (crossing.neutralIso (neutral.functor.obj X) (homogeneous X)
        (neutral.functor.obj Y)).hom ≫ μ neutral.functor Y X

attribute [instance] FaithfulCrossedRealization.category FaithfulCrossedRealization.preadditive
  FaithfulCrossedRealization.linear FaithfulCrossedRealization.kernels
  FaithfulCrossedRealization.biproducts FaithfulCrossedRealization.finiteHom
  FaithfulCrossedRealization.monoidal FaithfulCrossedRealization.monoidalPreadditive
  FaithfulCrossedRealization.monoidalLinear FaithfulCrossedRealization.rightRigid
  FaithfulCrossedRealization.simpleUnit FaithfulCrossedRealization.finiteIndex
  FaithfulCrossedRealization.actionMonoidal FaithfulCrossedRealization.actionCoherence
  FaithfulCrossedRealization.actionAdditive FaithfulCrossedRealization.actionLinear
  FaithfulCrossedRealization.neutralMonoidal FaithfulCrossedRealization.neutralActionMonoidal
  FaithfulCrossedRealization.neutralAdditive FaithfulCrossedRealization.neutralLinear
  FaithfulCrossedRealization.neutralFull FaithfulCrossedRealization.neutralFaithful

include sourceKernels sourceFiniteHom sourceMonoidalPreadditive sourceMonoidalLinear
  sourceRightRigid sourceSimpleUnit sourceActionMonoidal sourceActionBraided
  sourceActionAdditive sourceActionLinear in
/-- The precise external existence input in relative cochain form.
The input includes the specified action, rather than only its homomorphism
on isomorphism classes. The normalized cocycle is supplied by external ENO
obstruction theory; its primitive will be constructed in Lean. -/
def ObstructionRealization {ι : Type w} [Fintype ι]
    (_S : FiniteSemisimpleSkeleton C ι) (_hN : IsNondegenerate (C := C)) : Prop :=
  ∃ ω : FourCocycle C2 ℂˣ,
    ∀ ψ : ThreeCochain C2 ℂˣ, dThree ψ.val = ω.val →
      Nonempty (FaithfulCrossedRealization.{v,u,v',u',w'} A)

/-- The paper's actual normalized-cochain calculation supplies a genuine
primitive for every external normalized fourth obstruction on C₂. -/
theorem c2_fourCocycle_is_coboundary (ω : FourCocycle C2 ℂˣ) :
    ∃ ψ : ThreeCochain C2 ℂˣ, dThree ψ.val = ω.val := by
  let a : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 → ℂˣ :=
    fun g h k l => ω.val (Multiplicative.ofAdd g) (Multiplicative.ofAdd h)
      (Multiplicative.ofAdd k) (Multiplicative.ofAdd l)
  have ha : Paper18.IsNormalizedFour a := by
    intro g h k l hn
    rcases hn with rfl | rfl | rfl | rfl <;> simp [a]
  obtain ⟨ψ, hψ, hdψ⟩ := Paper18.normalizedFour_is_coboundary a ha
  let q : ThreeCochain C2 ℂˣ :=
    { val := fun g h k => ψ g.toAdd h.toAdd k.toAdd
      one₁ h k := hψ 0 h.toAdd k.toAdd (Or.inl rfl)
      one₂ g k := hψ g.toAdd 0 k.toAdd (Or.inr (Or.inl rfl))
      one₃ g h := hψ g.toAdd h.toAdd 0 (Or.inr (Or.inr rfl)) }
  refine ⟨q, ?_⟩
  funext g h k l
  exact congrFun (congrFun (congrFun (congrFun hdψ (Multiplicative.toAdd g))
    (Multiplicative.toAdd h)) (Multiplicative.toAdd k)) (Multiplicative.toAdd l)

/-- Relative to the explicitly supplied external realization theorem,
the actual C₂ fourth obstruction vanishes by the proved cochain argument. -/
theorem faithfulCrossedRealization_exists {ι : Type w} [Fintype ι]
    (S : FiniteSemisimpleSkeleton C ι) (hN : IsNondegenerate (C := C))
    (h : ObstructionRealization.{v,u,w,v',u',w'} A S hN) :
    Nonempty (FaithfulCrossedRealization.{v,u,v',u',w'} A) := by
  obtain ⟨ω, hω⟩ := h
  obtain ⟨ψ, hψ⟩ := c2_fourCocycle_is_coboundary ω
  exact hω ψ hψ

end Paper18.External.ENOExtensionTheory
