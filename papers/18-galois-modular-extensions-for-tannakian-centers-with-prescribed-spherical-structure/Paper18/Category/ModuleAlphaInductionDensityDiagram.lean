import Paper18.Category.ModuleAlphaInductionDensityDiagramCentral

/-! # Actual full-neutral recovery in the alpha-induction density diagram

The extracted contraction is an actual ambient morphism between neutral
objects. Actual fullness of the neutral inclusion lifts it to the source;
its actual central lift then proves the crossing commutation needed to
recover the original morphism. Alpha-induction fullness is not assumed.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u vC uC w
namespace Paper18.Category.ModuleAlphaInduction
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  {C : Type uC} [Category.{vC} C]
  (F : C ⥤ Center D) [(F ⋙ Center.forget D).Full]
  {X Y : C} {n p : D}

/-- The actual full neutral inclusion proves that the extracted actual
contraction respects all the true central half-braidings. -/
theorem leftClosure_comm_of_full (cup : 𝟙_ D ⟶ p ⊗ n) (cap : p ⊗ n ⟶ 𝟙_ D)
    (f : (F.obj X).1 ⊗ n ⟶ (F.obj Y).1 ⊗ n) (q : D) :
    let a := ModuleFunctor.leftClosure cup cap
      (((F.obj X).2.β n).inv ≫ f ≫ ((F.obj Y).2.β n).hom)
    a ▷ q ≫ ((F.obj Y).2.β q).hom = ((F.obj X).2.β q).hom ≫ q ◁ a := by
  let a := ModuleFunctor.leftClosure cup cap
    (((F.obj X).2.β n).inv ≫ f ≫ ((F.obj Y).2.β n).hom)
  let a₀ := (F ⋙ Center.forget D).preimage a
  have ha : (F.map a₀).f = a := (F ⋙ Center.forget D).map_preimage a
  change a ▷ q ≫ ((F.obj Y).2.β q).hom = ((F.obj X).2.β q).hom ≫ q ◁ a
  rw [← ha]
  exact (F.map a₀).comm q

/-- The actual normalized matrix-action relation gives the exact requested
right-tensor recovery. Actual fullness is used only for neutral morphisms,
whose centrality is then proved by the actual central lift. -/
theorem eq_leftClosure_whiskerRight_of_full
    (cup : 𝟙_ D ⟶ p ⊗ n) (cap : p ⊗ n ⟶ 𝟙_ D)
    (hnorm : cup ≫ cap = 𝟙 (𝟙_ D))
    (f : (F.obj X).1 ⊗ n ⟶ (F.obj Y).1 ⊗ n)
    (h : centralCapAction (F.obj X) cap ≫ f =
      (n ⊗ p) ◁ f ≫ centralCapAction (F.obj Y) cap) :
    f = ModuleFunctor.leftClosure cup cap
      (((F.obj X).2.β n).inv ≫ f ≫ ((F.obj Y).2.β n).hom) ▷ n :=
  eq_closure_whiskerRight_of_central (F.obj X) (F.obj Y) cup cap hnorm f h
    (leftClosure_comm_of_full F cup cap f n)

/-- Actual recovery produces an actual morphism in the neutral source,
with the required actual right tensor image. -/
theorem exists_preimage_whiskerRight_of_capAction
    (cup : 𝟙_ D ⟶ p ⊗ n) (cap : p ⊗ n ⟶ 𝟙_ D)
    (hnorm : cup ≫ cap = 𝟙 (𝟙_ D))
    (f : (F.obj X).1 ⊗ n ⟶ (F.obj Y).1 ⊗ n)
    (h : centralCapAction (F.obj X) cap ≫ f =
      (n ⊗ p) ◁ f ≫ centralCapAction (F.obj Y) cap) :
    ∃ a : X ⟶ Y, f = (F.map a).f ▷ n := by
  let a := ModuleFunctor.leftClosure cup cap
    (((F.obj X).2.β n).inv ≫ f ≫ ((F.obj Y).2.β n).hom)
  refine ⟨(F ⋙ Center.forget D).preimage a, ?_⟩
  have ha : (F.map ((F ⋙ Center.forget D).preimage a)).f = a :=
    (F ⋙ Center.forget D).map_preimage a
  rw [ha]
  exact eq_leftClosure_whiskerRight_of_full F cup cap hnorm f h

section Semisimple
attribute [local instance 2000] RightRigidCategory.rightDual
variable [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D] [Simple (𝟙_ D)]
  [∀ A B : D, FiniteDimensional ℂ (A ⟶ B)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (n : D) [Simple n]

/-- Specialization to the actual normalized left cup constructed by
semisimplicity. Its normalization is proved, with no ambient braiding or
pivotal structure. -/
theorem eq_simpleLeftContraction_whiskerRight
    (f : (F.obj X).1 ⊗ n ⟶ (F.obj Y).1 ⊗ n)
    (h : centralCapAction (F.obj X) (ε_ n (dual D n)) ≫ f =
      (n ⊗ dual D n) ◁ f ≫ centralCapAction (F.obj Y) (ε_ n (dual D n))) :
    f = ModuleFunctor.simpleLeftContraction S n
      (((F.obj X).2.β n).inv ≫ f ≫ ((F.obj Y).2.β n).hom) ▷ n :=
  eq_leftClosure_whiskerRight_of_full F (ModuleFunctor.normalizedLeftCup S n)
    (ε_ n (dual D n)) (ModuleFunctor.normalizedLeftCup_evaluation S n) f h

end Semisimple
end Paper18.Category.ModuleAlphaInduction
