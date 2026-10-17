import Paper18.Category.LocalModulesCoherence

/-! # Actual tensor restriction along algebra automorphisms

Twisting both module actions by an algebra automorphism changes the two
balancing maps by the same invertible precomposition. The balancing
quotients therefore give the actual strong tensor comparison.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.BraidedCategory
open scoped MonObj
universe v u
namespace Paper18.Category.RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [HasCoequalizers C] {A : C} [MonObj A] [IsCommMonObj A]
  (e : A ≅ A) [IsMonHom e.hom]

/-- Restrict the actual module action along an actual algebra automorphism. -/
abbrev restriction : Mod_ C A ⥤ Mod_ C A := Mod_.comap e.hom

omit [BraidedCategory C] [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A] in
@[simp]
theorem restriction_action (M : Mod_ C A) :
    γ[A,((restriction e).obj M).X] = (e.hom ▷ M.X) ≫ γ[A,M.X] := rfl

omit [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A] in
@[reassoc]
theorem restriction_rightAction (M : Mod_ C A) :
    rightAction ((restriction e).obj M) = (M.X ◁ e.hom) ≫ rightAction M := by
  unfold rightAction
  rw [restriction_action]
  exact (braiding_naturality_right_assoc M.X e.hom _).symm

omit [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A] in
@[reassoc]
theorem restriction_parallelLeft (M N : Mod_ C A) :
    parallelLeft ((restriction e).obj M) ((restriction e).obj N) =
      ((M.X ◁ e.hom) ▷ N.X) ≫ parallelLeft M N := by
  unfold parallelLeft
  rw [restriction_rightAction, comp_whiskerRight]
  rfl

omit [BraidedCategory C] [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A] in
@[reassoc]
theorem restriction_parallelRight (M N : Mod_ C A) :
    parallelRight ((restriction e).obj M) ((restriction e).obj N) =
      ((M.X ◁ e.hom) ▷ N.X) ≫ parallelRight M N := by
  unfold parallelRight
  rw [restriction_action, whiskerLeft_comp]
  exact (associator_naturality_middle_assoc M.X e.hom N.X _).symm

omit [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A] in
/-- The same underlying map is balanced before and after simultaneous
restriction of both actions. -/
theorem restriction_balanced_iff (M N : Mod_ C A) {Z : C} (f : M.X ⊗ N.X ⟶ Z) :
    Balanced ((restriction e).obj M) ((restriction e).obj N) f ↔ Balanced M N f := by
  unfold Balanced
  rw [restriction_parallelLeft, restriction_parallelRight]
  simp only [Category.assoc]
  exact cancel_epi ((M.X ◁ e.hom) ▷ N.X)

/-- The quotient comparison is an actual module morphism. -/
def restrictionTensorHom (M N : Mod_ C A) :
    (restriction e).obj M ⊗ (restriction e).obj N ⟶ (restriction e).obj (M ⊗ N) :=
  descModule _ _ _ (π M N) ((restriction_balanced_iff e M N _).mpr (condition M N)) (by
    rw [restriction_action, restriction_action]
    change (α_ A M.X N.X).inv ≫ ((e.hom ▷ M.X) ≫ γ[A,M.X]) ▷ N.X ≫ π M N =
      (A ◁ π M N) ≫ (e.hom ▷ (M ⊗ N).X) ≫ γ[A,(M ⊗ N).X]
    calc
      _ = (e.hom ▷ (M.X ⊗ N.X)) ≫ (α_ A M.X N.X).inv ≫ γ[A,M.X] ▷ N.X ≫ π M N := by
        monoidal
      _ = (e.hom ▷ (M.X ⊗ N.X)) ≫ (A ◁ π M N) ≫ γ[A,(M ⊗ N).X] := by
        rw [π_action]
      _ = _ := by erw [whisker_exchange_assoc])

@[reassoc (attr := simp)]
theorem π_restrictionTensorHom (M N : Mod_ C A) :
    π ((restriction e).obj M) ((restriction e).obj N) ≫ (restrictionTensorHom e M N).hom = π M N :=
  π_desc _ _ _ _

omit [BraidedCategory C] [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A] in
private theorem isIso_of_hom {M N : Mod_ C A} (f : M ⟶ N) [IsIso f.hom] : IsIso f := by
  letI : IsMod_Hom A (asIso f.hom).hom := f.isMod_Hom
  let h : N ⟶ M := ⟨(asIso f.hom).inv⟩
  refine ⟨⟨h, ?_, ?_⟩⟩
  · apply Mod_.Hom.ext
    exact IsIso.hom_inv_id f.hom
  · apply Mod_.Hom.ext
    exact IsIso.inv_hom_id f.hom

instance restrictionTensorHom_isIso (M N : Mod_ C A) : IsIso (restrictionTensorHom e M N) := by
  let d := desc M N (π ((restriction e).obj M) ((restriction e).obj N))
    ((restriction_balanced_iff e M N _).mp (condition _ _))
  let z : ((restriction e).obj M ⊗ (restriction e).obj N).X ≅ (M ⊗ N).X :=
    { hom := (restrictionTensorHom e M N).hom
      inv := d
      hom_inv_id := by
        apply hom_ext ((restriction e).obj M) ((restriction e).obj N)
        change π ((restriction e).obj M) ((restriction e).obj N) ≫
          (restrictionTensorHom e M N).hom ≫ d = π ((restriction e).obj M) ((restriction e).obj N) ≫ 𝟙 _
        rw [π_restrictionTensorHom_assoc]
        dsimp only [d]
        rw [π_desc]
        erw [Category.comp_id]
      inv_hom_id := by
        apply hom_ext M N
        dsimp only [d]
        rw [π_desc_assoc, π_restrictionTensorHom]
        erw [Category.comp_id] }
  letI : IsIso (restrictionTensorHom e M N).hom := z.isIso_hom
  exact isIso_of_hom (restrictionTensorHom e M N)

/-- The automorphism itself intertwines the regular module with its twist. -/
def restrictionUnitHom : (𝟙_ (Mod_ C A)) ⟶ (restriction e).obj (𝟙_ (Mod_ C A)) :=
  Mod_.Hom.mk' e.hom (by
    change μ[A] ≫ e.hom = (A ◁ e.hom) ≫ (e.hom ▷ A) ≫ μ[A]
    rw [IsMonHom.mul_hom, MonoidalCategory.tensorHom_def', Category.assoc])

@[simp] theorem restrictionUnitHom_hom : (restrictionUnitHom e).hom = e.hom := rfl

instance restrictionUnitHom_isIso : IsIso (restrictionUnitHom e) := by
  letI : IsIso (restrictionUnitHom e).hom := e.isIso_hom
  exact isIso_of_hom (restrictionUnitHom e)

/-- Restriction preserves tensor products through the actual balancing quotient. -/
instance restrictionLaxMonoidal : (restriction e).LaxMonoidal where
  ε := restrictionUnitHom e
  «μ» M N := restrictionTensorHom e M N
  μ_natural_left f P := by
    apply module_hom_ext
    change π ((restriction e).obj _) ((restriction e).obj P) ≫
        ((restriction e).map f ▷ (restriction e).obj P).hom ≫ (restrictionTensorHom e _ P).hom =
      π ((restriction e).obj _) ((restriction e).obj P) ≫ (restrictionTensorHom e _ P).hom ≫
        (f ▷ P).hom
    rw [π_whiskerRight_assoc, π_restrictionTensorHom, π_restrictionTensorHom_assoc,
      π_whiskerRight]
    rfl
  μ_natural_right P f := by
    apply module_hom_ext
    change π ((restriction e).obj P) ((restriction e).obj _) ≫
        ((restriction e).obj P ◁ (restriction e).map f).hom ≫ (restrictionTensorHom e P _).hom =
      π ((restriction e).obj P) ((restriction e).obj _) ≫ (restrictionTensorHom e P _).hom ≫
        (P ◁ f).hom
    rw [π_whiskerLeft_assoc, π_restrictionTensorHom, π_restrictionTensorHom_assoc,
      π_whiskerLeft]
    rfl
  associativity M N P := by
    apply triple_hom_ext
    change (π ((restriction e).obj M) ((restriction e).obj N) ▷ P.X) ≫
        π ((restriction e).obj M ⊗ (restriction e).obj N) ((restriction e).obj P) ≫
        (restrictionTensorHom e M N ▷ (restriction e).obj P).hom ≫
        (restrictionTensorHom e (M ⊗ N) P).hom ≫ (α_ M N P).hom.hom =
      (π ((restriction e).obj M) ((restriction e).obj N) ▷ P.X) ≫
        π ((restriction e).obj M ⊗ (restriction e).obj N) ((restriction e).obj P) ≫
        (α_ ((restriction e).obj M) ((restriction e).obj N) ((restriction e).obj P)).hom.hom ≫
        ((restriction e).obj M ◁ restrictionTensorHom e N P).hom ≫
        (restrictionTensorHom e M (N ⊗ P)).hom
    erw [π_whiskerRight_assoc, ← comp_whiskerRight_assoc, π_restrictionTensorHom,
      π_restrictionTensorHom_assoc, π_associator]
    erw [π_associator_assoc ((restriction e).obj M) ((restriction e).obj N)
      ((restriction e).obj P), π_whiskerLeft_assoc, ← whiskerLeft_comp_assoc,
      π_restrictionTensorHom, π_restrictionTensorHom]
    try rfl
  left_unitality M := by
    apply module_hom_ext
    change π (𝟙_ (Mod_ C A)) ((restriction e).obj M) ≫
        (λ_ ((restriction e).obj M)).hom.hom =
      π (𝟙_ (Mod_ C A)) ((restriction e).obj M) ≫
        (restrictionUnitHom e ▷ (restriction e).obj M).hom ≫
        (restrictionTensorHom e (𝟙_ (Mod_ C A)) M).hom ≫ (λ_ M).hom.hom
    rw [π_leftUnitor, π_whiskerRight_assoc, π_restrictionTensorHom_assoc, π_leftUnitor]
    rfl
  right_unitality M := by
    apply module_hom_ext
    change π ((restriction e).obj M) (𝟙_ (Mod_ C A)) ≫
        (ρ_ ((restriction e).obj M)).hom.hom =
      π ((restriction e).obj M) (𝟙_ (Mod_ C A)) ≫
        ((restriction e).obj M ◁ restrictionUnitHom e).hom ≫
        (restrictionTensorHom e M (𝟙_ (Mod_ C A))).hom ≫ (ρ_ M).hom.hom
    rw [π_rightUnitor, π_whiskerLeft_assoc, π_restrictionTensorHom_assoc, π_rightUnitor,
      restriction_rightAction]
    rfl

instance restriction_ε_isIso : IsIso (Functor.LaxMonoidal.ε (restriction e)) :=
  inferInstanceAs (IsIso (restrictionUnitHom e))

instance restriction_μ_isIso (M N : Mod_ C A) :
    IsIso (Functor.LaxMonoidal.μ (restriction e) M N) :=
  inferInstanceAs (IsIso (restrictionTensorHom e M N))

/-- An actual algebra automorphism induces an actual strong monoidal
restriction functor. -/
instance restrictionMonoidal : (restriction e).Monoidal :=
  Functor.CoreMonoidal.toMonoidal (Functor.CoreMonoidal.ofLaxMonoidal (restriction e))

@[reassoc]
theorem π_restriction_μ (M N : Mod_ C A) :
    π ((restriction e).obj M) ((restriction e).obj N) ≫
      (Functor.LaxMonoidal.μ (restriction e) M N).hom = π M N :=
  π_restrictionTensorHom e M N

@[simp]
theorem restriction_ε_hom : (Functor.LaxMonoidal.ε (restriction e)).hom = e.hom := rfl

/-- For a transparent algebra the strong restriction functor preserves
the actual module braiding. -/
def restrictionBraidedOfTransparent (hA : A ∈ mugerCenter (C := C)) :
    letI := moduleBraidedOfTransparent hA
    (restriction e).Braided := by
  letI := moduleBraidedOfTransparent hA
  refine { toMonoidal := restrictionMonoidal e, braided := ?_ }
  intro M N
  apply module_hom_ext
  change π ((restriction e).obj M) ((restriction e).obj N) ≫
      (Functor.LaxMonoidal.μ (restriction e) M N).hom ≫ (β_ M N).hom.hom =
    π ((restriction e).obj M) ((restriction e).obj N) ≫
      (β_ ((restriction e).obj M) ((restriction e).obj N)).hom.hom ≫
      (Functor.LaxMonoidal.μ (restriction e) N M).hom
  rw [π_restriction_μ_assoc, π_moduleBraidingOfTransparent,
    π_moduleBraidingOfTransparent_assoc, π_restriction_μ]
  rfl

end Paper18.Category.RelativeTensor
