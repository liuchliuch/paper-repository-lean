import Paper18.Category.FixedBoundaryRestriction
import Paper18.Category.RelativeTensorCoherence

/-! # Strong tensor restriction along an isomorphism of actual commutative algebras -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.BraidedCategory
open scoped MonObj
universe v u
namespace Paper18.Category.InternalModule
open RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [HasCoequalizers C] {A B : C} [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
  (e : A ≅ B) [IsMonHom e.hom]

/-- Restrict the actual module action along an actual algebra isomorphism. -/
abbrev algebraComap : Mod_ C B ⥤ Mod_ C A := Mod_.comap e.hom

omit [BraidedCategory C] [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A] in
@[simp]
theorem algebraComap_action (M : Mod_ C B) :
    γ[A,((algebraComap e).obj M).X] = (e.hom ▷ M.X) ≫ γ[B,M.X] := rfl

omit [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A] in
@[reassoc]
theorem algebraComap_rightAction (M : Mod_ C B) :
    rightAction ((algebraComap e).obj M) = (M.X ◁ e.hom) ≫ rightAction M := by
  unfold rightAction
  rw [algebraComap_action]
  exact (braiding_naturality_right_assoc M.X e.hom _).symm

omit [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A] in
@[reassoc]
theorem algebraComap_parallelLeft (M N : Mod_ C B) :
    parallelLeft ((algebraComap e).obj M) ((algebraComap e).obj N) =
      ((M.X ◁ e.hom) ▷ N.X) ≫ parallelLeft M N := by
  unfold parallelLeft
  rw [algebraComap_rightAction, comp_whiskerRight]
  rfl

omit [BraidedCategory C] [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A] in
@[reassoc]
theorem algebraComap_parallelRight (M N : Mod_ C B) :
    parallelRight ((algebraComap e).obj M) ((algebraComap e).obj N) =
      ((M.X ◁ e.hom) ▷ N.X) ≫ parallelRight M N := by
  unfold parallelRight
  rw [algebraComap_action, whiskerLeft_comp]
  exact (associator_naturality_middle_assoc M.X e.hom N.X _).symm

omit [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A] in
/-- The same underlying map is balanced before and after simultaneous
restriction of both actions. -/
theorem algebraComap_balanced_iff (M N : Mod_ C B) {Z : C} (f : M.X ⊗ N.X ⟶ Z) :
    RelativeTensor.Balanced ((algebraComap e).obj M) ((algebraComap e).obj N) f ↔ RelativeTensor.Balanced M N f := by
  unfold RelativeTensor.Balanced
  rw [algebraComap_parallelLeft, algebraComap_parallelRight]
  simp only [Category.assoc]
  exact cancel_epi ((M.X ◁ e.hom) ▷ N.X)

/-- The quotient comparison is an actual module morphism. -/
def algebraComapTensorHom (M N : Mod_ C B) :
    (algebraComap e).obj M ⊗ (algebraComap e).obj N ⟶ (algebraComap e).obj (M ⊗ N) :=
  descModule _ _ _ (π M N) ((algebraComap_balanced_iff e M N _).mpr (condition M N)) (by
    rw [algebraComap_action, algebraComap_action]
    change (α_ A M.X N.X).inv ≫ ((e.hom ▷ M.X) ≫ γ[B,M.X]) ▷ N.X ≫ π M N =
      (A ◁ π M N) ≫ (e.hom ▷ (M ⊗ N).X) ≫ γ[B,(M ⊗ N).X]
    calc
      _ = (e.hom ▷ (M.X ⊗ N.X)) ≫ (α_ B M.X N.X).inv ≫ γ[B,M.X] ▷ N.X ≫ π M N := by
        monoidal
      _ = (e.hom ▷ (M.X ⊗ N.X)) ≫ (B ◁ π M N) ≫ γ[B,(M ⊗ N).X] := by
        rw [π_action]
      _ = _ := by erw [whisker_exchange_assoc])

@[reassoc (attr := simp)]
theorem π_algebraComapTensorHom (M N : Mod_ C B) :
    π ((algebraComap e).obj M) ((algebraComap e).obj N) ≫ (algebraComapTensorHom e M N).hom = π M N :=
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

instance algebraComapTensorHom_isIso (M N : Mod_ C B) : IsIso (algebraComapTensorHom e M N) := by
  let d := desc M N (π ((algebraComap e).obj M) ((algebraComap e).obj N))
    ((algebraComap_balanced_iff e M N _).mp (condition _ _))
  let z : ((algebraComap e).obj M ⊗ (algebraComap e).obj N).X ≅ (M ⊗ N).X :=
    { hom := (algebraComapTensorHom e M N).hom
      inv := d
      hom_inv_id := by
        apply hom_ext ((algebraComap e).obj M) ((algebraComap e).obj N)
        change π ((algebraComap e).obj M) ((algebraComap e).obj N) ≫
          (algebraComapTensorHom e M N).hom ≫ d = π ((algebraComap e).obj M) ((algebraComap e).obj N) ≫ 𝟙 _
        rw [π_algebraComapTensorHom_assoc]
        dsimp only [d]
        rw [π_desc]
        erw [Category.comp_id]
      inv_hom_id := by
        apply hom_ext M N
        dsimp only [d]
        rw [π_desc_assoc, π_algebraComapTensorHom]
        erw [Category.comp_id] }
  letI : IsIso (algebraComapTensorHom e M N).hom := z.isIso_hom
  exact isIso_of_hom (algebraComapTensorHom e M N)

/-- The algebra isomorphism itself intertwines the regular module with its twist. -/
def algebraComapUnitHom : (𝟙_ (Mod_ C A)) ⟶ (algebraComap e).obj (𝟙_ (Mod_ C B)) :=
  Mod_.Hom.mk' e.hom (by
    change μ[A] ≫ e.hom = (A ◁ e.hom) ≫ (e.hom ▷ B) ≫ μ[B]
    rw [IsMonHom.mul_hom, MonoidalCategory.tensorHom_def', Category.assoc])

@[simp] theorem algebraComapUnitHom_hom : (algebraComapUnitHom e).hom = e.hom := rfl

instance algebraComapUnitHom_isIso : IsIso (algebraComapUnitHom e) := by
  letI : IsIso (algebraComapUnitHom e).hom := e.isIso_hom
  exact isIso_of_hom (algebraComapUnitHom e)

/-- Restriction preserves tensor products through the actual balancing quotient. -/
instance algebraComapLaxMonoidal : (algebraComap e).LaxMonoidal where
  ε := algebraComapUnitHom e
  «μ» M N := algebraComapTensorHom e M N
  μ_natural_left f P := by
    apply module_hom_ext
    change π ((algebraComap e).obj _) ((algebraComap e).obj P) ≫
        ((algebraComap e).map f ▷ (algebraComap e).obj P).hom ≫ (algebraComapTensorHom e _ P).hom =
      π ((algebraComap e).obj _) ((algebraComap e).obj P) ≫ (algebraComapTensorHom e _ P).hom ≫
        (f ▷ P).hom
    rw [π_whiskerRight_assoc, π_algebraComapTensorHom, π_algebraComapTensorHom_assoc,
      π_whiskerRight]
    rfl
  μ_natural_right P f := by
    apply module_hom_ext
    change π ((algebraComap e).obj P) ((algebraComap e).obj _) ≫
        ((algebraComap e).obj P ◁ (algebraComap e).map f).hom ≫ (algebraComapTensorHom e P _).hom =
      π ((algebraComap e).obj P) ((algebraComap e).obj _) ≫ (algebraComapTensorHom e P _).hom ≫
        (P ◁ f).hom
    rw [π_whiskerLeft_assoc, π_algebraComapTensorHom, π_algebraComapTensorHom_assoc,
      π_whiskerLeft]
    rfl
  associativity M N P := by
    apply triple_hom_ext
    change (π ((algebraComap e).obj M) ((algebraComap e).obj N) ▷ P.X) ≫
        π ((algebraComap e).obj M ⊗ (algebraComap e).obj N) ((algebraComap e).obj P) ≫
        (algebraComapTensorHom e M N ▷ (algebraComap e).obj P).hom ≫
        (algebraComapTensorHom e (M ⊗ N) P).hom ≫ (α_ M N P).hom.hom =
      (π ((algebraComap e).obj M) ((algebraComap e).obj N) ▷ P.X) ≫
        π ((algebraComap e).obj M ⊗ (algebraComap e).obj N) ((algebraComap e).obj P) ≫
        (α_ ((algebraComap e).obj M) ((algebraComap e).obj N) ((algebraComap e).obj P)).hom.hom ≫
        ((algebraComap e).obj M ◁ algebraComapTensorHom e N P).hom ≫
        (algebraComapTensorHom e M (N ⊗ P)).hom
    erw [π_whiskerRight_assoc, ← comp_whiskerRight_assoc, π_algebraComapTensorHom,
      π_algebraComapTensorHom_assoc, π_associator]
    erw [π_associator_assoc ((algebraComap e).obj M) ((algebraComap e).obj N)
      ((algebraComap e).obj P), π_whiskerLeft_assoc, ← whiskerLeft_comp_assoc,
      π_algebraComapTensorHom, π_algebraComapTensorHom]
    try rfl
  left_unitality M := by
    apply module_hom_ext
    change π (𝟙_ (Mod_ C A)) ((algebraComap e).obj M) ≫
        (λ_ ((algebraComap e).obj M)).hom.hom =
      π (𝟙_ (Mod_ C A)) ((algebraComap e).obj M) ≫
        (algebraComapUnitHom e ▷ (algebraComap e).obj M).hom ≫
        (algebraComapTensorHom e (𝟙_ (Mod_ C B)) M).hom ≫ (λ_ M).hom.hom
    rw [π_leftUnitor, π_whiskerRight_assoc, π_algebraComapTensorHom_assoc, π_leftUnitor]
    rfl
  right_unitality M := by
    apply module_hom_ext
    change π ((algebraComap e).obj M) (𝟙_ (Mod_ C A)) ≫
        (ρ_ ((algebraComap e).obj M)).hom.hom =
      π ((algebraComap e).obj M) (𝟙_ (Mod_ C A)) ≫
        ((algebraComap e).obj M ◁ algebraComapUnitHom e).hom ≫
        (algebraComapTensorHom e M (𝟙_ (Mod_ C B))).hom ≫ (ρ_ M).hom.hom
    rw [π_rightUnitor, π_whiskerLeft_assoc, π_algebraComapTensorHom_assoc, π_rightUnitor,
      algebraComap_rightAction]
    rfl

instance algebraComap_ε_isIso : IsIso (Functor.LaxMonoidal.ε (algebraComap e)) :=
  inferInstanceAs (IsIso (algebraComapUnitHom e))

instance algebraComap_μ_isIso (M N : Mod_ C B) :
    IsIso (Functor.LaxMonoidal.μ (algebraComap e) M N) :=
  inferInstanceAs (IsIso (algebraComapTensorHom e M N))

/-- An actual algebra isomorphism induces an actual strong monoidal
algebraComap functor. -/
instance algebraComapMonoidal : (algebraComap e).Monoidal :=
  Functor.CoreMonoidal.toMonoidal (Functor.CoreMonoidal.ofLaxMonoidal (algebraComap e))

@[reassoc]
theorem π_algebraComap_μ (M N : Mod_ C B) :
    π ((algebraComap e).obj M) ((algebraComap e).obj N) ≫
      (Functor.LaxMonoidal.μ (algebraComap e) M N).hom = π M N :=
  π_algebraComapTensorHom e M N

@[simp]
theorem algebraComap_ε_hom : (Functor.LaxMonoidal.ε (algebraComap e)).hom = e.hom := rfl


end Paper18.Category.InternalModule
