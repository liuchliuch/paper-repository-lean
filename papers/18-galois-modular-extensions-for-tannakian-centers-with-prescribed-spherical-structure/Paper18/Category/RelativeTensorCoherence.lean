import Paper18.Category.RelativeTensorLinear

/-! # Actual quotient formulas for relative-tensor coherence maps -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj
universe v u
namespace Paper18.Category.RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [HasCoequalizers C] {A : C} [MonObj A] [IsCommMonObj A]

@[reassoc (attr := simp)]
theorem π_leftUnitor (M : Mod_ C A) :
    π (𝟙_ (Mod_ C A)) M ≫ (λ_ M).hom.hom = γ[A,M.X] := by
  dsimp [moduleMonoidal, Monoidal.transport, Monoidal.induced, Monoidal.transportStruct,
    canonicalEquivalence, canonicalLift, canonicalForget, canonicalUnitIso,
    canonicalCounitIso, ObjectProperty.isoMk, fromBimod, fromBimodObj,
    toBimod, toBimodObj, Bimod.isoOfIso]
  dsimp [bimodMonoidal, bimodBicategory, Bimod.monBicategory]
  dsimp [Bimod.whiskerRight, Bimod.whiskerLeft, Bimod.leftUnitorBimod,
    Bimod.rightUnitorBimod, Bimod.associatorBimod, Bimod.isoOfIso]
  unfold π
  simp only [Category.comp_id]
  erw [ι_colimMap_assoc, parallelPairHom_app_one]
  simp only [id_whiskerRight]
  dsimp [Bimod.LeftUnitorBimod.hom, Bimod.RightUnitorBimod.hom]
  erw [coequalizer.π_desc]
  change 𝟙 (A ⊗ M.X) ≫ γ[A,M.X] = γ[A,M.X]
  exact Category.id_comp _

@[reassoc (attr := simp)]
theorem π_rightUnitor (M : Mod_ C A) :
    π M (𝟙_ (Mod_ C A)) ≫ (ρ_ M).hom.hom = rightAction M := by
  dsimp [moduleMonoidal, Monoidal.transport, Monoidal.induced, Monoidal.transportStruct,
    canonicalEquivalence, canonicalLift, canonicalForget, canonicalUnitIso,
    canonicalCounitIso, ObjectProperty.isoMk, fromBimod, fromBimodObj,
    toBimod, toBimodObj, Bimod.isoOfIso]
  dsimp [bimodMonoidal, bimodBicategory, Bimod.monBicategory]
  dsimp [Bimod.whiskerRight, Bimod.whiskerLeft, Bimod.leftUnitorBimod,
    Bimod.rightUnitorBimod, Bimod.associatorBimod, Bimod.isoOfIso]
  unfold π
  simp only [Category.comp_id]
  erw [ι_colimMap_assoc, parallelPairHom_app_one]
  simp only [whiskerLeft_id]
  dsimp [Bimod.LeftUnitorBimod.hom, Bimod.RightUnitorBimod.hom]
  erw [coequalizer.π_desc]
  change 𝟙 (M.X ⊗ A) ≫ rightAction M = rightAction M
  exact Category.id_comp _

@[reassoc]
theorem π_associator (M N P : Mod_ C A) :
    (π M N ▷ P.X) ≫ π (M ⊗ N) P ≫ (α_ M N P).hom.hom =
      (α_ M.X N.X P.X).hom ≫ (M.X ◁ π N P) ≫ π M (N ⊗ P) := by
  dsimp [moduleMonoidal, Monoidal.transport, Monoidal.induced, Monoidal.transportStruct,
    canonicalEquivalence, canonicalLift, canonicalForget, canonicalUnitIso,
    canonicalCounitIso, ObjectProperty.isoMk, fromBimod, fromBimodObj,
    toBimod, toBimodObj, Bimod.isoOfIso]
  dsimp [bimodMonoidal, bimodBicategory, Bimod.monBicategory]
  dsimp [Bimod.whiskerRight, Bimod.whiskerLeft, Bimod.leftUnitorBimod,
    Bimod.rightUnitorBimod, Bimod.associatorBimod, Bimod.isoOfIso]
  unfold π
  erw [ι_colimMap_assoc, parallelPairHom_app_one]
  simp only [id_whiskerRight]
  dsimp [Bimod.AssociatorBimod.hom, Bimod.AssociatorBimod.homAux]
  erw [coequalizer.π_desc_assoc]
  dsimp [bimodMonoidal, bimodBicategory, Bimod.monBicategory, Bimod.AssociatorBimod.homAux]
  simp only [Category.assoc]
  erw [Category.id_comp]
  slice_lhs 1 3 => erw [π_tensor_id_preserves_coequalizer_inv_desc]
  dsimp [CategoryTheory.instMonoidalCategoryHom, bimodBicategory,
    Bimod.monBicategory, Bimod.whiskerLeft]
  simp only [Category.assoc]
  erw [ι_colimMap, parallelPairHom_app_one]
  simp only [MonoidalCategory.whiskerLeft_id]
  erw [Category.id_comp]
  rfl

@[reassoc]
theorem π_associator_inv (M N P : Mod_ C A) :
    (M.X ◁ π N P) ≫ π M (N ⊗ P) ≫ (α_ M N P).inv.hom =
      (α_ M.X N.X P.X).inv ≫ (π M N ▷ P.X) ≫ π (M ⊗ N) P := by
  have h := congrArg (fun k => k ≫ (α_ M N P).inv.hom) (π_associator M N P)
  simp only [Category.assoc, ← Mod_.comp_hom', Iso.hom_inv_id, Mod_.id_hom'] at h
  erw [Category.comp_id] at h
  apply (cancel_epi (α_ M.X N.X P.X).hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h.symm

instance π_whiskerRight_epi (M N : Mod_ C A) (X : C) : Epi (π M N ▷ X) := by
  exact inferInstanceAs (Epi ((tensorRight X).map
    (coequalizer.π (parallelLeft M N) (parallelRight M N))))

instance π_whiskerLeft_epi (M N : Mod_ C A) (X : C) : Epi (X ◁ π M N) := by
  exact inferInstanceAs (Epi ((tensorLeft X).map
    (coequalizer.π (parallelLeft M N) (parallelRight M N))))

/-- Maps out of a triple relative tensor are determined before both balancing quotients. -/
theorem triple_hom_ext {M N P Q : Mod_ C A} {f g : (M ⊗ N) ⊗ P ⟶ Q}
    (h : (π M N ▷ P.X) ≫ π (M ⊗ N) P ≫ f.hom =
      (π M N ▷ P.X) ≫ π (M ⊗ N) P ≫ g.hom) : f = g := by
  apply module_hom_ext
  exact (cancel_epi (π M N ▷ P.X)).mp h

/-- The analogous determination for a triple with the other bracketing. -/
theorem triple_hom_ext' {M N P Q : Mod_ C A} {f g : M ⊗ (N ⊗ P) ⟶ Q}
    (h : (M.X ◁ π N P) ≫ π M (N ⊗ P) ≫ f.hom =
      (M.X ◁ π N P) ≫ π M (N ⊗ P) ≫ g.hom) : f = g := by
  apply module_hom_ext
  exact (cancel_epi (M.X ◁ π N P)).mp h

end Paper18.Category.RelativeTensor
