import Paper18.Category.BalancedModuleCategoryExternalPresentation

/-! # The constructed extension has an actual natural external comparison -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u vE uE
namespace Paper18.Category.BalancedModuleCategory
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  {A B : D} [MonObj A] [MonObj B]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

omit [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] in
lemma external_map_underlying {X Y : Mod_ D A × RightModules B} (f : X ⟶ Y) :
    (external.map f).hom =
      ambientRightFunctor.map (CategoryTheory.Prod.mkHom f.1 f.2.hom.unmop) := by
  apply Mod_.Hom.ext
  rw [ambientRightFunctor_map_hom]
  rfl

omit [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] in
lemma rightProjection_naturality {N P : RightModules B} (f : N ⟶ P) :
    ambientLeftFunctor.map (CategoryTheory.Prod.mkHom f.hom.unmop (𝟙 (Mod_.regular (mop B)))) ≫
      rightProjection P = rightProjection N ≫ f := by
  apply Mod_.Hom.ext
  apply Quiver.Hom.unmop_inj
  simp only [Mod_.comp_hom', unmop_comp, ambientLeftFunctor_map_hom]
  change (f.hom.unmop ⊗ₘ 𝟙 B) ≫ rightAction P = rightAction N ≫ f.hom.unmop
  rw [tensorHom_id]
  exact (congrArg Quiver.Hom.unmop f.isMod_Hom.smul_hom).symm

variable {E : Type uE} [Category.{vE} E]
namespace BalancedFunctor
variable (F : BalancedFunctor (A := A) (B := B) E)

/-- The actual coequalizer projection, expressed only using balancing
and the given right module's actual action. -/
def externalPresentationMap (M : Mod_ D A) (N : RightModules B) :
    F.regularSlice.obj (toAlgebraObj (externalObj M N)).A ⟶ F.toFunctor.obj (M, N) :=
  (F.externalNodeIso M N).hom ≫
    F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) (rightProjection N))

lemma externalPresentationMap_naturality {X Y : Mod_ D A × RightModules B} (f : X ⟶ Y) :
    F.regularSlice.map (external.map f).hom ≫ F.externalPresentationMap Y.1 Y.2 =
      F.externalPresentationMap X.1 X.2 ≫ F.toFunctor.map f := by
  have hn := F.comparison.hom.naturality (CategoryTheory.Prod.mkHom
    (CategoryTheory.Prod.mkHom f.1 f.2.hom.unmop) (𝟙 (Mod_.regular (mop B))))
  change F.toFunctor.map (CategoryTheory.Prod.mkHom
      (ambientRightFunctor.map (CategoryTheory.Prod.mkHom f.1 f.2.hom.unmop))
        (𝟙 (Mod_.regular (mop B)))) ≫ (F.externalNodeIso Y.1 Y.2).hom =
    (F.externalNodeIso X.1 X.2).hom ≫ F.toFunctor.map (CategoryTheory.Prod.mkHom f.1
      (ambientLeftFunctor.map (CategoryTheory.Prod.mkHom f.2.hom.unmop
        (𝟙 (Mod_.regular (mop B)))))) at hn
  have hm :
      F.toFunctor.map (CategoryTheory.Prod.mkHom f.1
        (ambientLeftFunctor.map (CategoryTheory.Prod.mkHom f.2.hom.unmop
          (𝟙 (Mod_.regular (mop B)))))) ≫
        F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 Y.1) (rightProjection Y.2)) =
      F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 X.1) (rightProjection X.2)) ≫ F.toFunctor.map f := by
    rw [← F.toFunctor.map_comp, ← F.toFunctor.map_comp]
    congr 1
    apply CategoryTheory.prod.hom_ext
    · change f.1 ≫ 𝟙 _ = 𝟙 _ ≫ f.1
      rw [Category.comp_id, Category.id_comp]
    · exact rightProjection_naturality f.2
  rw [external_map_underlying]
  exact vertical_square hn hm

variable [HasCoequalizers E]

/-- The actual external value is the actual coequalizer used to define
the extension. The isomorphism follows from the proved split diagram. -/
def extensionExternalIso (SB : SeparableAlgebra B) (M : Mod_ D A) (N : RightModules B) :
    F.extension.obj (externalObj M N) ≅ F.toFunctor.obj (M, N) :=
  (coequalizerIsCoequalizer
    (F.rightActionMap.app (toAlgebraObj (externalObj M N)).A)
    (F.regularSlice.map (toAlgebraObj (externalObj M N)).a)).coconePointUniqueUpToIso
      (F.externalSplitCoequalizer SB M N).isCoequalizer

@[reassoc (attr := simp)]
lemma extensionExternalIso_π (SB : SeparableAlgebra B) (M : Mod_ D A) (N : RightModules B) :
    F.rightMonadModule.descentπ (toAlgebraObj (externalObj M N)) ≫
        (F.extensionExternalIso SB M N).hom = F.externalPresentationMap M N := by
  exact (coequalizerIsCoequalizer
    (F.rightActionMap.app (toAlgebraObj (externalObj M N)).A)
    (F.regularSlice.map (toAlgebraObj (externalObj M N)).a)).comp_coconePointUniqueUpToIso_hom
      (F.externalSplitCoequalizer SB M N).isCoequalizer WalkingParallelPair.one

/-- Naturality holds on every actual pair of module maps. -/
def extensionExternalNatIso (SB : SeparableAlgebra B) : external ⋙ F.extension ≅ F.toFunctor :=
  NatIso.ofComponents (fun X => F.extensionExternalIso SB X.1 X.2) (by
    intro X Y f
    apply (cancel_epi (F.rightMonadModule.descentπ (toAlgebraObj (externalObj X.1 X.2)))).mp
    change F.rightMonadModule.descentπ (toAlgebraObj (externalObj X.1 X.2)) ≫
        F.rightMonadModule.descentMap (toAlgebras.map (external.map f)) ≫
          (F.extensionExternalIso SB Y.1 Y.2).hom =
      F.rightMonadModule.descentπ (toAlgebraObj (externalObj X.1 X.2)) ≫
        (F.extensionExternalIso SB X.1 X.2).hom ≫ F.toFunctor.map f
    rw [RightMonadModule.descentπ_map_assoc, extensionExternalIso_π_assoc]
    change F.regularSlice.map (external.map f).hom ≫
        (F.rightMonadModule.descentπ (toAlgebraObj (externalObj Y.1 Y.2)) ≫
          (F.extensionExternalIso SB Y.1 Y.2).hom) = _
    rw [extensionExternalIso_π]
    exact F.externalPresentationMap_naturality f)

end BalancedFunctor
end Paper18.Category.BalancedModuleCategory
