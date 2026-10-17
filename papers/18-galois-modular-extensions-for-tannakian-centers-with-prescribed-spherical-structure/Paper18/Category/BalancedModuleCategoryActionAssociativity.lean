import Paper18.Category.BalancedModuleCategoryActionUnit

/-! # Balancing derives the right monad action's associativity -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u vE uE
namespace Paper18.Category.BalancedModuleCategory
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  {A B : D} [MonObj A] [MonObj B]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

omit [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] in
lemma rightRegularMultiply_assoc :
    (rightAmbientAssoc (Mod_.regular (mop B)) B B).hom ≫
        ambientLeftFunctor.map (CategoryTheory.Prod.mkHom μ[B] (𝟙 (Mod_.regular (mop B)))) ≫
          rightRegularMultiply =
      ambientLeftFunctor.map (CategoryTheory.Prod.mkHom (𝟙 B) (rightRegularMultiply (B := B))) ≫
        rightRegularMultiply := by
  apply Mod_.Hom.ext
  apply Quiver.Hom.unmop_inj
  simp only [Mod_.comp_hom', unmop_comp, ambientLeftFunctor_map_hom]
  change (α_ B B B).inv ≫ (μ[B] ⊗ₘ 𝟙 B) ≫ μ[B] = (𝟙 B ⊗ₘ μ[B]) ≫ μ[B]
  simpa only [tensorHom_id, id_tensorHom, Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun f => (α_ B B B).inv ≫ f) (MonObj.mul_assoc B)

variable {E : Type uE} [Category.{vE} E]
namespace BalancedFunctor
variable (F : BalancedFunctor (A := A) (B := B) E)

omit [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] in
lemma comparison_naturality_right (M : Mod_ D A) (X : D) {N P : RightModules B} (f : N ⟶ P) :
    F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 (RelativeTensor.ambientTensor M X)) f) ≫
        F.comparison.hom.app ((M, X), P) =
      F.comparison.hom.app ((M, X), N) ≫ F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M)
        (ambientLeftFunctor.map (CategoryTheory.Prod.mkHom (𝟙 X) f))) := by
  have h := F.comparison.hom.naturality (CategoryTheory.Prod.mkHom
    (CategoryTheory.Prod.mkHom (𝟙 M) (𝟙 X)) f)
  change F.toFunctor.map (CategoryTheory.Prod.mkHom
      (ambientRightFunctor.map (𝟙 (M, X))) f) ≫ F.comparison.hom.app ((M, X), P) =
    F.comparison.hom.app ((M, X), N) ≫ F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M)
      (ambientLeftFunctor.map (CategoryTheory.Prod.mkHom (𝟙 X) f))) at h
  have hi : ambientRightFunctor.map (𝟙 (M, X)) = 𝟙 (RelativeTensor.ambientTensor M X) :=
    ambientRightFunctor.map_id (M, X)
  rw [hi] at h
  exact h

theorem rightActionMap_assoc (M : Mod_ D A) :
    F.regularSlice.map ((outerMonad (A := A) (B := B)).μ.app M) ≫ F.rightActionMap.app M =
      F.rightActionMap.app ((outerMonad (A := A) (B := B)).obj M) ≫ F.rightActionMap.app M := by
  let R := Mod_.regular (mop B)
  let m := rightRegularMultiply (B := B)
  let a := (RelativeTensor.ambientTensorAssoc M B B).hom
  have hp : CategoryTheory.Prod.mkHom
      (a ≫ RelativeTensor.ambientTensorMapRight M μ[B]) (𝟙 R) =
      CategoryTheory.Prod.mkHom a (𝟙 R) ≫
        CategoryTheory.Prod.mkHom (RelativeTensor.ambientTensorMapRight M μ[B]) (𝟙 R) := by
    apply CategoryTheory.prod.hom_ext
    · rfl
    · exact (comp_id _).symm
  have hm :
      F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) (rightAmbientAssoc R B B).hom) ≫
        F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M)
          (ambientLeftFunctor.map (CategoryTheory.Prod.mkHom μ[B] (𝟙 R)))) ≫
          F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) m) =
      F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M)
        (ambientLeftFunctor.map (CategoryTheory.Prod.mkHom (𝟙 B) m))) ≫
          F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) m) := by
    simp only [← F.toFunctor.map_comp]
    congr 1
    apply CategoryTheory.prod.hom_ext
    · change 𝟙 M ≫ 𝟙 M ≫ 𝟙 M = 𝟙 M ≫ 𝟙 M
      simp only [Category.id_comp]
    · exact rightRegularMultiply_assoc
  change F.toFunctor.map (CategoryTheory.Prod.mkHom
      ((outerMonad (A := A) (B := B)).μ.app M) (𝟙 R)) ≫
      (F.comparison.hom.app ((M, B), R) ≫ F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) m)) =
    (F.comparison.hom.app ((RelativeTensor.ambientTensor M B, B), R) ≫
      F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 (RelativeTensor.ambientTensor M B)) m)) ≫
        (F.comparison.hom.app ((M, B), R) ≫ F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) m))
  rw [outerMonad_multiplication, hp, F.toFunctor.map_comp]
  have hn := F.comparison_naturality_ambient M μ[B] R
  have hr := F.comparison_naturality_right M B m
  calc
    _ = F.toFunctor.map (CategoryTheory.Prod.mkHom a (𝟙 R)) ≫
        F.comparison.hom.app ((M, B ⊗ B), R) ≫
          (F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M)
            (ambientLeftFunctor.map (CategoryTheory.Prod.mkHom μ[B] (𝟙 R)))) ≫
              F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) m)) := by
      simpa only [Category.assoc] using congrArg
        (fun f => F.toFunctor.map (CategoryTheory.Prod.mkHom a (𝟙 R)) ≫ f ≫
          F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) m)) hn
    _ = F.comparison.hom.app ((RelativeTensor.ambientTensor M B, B), R) ≫
        F.comparison.hom.app ((M, B), rightAmbientTensor R B) ≫
          (F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) (rightAmbientAssoc R B B).hom) ≫
            F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M)
              (ambientLeftFunctor.map (CategoryTheory.Prod.mkHom μ[B] (𝟙 R)))) ≫
                F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) m)) := by
      simpa only [Category.assoc] using congrArg
        (fun f => f ≫ F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M)
          (ambientLeftFunctor.map (CategoryTheory.Prod.mkHom μ[B] (𝟙 R)))) ≫
            F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) m)) (F.assoc_condition M B B R)
    _ = F.comparison.hom.app ((RelativeTensor.ambientTensor M B, B), R) ≫
        F.comparison.hom.app ((M, B), rightAmbientTensor R B) ≫
          (F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M)
            (ambientLeftFunctor.map (CategoryTheory.Prod.mkHom (𝟙 B) m))) ≫
              F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) m)) := by rw [hm]
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun f => F.comparison.hom.app ((RelativeTensor.ambientTensor M B, B), R) ≫ f ≫
          F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) m)) hr.symm

end BalancedFunctor
end Paper18.Category.BalancedModuleCategory
