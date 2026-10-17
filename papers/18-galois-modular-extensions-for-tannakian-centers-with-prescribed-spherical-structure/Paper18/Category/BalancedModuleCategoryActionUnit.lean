import Paper18.Category.BalancedModuleCategoryActionData

/-! # The derived right-monad-action map satisfies its actual unit law -/
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
lemma ambientRightFunctor_map_id_left (M : Mod_ D A) {X Y : D} (f : X ⟶ Y) :
    ambientRightFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) f) =
      RelativeTensor.ambientTensorMapRight M f := by
  apply Mod_.Hom.ext
  change (𝟙 M.X) ▷ X ≫ M.X ◁ f = M.X ◁ f
  rw [id_whiskerRight, id_comp]

omit [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] in
lemma rightRegularMultiply_unit :
    ambientLeftFunctor.map (CategoryTheory.Prod.mkHom η[B] (𝟙 (Mod_.regular (mop B)))) ≫
        rightRegularMultiply = (InternalModule.ambientTensorUnit (Mod_.regular (mop B))).hom := by
  apply Mod_.Hom.ext
  apply Quiver.Hom.unmop_inj
  simp only [Mod_.comp_hom', unmop_comp, ambientLeftFunctor_map_hom]
  change (η[B] ⊗ₘ 𝟙 B) ≫ μ[B] = (λ_ B).hom
  simpa only [tensorHom_id] using MonObj.one_mul B

variable {E : Type uE} [Category.{vE} E]
namespace BalancedFunctor
variable (F : BalancedFunctor (A := A) (B := B) E)

omit [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] in
lemma comparison_naturality_ambient (M : Mod_ D A) {X Y : D} (f : X ⟶ Y) (N : RightModules B) :
    F.toFunctor.map (CategoryTheory.Prod.mkHom (RelativeTensor.ambientTensorMapRight M f) (𝟙 N)) ≫
        F.comparison.hom.app ((M, Y), N) =
      F.comparison.hom.app ((M, X), N) ≫ F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M)
        (ambientLeftFunctor.map (CategoryTheory.Prod.mkHom f (𝟙 N)))) := by
  have h := F.comparison.hom.naturality (CategoryTheory.Prod.mkHom
    (CategoryTheory.Prod.mkHom (𝟙 M) f) (𝟙 N))
  change F.toFunctor.map (CategoryTheory.Prod.mkHom
      (ambientRightFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) f)) (𝟙 N)) ≫
      F.comparison.hom.app ((M, Y), N) =
    F.comparison.hom.app ((M, X), N) ≫ F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M)
      (ambientLeftFunctor.map (CategoryTheory.Prod.mkHom f (𝟙 N)))) at h
  rw [ambientRightFunctor_map_id_left] at h
  exact h

theorem rightActionMap_unit (M : Mod_ D A) :
    F.regularSlice.map ((outerMonad (A := A) (B := B)).η.app M) ≫ F.rightActionMap.app M =
      𝟙 (F.regularSlice.obj M) := by
  let R := Mod_.regular (mop B)
  let u := InternalModule.ambientTensorUnit M
  have hp : CategoryTheory.Prod.mkHom
      (u.inv ≫ RelativeTensor.ambientTensorMapRight M η[B]) (𝟙 R) =
      CategoryTheory.Prod.mkHom u.inv (𝟙 R) ≫
        CategoryTheory.Prod.mkHom (RelativeTensor.ambientTensorMapRight M η[B]) (𝟙 R) := by
    apply CategoryTheory.prod.hom_ext
    · rfl
    · exact (comp_id _).symm
  have hm :
      F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M)
        (ambientLeftFunctor.map (CategoryTheory.Prod.mkHom η[B] (𝟙 R)))) ≫
          F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) (rightRegularMultiply (B := B))) =
      F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) (InternalModule.ambientTensorUnit R).hom) := by
    rw [← F.toFunctor.map_comp]
    congr 1
    apply CategoryTheory.prod.hom_ext
    · exact comp_id _
    · exact rightRegularMultiply_unit
  change F.toFunctor.map (CategoryTheory.Prod.mkHom
      ((outerMonad (A := A) (B := B)).η.app M) (𝟙 R)) ≫
      (F.comparison.hom.app ((M, B), R) ≫
        F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) (rightRegularMultiply (B := B)))) = _
  rw [outerMonad_unit, hp, F.toFunctor.map_comp]
  have hn := F.comparison_naturality_ambient M η[B] R
  calc
    _ = F.toFunctor.map (CategoryTheory.Prod.mkHom u.inv (𝟙 R)) ≫
        F.comparison.hom.app ((M, 𝟙_ D), R) ≫
          (F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M)
            (ambientLeftFunctor.map (CategoryTheory.Prod.mkHom η[B] (𝟙 R)))) ≫
              F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) (rightRegularMultiply (B := B)))) := by
      simpa only [Category.assoc] using
        congrArg (fun f => F.toFunctor.map (CategoryTheory.Prod.mkHom u.inv (𝟙 R)) ≫
          f ≫ F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) (rightRegularMultiply (B := B)))) hn
    _ = F.toFunctor.map (CategoryTheory.Prod.mkHom u.inv (𝟙 R)) ≫
        F.comparison.hom.app ((M, 𝟙_ D), R) ≫
          F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) (InternalModule.ambientTensorUnit R).hom) := by rw [hm]
    _ = F.toFunctor.map (CategoryTheory.Prod.mkHom u.inv (𝟙 R)) ≫
        F.toFunctor.map (CategoryTheory.Prod.mkHom u.hom (𝟙 R)) :=
      congrArg (fun f => F.toFunctor.map (CategoryTheory.Prod.mkHom u.inv (𝟙 R)) ≫ f)
        (F.unit_condition M R)
    _ = _ := by
      rw [← F.toFunctor.map_comp]
      have hu : CategoryTheory.Prod.mkHom u.inv (𝟙 R) ≫
          CategoryTheory.Prod.mkHom u.hom (𝟙 R) = 𝟙 (M, R) := by
        apply CategoryTheory.prod.hom_ext
        · exact u.inv_hom_id
        · exact comp_id _
      rw [hu]
      exact F.toFunctor.map_id (M, R)

end BalancedFunctor
end Paper18.Category.BalancedModuleCategory
