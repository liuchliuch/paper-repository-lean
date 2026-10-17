import Paper18.Category.DeligneProductMapBasic

/-! # Actual tensor and braiding coherence of the componentwise functor -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.Monoidal
open scoped TensorProduct
universe v u v' u' v₁ u₁ v₂ u₂
namespace Paper18.Category.LinearTensor
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  {E : Type u₁} [Category.{v₁} E] [Preadditive E] [Linear ℂ E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalLinear ℂ E]
  {H : Type u₂} [Category.{v₂} H] [Preadditive H] [Linear ℂ H]
  [MonoidalCategory H] [MonoidalPreadditive H] [MonoidalLinear ℂ H]

lemma whiskerLeft_pair (X : LinearTensor C D) {Y Z : LinearTensor C D}
    (f : Y.left ⟶ Z.left) (g : Y.right ⟶ Z.right) :
    X ◁ (show Y ⟶ Z from f ⊗ₜ[ℂ] g) =
      (show X ⊗ Y ⟶ X ⊗ Z from (X.left ◁ f) ⊗ₜ[ℂ] (X.right ◁ g)) := by
  simpa only [MonoidalCategory.id_tensorHom] using
    tensorLinear_tmul X Y X Z (𝟙 X.left) (𝟙 X.right) f g

lemma whiskerRight_pair {X Y : LinearTensor C D}
    (f : X.left ⟶ Y.left) (g : X.right ⟶ Y.right) (Z : LinearTensor C D) :
    (show X ⟶ Y from f ⊗ₜ[ℂ] g) ▷ Z =
      (show X ⊗ Z ⟶ Y ⊗ Z from (f ▷ Z.left) ⊗ₜ[ℂ] (g ▷ Z.right)) := by
  simpa only [MonoidalCategory.tensorHom_id] using
    tensorLinear_tmul X Z Y Z f g (𝟙 Z.left) (𝟙 Z.right)

lemma comp_pair {X Y Z : LinearTensor C D}
    (f : X.left ⟶ Y.left) (g : X.right ⟶ Y.right)
    (h : Y.left ⟶ Z.left) (k : Y.right ⟶ Z.right) :
    (show X ⟶ Y from f ⊗ₜ[ℂ] g) ≫ (show Y ⟶ Z from h ⊗ₜ[ℂ] k) =
      (show X ⟶ Z from (f ≫ h) ⊗ₜ[ℂ] (g ≫ k)) := compLinear_tmul X Y Z f g h k

lemma associator_pair_hom (X Y Z : LinearTensor C D) :
    (α_ X Y Z).hom = (α_ X.left Y.left Z.left).hom ⊗ₜ[ℂ]
      (α_ X.right Y.right Z.right).hom := rfl

lemma leftUnitor_pair_hom (X : LinearTensor C D) :
    (λ_ X).hom = (λ_ X.left).hom ⊗ₜ[ℂ] (λ_ X.right).hom := rfl

lemma rightUnitor_pair_hom (X : LinearTensor C D) :
    (ρ_ X).hom = (ρ_ X.left).hom ⊗ₜ[ℂ] (ρ_ X.right).hom := rfl

variable (F : C ⥤ E) [F.Additive] [F.Linear ℂ] [F.Monoidal]
  (G : D ⥤ H) [G.Additive] [G.Linear ℂ] [G.Monoidal]

def mapTensorIso (X Y : LinearTensor C D) :
    (map F G).obj X ⊗ (map F G).obj Y ≅ (map F G).obj (X ⊗ Y) :=
  isoOfPair (μIso F X.left Y.left) (μIso G X.right Y.right)

lemma mapTensorIso_hom (X Y : LinearTensor C D) :
    (mapTensorIso F G X Y).hom = μ F X.left Y.left ⊗ₜ[ℂ] μ G X.right Y.right := rfl

lemma mapTensorIso_natural_left {X Y : LinearTensor C D} (f : X ⟶ Y)
    (Z : LinearTensor C D) :
    (map F G).map f ▷ (map F G).obj Z ≫ (mapTensorIso F G Y Z).hom =
      (mapTensorIso F G X Z).hom ≫ (map F G).map (f ▷ Z) := by
  induction f using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [mapTensorIso_hom, map_tmul, whiskerRight_pair]
    dsimp only [map]
    rw [whiskerRight_pair (X := ⟨F.obj X.left,G.obj X.right⟩)
      (Y := ⟨F.obj Y.left,G.obj Y.right⟩) (F.map a) (G.map b)
      (⟨F.obj Z.left,G.obj Z.right⟩ : LinearTensor E H)]
    change compLinear
      (⟨F.obj X.left ⊗ F.obj Z.left,G.obj X.right ⊗ G.obj Z.right⟩ : LinearTensor E H)
      ⟨F.obj Y.left ⊗ F.obj Z.left,G.obj Y.right ⊗ G.obj Z.right⟩
      ⟨F.obj (Y.left ⊗ Z.left),G.obj (Y.right ⊗ Z.right)⟩ _ _ =
      compLinear
        (⟨F.obj X.left ⊗ F.obj Z.left,G.obj X.right ⊗ G.obj Z.right⟩ : LinearTensor E H)
        ⟨F.obj (X.left ⊗ Z.left),G.obj (X.right ⊗ Z.right)⟩
        ⟨F.obj (Y.left ⊗ Z.left),G.obj (Y.right ⊗ Z.right)⟩ _ _
    rw [compLinear_tmul, compLinear_tmul]
    exact congrArg₂ (TensorProduct.tmul ℂ) (μ_natural_left F a Z.left)
      (μ_natural_left G b Z.right)
  | add a b ha hb =>
    have hm : (map F G).map (a + b) = (map F G).map a + (map F G).map b :=
      (mapHom F G X Y).map_add a b
    rw [hm, MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp,
      MonoidalPreadditive.add_whiskerRight]
    have hn : (map F G).map (a ▷ Z + b ▷ Z) =
        (map F G).map (a ▷ Z) + (map F G).map (b ▷ Z) :=
      (mapHom F G (X ⊗ Z) (Y ⊗ Z)).map_add _ _
    rw [hn, Preadditive.comp_add]
    exact congrArg₂ (· + ·) ha hb

lemma mapTensorIso_natural_right (X : LinearTensor C D) {Y Z : LinearTensor C D}
    (f : Y ⟶ Z) :
    (map F G).obj X ◁ (map F G).map f ≫ (mapTensorIso F G X Z).hom =
      (mapTensorIso F G X Y).hom ≫ (map F G).map (X ◁ f) := by
  induction f using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [mapTensorIso_hom, map_tmul, whiskerLeft_pair]
    dsimp only [map]
    rw [whiskerLeft_pair (⟨F.obj X.left,G.obj X.right⟩ : LinearTensor E H)
      (Y := ⟨F.obj Y.left,G.obj Y.right⟩) (Z := ⟨F.obj Z.left,G.obj Z.right⟩)
      (F.map a) (G.map b)]
    change compLinear
      (⟨F.obj X.left ⊗ F.obj Y.left,G.obj X.right ⊗ G.obj Y.right⟩ : LinearTensor E H)
      ⟨F.obj X.left ⊗ F.obj Z.left,G.obj X.right ⊗ G.obj Z.right⟩
      ⟨F.obj (X.left ⊗ Z.left),G.obj (X.right ⊗ Z.right)⟩ _ _ =
      compLinear
        (⟨F.obj X.left ⊗ F.obj Y.left,G.obj X.right ⊗ G.obj Y.right⟩ : LinearTensor E H)
        ⟨F.obj (X.left ⊗ Y.left),G.obj (X.right ⊗ Y.right)⟩
        ⟨F.obj (X.left ⊗ Z.left),G.obj (X.right ⊗ Z.right)⟩ _ _
    rw [compLinear_tmul, compLinear_tmul]
    exact congrArg₂ (TensorProduct.tmul ℂ) (μ_natural_right F X.left a)
      (μ_natural_right G X.right b)
  | add a b ha hb =>
    have hm : (map F G).map (a + b) = (map F G).map a + (map F G).map b :=
      (mapHom F G Y Z).map_add a b
    rw [hm, MonoidalPreadditive.whiskerLeft_add, Preadditive.add_comp,
      MonoidalPreadditive.whiskerLeft_add]
    have hn : (map F G).map (X ◁ a + X ◁ b) =
        (map F G).map (X ◁ a) + (map F G).map (X ◁ b) :=
      (mapHom F G (X ⊗ Y) (X ⊗ Z)).map_add _ _
    rw [hn, Preadditive.comp_add]
    exact congrArg₂ (· + ·) ha hb

def mapCoreMonoidal : (map F G).CoreMonoidal where
  εIso := isoOfPair (εIso F) (εIso G)
  μIso := mapTensorIso F G
  μIso_hom_natural_left := fun f Z => mapTensorIso_natural_left F G f Z
  μIso_hom_natural_right := fun X f => mapTensorIso_natural_right F G X f
  associativity X Y Z := by
    have hm : (map F G).map (α_ X Y Z).hom =
        F.map (α_ X.left Y.left Z.left).hom ⊗ₜ[ℂ]
          G.map (α_ X.right Y.right Z.right).hom := rfl
    rw [hm]
    simp only [mapTensorIso_hom, associator_pair_hom]
    dsimp only [map, tensorObject]
    rw [whiskerRight_pair
      (X := (⟨F.obj X.left ⊗ F.obj Y.left,G.obj X.right ⊗ G.obj Y.right⟩ : LinearTensor E H))
      (Y := ⟨F.obj (X.left ⊗ Y.left),G.obj (X.right ⊗ Y.right)⟩)
      (μ F X.left Y.left) (μ G X.right Y.right) ⟨F.obj Z.left,G.obj Z.right⟩]
    rw [whiskerLeft_pair (⟨F.obj X.left,G.obj X.right⟩ : LinearTensor E H)
      (Y := ⟨F.obj Y.left ⊗ F.obj Z.left,G.obj Y.right ⊗ G.obj Z.right⟩)
      (Z := ⟨F.obj (Y.left ⊗ Z.left),G.obj (Y.right ⊗ Z.right)⟩)
      (μ F Y.left Z.left) (μ G Y.right Z.right)]
    simp only [comp_def, compLinear_tmul]
    change
      (μ F X.left Y.left ▷ F.obj Z.left ≫ μ F (X.left ⊗ Y.left) Z.left ≫
        F.map (α_ X.left Y.left Z.left).hom) ⊗ₜ[ℂ]
      (μ G X.right Y.right ▷ G.obj Z.right ≫ μ G (X.right ⊗ Y.right) Z.right ≫
        G.map (α_ X.right Y.right Z.right).hom) =
      ((α_ (F.obj X.left) (F.obj Y.left) (F.obj Z.left)).hom ≫
        F.obj X.left ◁ μ F Y.left Z.left ≫ μ F X.left (Y.left ⊗ Z.left)) ⊗ₜ[ℂ]
      ((α_ (G.obj X.right) (G.obj Y.right) (G.obj Z.right)).hom ≫
        G.obj X.right ◁ μ G Y.right Z.right ≫ μ G X.right (Y.right ⊗ Z.right))
    exact congrArg₂ (TensorProduct.tmul ℂ) (associativity F X.left Y.left Z.left)
      (associativity G X.right Y.right Z.right)
  left_unitality X := by
    have hm : (map F G).map (λ_ X).hom =
        F.map (λ_ X.left).hom ⊗ₜ[ℂ] G.map (λ_ X.right).hom := rfl
    rw [hm]
    simp only [mapTensorIso_hom, leftUnitor_pair_hom, isoOfPair, εIso_hom]
    dsimp only [map, tensorObject]
    rw [whiskerRight_pair (X := (⟨𝟙_ E,𝟙_ H⟩ : LinearTensor E H))
      (Y := ⟨F.obj (𝟙_ C),G.obj (𝟙_ D)⟩) (ε F) (ε G) ⟨F.obj X.left,G.obj X.right⟩]
    simp only [comp_def, compLinear_tmul]
    change (λ_ (F.obj X.left)).hom ⊗ₜ[ℂ] (λ_ (G.obj X.right)).hom =
      (ε F ▷ F.obj X.left ≫ μ F (𝟙_ C) X.left ≫ F.map (λ_ X.left).hom) ⊗ₜ[ℂ]
      (ε G ▷ G.obj X.right ≫ μ G (𝟙_ D) X.right ≫ G.map (λ_ X.right).hom)
    exact congrArg₂ (TensorProduct.tmul ℂ) (left_unitality F X.left)
      (left_unitality G X.right)
  right_unitality X := by
    have hm : (map F G).map (ρ_ X).hom =
        F.map (ρ_ X.left).hom ⊗ₜ[ℂ] G.map (ρ_ X.right).hom := rfl
    rw [hm]
    simp only [mapTensorIso_hom, rightUnitor_pair_hom, isoOfPair, εIso_hom]
    dsimp only [map, tensorObject]
    rw [whiskerLeft_pair (⟨F.obj X.left,G.obj X.right⟩ : LinearTensor E H)
      (Y := ⟨𝟙_ E,𝟙_ H⟩) (Z := ⟨F.obj (𝟙_ C),G.obj (𝟙_ D)⟩) (ε F) (ε G)]
    simp only [comp_def, compLinear_tmul]
    change (ρ_ (F.obj X.left)).hom ⊗ₜ[ℂ] (ρ_ (G.obj X.right)).hom =
      (F.obj X.left ◁ ε F ≫ μ F X.left (𝟙_ C) ≫ F.map (ρ_ X.left).hom) ⊗ₜ[ℂ]
      (G.obj X.right ◁ ε G ≫ μ G X.right (𝟙_ D) ≫ G.map (ρ_ X.right).hom)
    exact congrArg₂ (TensorProduct.tmul ℂ) (right_unitality F X.left)
      (right_unitality G X.right)

instance map_monoidal : (map F G).Monoidal := (mapCoreMonoidal F G).toMonoidal

omit [F.Monoidal] [G.Monoidal] in
instance map_braided [BraidedCategory C] [BraidedCategory D]
    [BraidedCategory E] [BraidedCategory H] [F.Braided] [G.Braided] :
    (map F G).Braided := by
  letI : F.Monoidal := (inferInstance : F.Braided).toMonoidal
  letI : G.Monoidal := (inferInstance : G.Braided).toMonoidal
  exact {
    braided X Y := by
      change (μ F X.left Y.left ≫ F.map (β_ X.left Y.left).hom) ⊗ₜ[ℂ]
          (μ G X.right Y.right ≫ G.map (β_ X.right Y.right).hom) =
        ((β_ (F.obj X.left) (F.obj Y.left)).hom ≫ μ F Y.left X.left) ⊗ₜ[ℂ]
          ((β_ (G.obj X.right) (G.obj Y.right)).hom ≫ μ G Y.right X.right)
      exact congrArg₂ (TensorProduct.tmul ℂ) (Functor.LaxBraided.braided (F := F) _ _)
        (Functor.LaxBraided.braided (F := G) _ _) }

end Paper18.Category.LinearTensor
