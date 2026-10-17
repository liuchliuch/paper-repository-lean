import Paper18.Category.PicardGradedAssemblyTensor
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Linear.FunctorCategory

/-! # Separate additivity and complex linearity of actual convolution -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe w v u
namespace Paper18.Category.PicardGradedAssembly
variable {G : Type w} [Mul G] [Fintype G]
  {C : G → Type u} [∀ g, Category.{v} (C g)] [∀ g, Preadditive (C g)]
  [∀ g, HasFiniteBiproducts (C g)] (P : ComponentProducts (C := C))

omit [Fintype G] [∀ g, HasFiniteBiproducts (C g)] [∀ g, Preadditive (C g)] in
@[simp] lemma summand_map_right (X : Total C) {Y Y' : Total C} (f : Y ⟶ Y')
    (k : G) (p : Fiber k) :
    (summandFunctor P k p).map (show (X,Y) ⟶ (X,Y') from (𝟙 X, f)) =
      (transport C p.2).map (((P p.1.1 p.1.2).obj (X p.1.1)).map (f p.1.2)) := by
  simp [summandFunctor, Functor.uncurry]

omit [Fintype G] [∀ g, HasFiniteBiproducts (C g)] [∀ g, Preadditive (C g)] in
@[simp] lemma summand_map_left {X X' : Total C} (f : X ⟶ X') (Y : Total C)
    (k : G) (p : Fiber k) :
    (summandFunctor P k p).map (show (X,Y) ⟶ (X',Y) from (f, 𝟙 Y)) =
      (transport C p.2).map (((P p.1.1 p.1.2).map (f p.1.1)).app (Y p.1.2)) := by
  simp [summandFunctor, Functor.uncurry]

instance convolutionRightAdditive [∀ g h X, ((P g h).obj X).Additive] (X : Total C) :
    ((convolution P).obj X).Additive where
  map_add {Y Z} f t := by
    funext k
    change convolutionMap P (𝟙 X) (f+t) k = convolutionMap P (𝟙 X) f k + convolutionMap P (𝟙 X) t k
    apply biproduct.hom_ext
    intro p
    simp only [convolutionMap, biproduct.map_π, Preadditive.add_comp]
    simp [summandFunctor, Functor.uncurry]

instance convolutionLeftAdditive [∀ g h, (P g h).Additive] : (convolution P).Additive where
  map_add {X Z} f t := by
    apply NatTrans.ext
    funext Y k
    change convolutionMap P (f+t) (𝟙 Y) k = convolutionMap P f (𝟙 Y) k + convolutionMap P t (𝟙 Y) k
    apply biproduct.hom_ext
    intro p
    simp only [convolutionMap, biproduct.map_π, Preadditive.add_comp]
    simp [summandFunctor, Functor.uncurry]

variable [∀ g, Linear ℂ (C g)]
instance convolutionRightLinear [∀ g h X, ((P g h).obj X).Linear ℂ] (X : Total C) :
    ((convolution P).obj X).Linear ℂ where
  map_smul f r := by
    funext k
    change convolutionMap P (𝟙 X) (r • f) k = r • convolutionMap P (𝟙 X) f k
    apply biproduct.hom_ext
    intro p
    simp only [convolutionMap, biproduct.map_π, Linear.smul_comp]
    simp [summandFunctor, Functor.uncurry]

instance convolutionLeftLinear [∀ g h, (P g h).Linear ℂ] : (convolution P).Linear ℂ where
  map_smul f r := by
    apply NatTrans.ext
    funext Y k
    change convolutionMap P (r • f) (𝟙 Y) k = r • convolutionMap P f (𝟙 Y) k
    apply biproduct.hom_ext
    intro p
    simp only [convolutionMap, biproduct.map_π, Linear.smul_comp]
    simp [summandFunctor, Functor.uncurry]

end Paper18.Category.PicardGradedAssembly
