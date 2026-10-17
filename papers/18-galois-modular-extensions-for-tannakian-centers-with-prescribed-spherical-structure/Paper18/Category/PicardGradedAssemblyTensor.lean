import Paper18.Category.PicardGradedAssemblyBasic
import Mathlib.CategoryTheory.Functor.Currying

/-! # Actual finite convolution of heterogeneous component categories -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe w v u
namespace Paper18.Category.PicardGradedAssembly
variable {G : Type w} [Mul G] [Fintype G]
  {C : G → Type u} [∀ g, Category.{v} (C g)] [∀ g, Preadditive (C g)]
  [∀ g, HasFiniteBiproducts (C g)]

/-- The finite multiplication fiber over the actual output component. -/
abbrev Fiber (k : G) := {p : G × G // p.1 * p.2 = k}

/-- Genuine products on components, with no associativity requirement. -/
abbrev ComponentProducts := ∀ g h : G, C g ⥤ C h ⥤ C (g * h)
variable (P : ComponentProducts (C := C))

/-- A single summand of convolution, transported to the correct category. -/
def summandFunctor (k : G) (p : Fiber k) : Total C × Total C ⥤ C k :=
  ((Pi.eval C p.1.1).prod (Pi.eval C p.1.2)) ⋙
    Functor.uncurry.obj (P p.1.1 p.1.2) ⋙ transport C p.2

/-- The tensor object has an actual biproduct in each output component. -/
def convolutionObject (X Y : Total C) : Total C :=
  fun k => ⨁ fun p : Fiber k => (summandFunctor P k p).obj (X, Y)

/-- Actual morphisms are mapped diagonally on each finite fiber. -/
def convolutionMap {X Y X' Y' : Total C} (f : X ⟶ X') (t : Y ⟶ Y') :
    convolutionObject P X Y ⟶ convolutionObject P X' Y' :=
  fun k => biproduct.map (fun p : Fiber k => (summandFunctor P k p).map (f, t))

/-- The actual convolution bifunctor exists before a pentagon is imposed. -/
def convolutionFunctor : Total C × Total C ⥤ Total C where
  obj X := convolutionObject P X.1 X.2
  map f := convolutionMap P f.1 f.2
  map_id X := by
    funext k
    apply biproduct.hom_ext
    intro p
    simp only [convolutionMap, biproduct.map_π]
    change _ ≫ (summandFunctor P k p).map (𝟙 X) = (𝟙 (convolutionObject P X.1 X.2)) k ≫ _
    simp
  map_comp f t := by
    funext k
    apply biproduct.hom_ext
    intro p
    simp [convolutionMap, Category.assoc, ← Functor.map_comp]

/-- Its curried form is the actual tensor functor on families. -/
def convolution : Total C ⥤ Total C ⥤ Total C := Functor.curry.obj (convolutionFunctor P)

@[reassoc (attr := simp)]
lemma summand_ι_convolutionMap {X Y X' Y' : Total C} (f : X ⟶ X') (t : Y ⟶ Y')
    (k : G) (p : Fiber k) :
    biproduct.ι (fun p : Fiber k => (summandFunctor P k p).obj (X,Y)) p ≫
        convolutionMap P f t k =
      (summandFunctor P k p).map (f,t) ≫
        biproduct.ι (fun p : Fiber k => (summandFunctor P k p).obj (X',Y')) p :=
  by
    exact biproduct.ι_map (fun q : Fiber k => (summandFunctor P k q).map
      (show (X,Y) ⟶ (X',Y') from (f,t))) p

@[reassoc (attr := simp)]
lemma convolutionMap_summand_π {X Y X' Y' : Total C} (f : X ⟶ X') (t : Y ⟶ Y')
    (k : G) (p : Fiber k) :
    convolutionMap P f t k ≫
        biproduct.π (fun p : Fiber k => (summandFunctor P k p).obj (X',Y')) p =
      biproduct.π (fun p : Fiber k => (summandFunctor P k p).obj (X,Y)) p ≫
        (summandFunctor P k p).map (f,t) :=
  by
    exact biproduct.map_π (fun q : Fiber k => (summandFunctor P k q).map
      (show (X,Y) ⟶ (X',Y') from (f,t))) p

end Paper18.Category.PicardGradedAssembly
