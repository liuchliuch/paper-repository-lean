import Paper18.Category.LinearTensorAdditive

/-! # Actual full faithfulness of finite additive-envelope lifts

Every morphism between the lifted finite biproducts is reconstructed from
its actual injection/projection matrix entries. Fullness and faithfulness
of the original functor therefore pass to its actual additive-envelope lift.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u v' u'
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]
  [HasFiniteBiproducts D] (F : C ⥤ D) [F.Additive]

/-- Matrix entries of the actual lifted morphism are the actual mapped entries. -/
@[reassoc (attr := simp)]
lemma linearMatLift_component {X Y : Mat_ C} (f : X ⟶ Y) (i : X.ι) (j : Y.ι) :
    biproduct.ι (fun i => F.obj (X.X i)) i ≫ (linearMatLift F).map f ≫
      biproduct.π (fun j => F.obj (Y.X j)) j = F.map (f i j) := by
  simp [linearMatLift]

instance linearMatLift_faithful [F.Faithful] : (linearMatLift F).Faithful where
  map_injective {X Y} f g h := by
    ext i j
    apply F.map_injective
    have he := congrArg (fun k => biproduct.ι (fun i => F.obj (X.X i)) i ≫ k ≫
      biproduct.π (fun j => F.obj (Y.X j)) j) h
    simpa using he

/-- An explicit actual preimage is the matrix of actual full-functor preimages
of the injection/projection components. -/
def linearMatLiftPreimage [F.Full] {X Y : Mat_ C}
    (f : (linearMatLift F).obj X ⟶ (linearMatLift F).obj Y) : X ⟶ Y := fun i j =>
  F.preimage (biproduct.ι (fun i => F.obj (X.X i)) i ≫ f ≫
    biproduct.π (fun j => F.obj (Y.X j)) j)

@[simp] lemma linearMatLift_map_preimage [F.Full] {X Y : Mat_ C}
    (f : (linearMatLift F).obj X ⟶ (linearMatLift F).obj Y) :
    (linearMatLift F).map (linearMatLiftPreimage F f) = f := by
  apply biproduct.hom_ext'
  intro i
  apply biproduct.hom_ext
  intro j
  simp [linearMatLiftPreimage]

instance linearMatLift_full [F.Full] : (linearMatLift F).Full where
  map_surjective f := ⟨linearMatLiftPreimage F f, linearMatLift_map_preimage F f⟩

/-- A lifted singleton is actually isomorphic to the original functor image. -/
def linearMatLiftSingletonIso (X : C) :
    (linearMatLift F).obj ((Mat_.embedding C).obj X) ≅ F.obj X :=
  biproductUniqueIso (fun _ : PUnit => F.obj X)

/-- The singleton identifications are natural actual isomorphisms. -/
def linearMatLiftEmbeddingIso : Mat_.embedding C ⋙ linearMatLift F ≅ F :=
  NatIso.ofComponents (linearMatLiftSingletonIso F) (fun {X Y} f => by
    apply biproduct.hom_ext'
    intro i
    cases i
    simp [linearMatLiftSingletonIso, linearMatLift, Mat_.embedding,
      biproduct.lift_desc, limitBiconeOfUnique])

end Paper18.Category
