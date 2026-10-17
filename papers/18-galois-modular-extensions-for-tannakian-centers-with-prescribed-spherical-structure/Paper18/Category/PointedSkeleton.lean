import Paper18.Category.PointedSimple
import Paper18.Category.PointedBiproducts
import Paper18.Category.Semisimple

/-! # Actual finite simple decompositions of finite graded vector spaces -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
namespace Paper18.Category.PointedVec
variable {A : Type} [Fintype A] [AddGroup A]

/-- A homogeneous coordinate map onto a concentrated line. -/
def toSimple (a : A) (X : PointedVec A) (l : X a →ₗ[ℂ] ℂ) : X ⟶ simpleObject A a := fun b =>
  if hb : b = a then
    eqToHom (congrArg X hb) ≫ FGModuleCat.ofHom l ≫
      (GradedObject.singleObjApplyIsoOfEq a (FGModuleCat.of ℂ ℂ) b hb).inv
  else 0

omit [Fintype A] [AddGroup A] in
lemma fromSimple_at (a : A) (X : PointedVec A) (v : X a) :
    fromSimple a X v a = (simpleFiberIso A a).hom ≫
      FGModuleCat.ofHom (LinearMap.toSpanSingleton ℂ (X a) v) := by
  simp [fromSimple, simpleFiberIso]

omit [Fintype A] [AddGroup A] in
lemma toSimple_at (a : A) (X : PointedVec A) (l : X a →ₗ[ℂ] ℂ) :
    toSimple a X l a = FGModuleCat.ofHom l ≫ (simpleFiberIso A a).inv := by
  simp [toSimple, simpleFiberIso]

/-- The finite set of homogeneous basis vectors of an actual object. -/
abbrev BasisIndex (X : PointedVec A) := Σ a : A, Fin (Module.finrank ℂ (X a))

/-- A chosen basis for each homogeneous component. -/
abbrev fiberBasis (X : PointedVec A) (a : A) := Module.finBasis ℂ (X a)

/-- Actual inclusion of a homogeneous basis line. -/
def basisInclusion (X : PointedVec A) (j : BasisIndex X) : simpleObject A j.1 ⟶ X :=
  fromSimple j.1 X (fiberBasis X j.1 j.2)

/-- Actual projection onto a homogeneous basis line. -/
def basisProjection (X : PointedVec A) (j : BasisIndex X) : X ⟶ simpleObject A j.1 :=
  toSimple j.1 X ((fiberBasis X j.1).coord j.2)

lemma basisInclusion_projection_same (X : PointedVec A) (a : A)
    (i j : Fin (Module.finrank ℂ (X a))) :
    basisInclusion X ⟨a, i⟩ ≫ basisProjection X ⟨a, j⟩ =
      if h : i = j then eqToHom (congrArg (fun _ : Fin (Module.finrank ℂ (X a)) =>
        simpleObject A a) h) else 0 := by
  have hmid : FGModuleCat.ofHom (LinearMap.toSpanSingleton ℂ (X a) (fiberBasis X a i)) ≫
      FGModuleCat.ofHom ((fiberBasis X a).coord j) =
      if i = j then 𝟙 (FGModuleCat.of ℂ ℂ) else 0 := by
    apply FGModuleCat.hom_ext
    ext
    split_ifs with hij
    · subst j
      simp [FGModuleCat.hom_comp]
    · simp [FGModuleCat.hom_comp, Ne.symm hij]
  funext b
  by_cases hb : b = a
  · subst b
    change fromSimple a X (fiberBasis X a i) a ≫
      toSimple a X ((fiberBasis X a).coord j) a = _
    rw [fromSimple_at, toSimple_at]
    simp only [Category.assoc, ← Category.assoc (FGModuleCat.ofHom _) (FGModuleCat.ofHom _), hmid]
    split_ifs with hij
    · subst j
      simp
    · change (simpleFiberIso A a).hom ≫ 0 ≫ (simpleFiberIso A a).inv = 0
      simp
  · exact (simpleFiber_isZero A a b hb).eq_of_src _ _

/-- Matrix-unit equations for homogeneous basis inclusions and projections. -/
lemma basisInclusion_projection (X : PointedVec A) (i j : BasisIndex X) :
    basisInclusion X i ≫ basisProjection X j =
      if h : i = j then eqToHom (congrArg (fun k : BasisIndex X => simpleObject A k.1) h)
        else 0 := by
  obtain ⟨a, i⟩ := i
  obtain ⟨b, j⟩ := j
  by_cases hab : a = b
  · subst b
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using
      basisInclusion_projection_same X a i j
  · have hne : (⟨a, i⟩ : BasisIndex X) ≠ ⟨b, j⟩ := by
      intro h
      exact hab (congrArg Sigma.fst h)
    rw [dif_neg hne]
    funext c
    by_cases hca : c = a
    · subst c
      exact (simpleFiber_isZero A b a hab).eq_of_tgt _ _
    · exact (simpleFiber_isZero A a c hca).eq_of_src _ _

/-- The homogeneous basis lines form an actual biproduct bicone with
vertex the original graded vector space. -/
def basisBicone (X : PointedVec A) :
    Bicone (fun i : BasisIndex X => simpleObject A i.1) where
  pt := X
  π := basisProjection X
  ι := basisInclusion X
  ι_π i j := by
    by_cases hij : i = j
    · subst j
      simp [basisInclusion_projection]
    · simp [basisInclusion_projection, hij]

omit [Fintype A] [AddGroup A] in
lemma fiber_basis_resolution (X : PointedVec A) (a : A) :
    (∑ i : Fin (Module.finrank ℂ (X a)),
      (basisProjection X ⟨a, i⟩) a ≫ (basisInclusion X ⟨a, i⟩) a) = 𝟙 (X a) := by
  simp only [basisProjection, basisInclusion, toSimple_at, fromSimple_at,
    Category.assoc, Iso.inv_hom_id_assoc]
  apply FGModuleCat.hom_ext
  ext v
  let U : (X a ⟶ X a) →+ (X a →ₗ[ℂ] X a) :=
    { toFun := fun f => f.hom
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change (U (∑ i : Fin (Module.finrank ℂ (X a)),
    FGModuleCat.ofHom ((fiberBasis X a).coord i) ≫
      FGModuleCat.ofHom (LinearMap.toSpanSingleton ℂ (X a) (fiberBasis X a i)))) v = v
  rw [map_sum]
  simp only [LinearMap.sum_apply]
  change ∑ i : Fin (Module.finrank ℂ (X a)),
    ((fiberBasis X a).repr v) i • (fiberBasis X a i) = v
  exact (fiberBasis X a).sum_repr v

omit [AddGroup A] in
/-- The sum of the actual homogeneous matrix idempotents is the identity. -/
lemma basis_resolution (X : PointedVec A) :
    (∑ i : BasisIndex X, basisProjection X i ≫ basisInclusion X i) = 𝟙 X := by
  funext b
  rw [Finset.sum_apply]
  simp only [comp_apply, id_apply]
  rw [Fintype.sum_sigma]
  have hdeg (a : A) (hab : a ≠ b) :
      (∑ i : Fin (Module.finrank ℂ (X a)),
        (basisProjection X ⟨a, i⟩) b ≫ (basisInclusion X ⟨a, i⟩) b) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [basisProjection, basisInclusion, toSimple, fromSimple, Ne.symm hab]
  rw [Finset.sum_eq_single b]
  · exact fiber_basis_resolution X b
  · intro a _ hab
    exact hdeg a hab
  · simp

/-- The homogeneous basis bicone satisfies the actual limit and colimit
universal properties. -/
def basisBiconeIsBilimit (X : PointedVec A) : (basisBicone X).IsBilimit :=
  isBilimitOfTotal (basisBicone X) (basis_resolution X)

/-- Actual finite decomposition into homogeneous one-dimensional objects. -/
def basisDecomposition (X : PointedVec A) :
    X ≅ ⨁ fun i : BasisIndex X => simpleObject A i.1 :=
  biproduct.uniqueUpToIso _ (basisBiconeIsBilimit X)

/-- Reindex the actual homogeneous decomposition by a finite ordinal. -/
def finiteBasisDecomposition (X : PointedVec A) :
    X ≅ ⨁ fun i : Fin (Fintype.card (BasisIndex X)) =>
      simpleObject A (((Fintype.equivFin (BasisIndex X)).symm i).1) :=
  basisDecomposition X ≪≫
    (biproduct.reindex (Fintype.equivFin (BasisIndex X)).symm
      (fun i : BasisIndex X => simpleObject A i.1)).symm

/-- The genuine finite semisimple skeleton of finite graded vector spaces:
all decomposition equations are actual isomorphisms of graded objects. -/
def skeleton (A : Type) [Fintype A] [AddGroup A] :
    FiniteSemisimpleSkeleton (PointedVec A) A where
  simpleObject := simpleObject A
  simple := simple_simpleObject
  iso_injective a b h := simpleObject_iso_injective a b (Classical.choice h)
  length X := Fintype.card (BasisIndex X)
  label X i := ((Fintype.equivFin (BasisIndex X)).symm i).1
  decomposition := finiteBasisDecomposition

/-- Kernels of actual finite graded vector-space morphisms are formed
componentwise, with the componentwise universal property. -/
instance hasKernels : HasKernels (PointedVec A) where
  has_limit {X Y} f := by
    let K : PointedVec A := fun a => kernel (f a)
    let k : K ⟶ X := fun a => kernel.ι (f a)
    have hk : k ≫ f = 0 := by
      funext a
      exact kernel.condition (f a)
    exact HasLimit.mk
      { cone := KernelFork.ofι k hk
        isLimit := KernelFork.IsLimit.ofι k hk
          (fun {W} g hg a => kernel.lift (f a) (g a) (congrFun hg a))
          (fun g hg => by
            funext a
            exact kernel.lift_ι (f a) (g a) (congrFun hg a))
          (fun g hg m hm => by
            funext a
            apply (cancel_mono (kernel.ι (f a))).mp
            exact (congrFun hm a).trans (kernel.lift_ι (f a) (g a) (congrFun hg a)).symm) }

end Paper18.Category.PointedVec
