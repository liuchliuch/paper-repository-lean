import Paper18.Category.SemisimpleCoendDinatural

/-!
# Coends of actual complex-bilinear bifunctors on finite semisimple categories

The finite sum over actual simple objects carries a proved cowedge and its
actual universal property. Coend existence and the direct-sum comparison
are consequences, not premises or numerical certificates.
-/
noncomputable section
open Classical Opposite
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe v u w v' u'
namespace Paper18.Category.FiniteSemisimpleSkeleton
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  (H : Cᵒᵖ ⥤ C ⥤ D) [H.Additive] [H.Linear ℂ]
  [∀ X, (H.obj X).Additive] [∀ X, (H.obj X).Linear ℂ]

omit [Linear ℂ C] [Linear ℂ D] [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [H.Additive] [H.Linear ℂ] [∀ X, (H.obj X).Additive] [∀ X, (H.obj X).Linear ℂ] in
lemma coendExtend_postcomp {Z W : D}
    (q : ∀ i, (H.obj (op (S.simpleObject i))).obj (S.simpleObject i) ⟶ Z)
    (g : Z ⟶ W) (X : C) :
    S.coendExtend H q X ≫ g = S.coendExtend H (fun i => q i ≫ g) X := by
  simp only [coendExtend, Preadditive.sum_comp, Category.assoc]

omit [Linear ℂ C] [Linear ℂ D] [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [H.Linear ℂ] [∀ X, (H.obj X).Additive] [∀ X, (H.obj X).Linear ℂ] in
/-- An actual cowedge is recovered by extending its components on simples. -/
lemma coendExtend_cowedge (c : Cowedge H) (X : C) :
    S.coendExtend H (fun i => c.π (S.simpleObject i)) X = c.π X := by
  unfold coendExtend
  calc
    _ = ∑ a : Fin (S.length X),
        (H.map (S.coendInclusion X a).op).app X ≫
          (H.map (S.coendProjection X a).op).app X ≫ c.π X := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← Cowedge.condition c (S.coendProjection X a)]
    _ = (H.map ((∑ a : Fin (S.length X),
        S.coendProjection X a ≫ S.coendInclusion X a)).op).app X ≫ c.π X := by
      simp only [op_sum, H.map_sum, NatTrans.app_sum, Preadditive.sum_comp,
        op_comp, H.map_comp, NatTrans.comp_app, Category.assoc]
    _ = c.π X := by rw [S.coendResolution]; simp

variable [HasFiniteBiproducts D]

/-- The actual diagonal bifunctor value at a simple representative. -/
abbrev semisimpleCoendDiagonal (i : ι) : D :=
  (H.obj (op (S.simpleObject i))).obj (S.simpleObject i)

/-- The actual finite sum of the bifunctor's simple diagonal. -/
def semisimpleCoendObject : D := ⨁ S.semisimpleCoendDiagonal H

/-- The actual dinatural family into the simple-diagonal direct sum. -/
def semisimpleCoendCowedge : Cowedge H :=
  Cowedge.mk (S.semisimpleCoendObject H)
    (S.coendExtend H (fun i => biproduct.ι (S.semisimpleCoendDiagonal H) i))
    (fun _ _ f => S.coendExtend_dinatural H _ f)

@[simp]
lemma semisimpleCoendCowedge_simple (i : ι) :
    (S.semisimpleCoendCowedge H).π (S.simpleObject i) = biproduct.ι (S.semisimpleCoendDiagonal H) i :=
  S.coendExtend_simple H _ i

/-- The finite simple-diagonal sum has the actual coend universal property. -/
def semisimpleCoendIsColimit : IsColimit (S.semisimpleCoendCowedge H) :=
  Multicofork.IsColimit.mk _
    (fun c => biproduct.desc (fun i : ι => c.π (S.simpleObject i)))
    (fun c X => by
      change S.coendExtend H _ X ≫ _ = _
      rw [S.coendExtend_postcomp]
      simp only [biproduct.ι_desc]
      exact S.coendExtend_cowedge H c X)
    (fun c m hm => by
      apply biproduct.hom_ext'
      intro i
      rw [biproduct.ι_desc]
      simpa only [S.semisimpleCoendCowedge_simple H i] using hm (S.simpleObject i))

/-- Coend existence is derived from the proved finite universal cowedge. -/
def semisimpleHasCoend : HasCoend H :=
  HasColimit.mk
    { cocone := S.semisimpleCoendCowedge H
      isColimit := S.semisimpleCoendIsColimit H }

/-- The mathlib coend is isomorphic to the actual finite simple-diagonal sum. -/
def semisimpleCoendIso :
    letI := S.semisimpleHasCoend H
    coend H ≅ S.semisimpleCoendObject H := by
  letI := S.semisimpleHasCoend H
  exact (colimit.isColimit _).coconePointUniqueUpToIso (S.semisimpleCoendIsColimit H)

/-- Canonical coend inclusions become the explicitly constructed actual
simple-summand resolution under the comparison isomorphism. -/
@[reassoc (attr := simp)]
lemma semisimpleCoendIso_ι (X : C) :
    letI := S.semisimpleHasCoend H
    coend.ι H X ≫ (S.semisimpleCoendIso H).hom =
      S.coendExtend H (fun i => biproduct.ι (S.semisimpleCoendDiagonal H) i) X := by
  letI := S.semisimpleHasCoend H
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (S.semisimpleCoendIsColimit H) (.right X)

/-- On an actual simple representative, the comparison identifies its
coend inclusion with the corresponding finite-biproduct inclusion. -/
@[reassoc (attr := simp)]
lemma semisimpleCoendIso_ι_simple (i : ι) :
    letI := S.semisimpleHasCoend H
    coend.ι H (S.simpleObject i) ≫ (S.semisimpleCoendIso H).hom =
      biproduct.ι (S.semisimpleCoendDiagonal H) i := by
  letI := S.semisimpleHasCoend H
  rw [S.semisimpleCoendIso_ι H, S.coendExtend_simple H]

@[reassoc (attr := simp)]
lemma semisimpleCoendIso_inv_ι (i : ι) :
    letI := S.semisimpleHasCoend H
    biproduct.ι (S.semisimpleCoendDiagonal H) i ≫ (S.semisimpleCoendIso H).inv =
      coend.ι H (S.simpleObject i) := by
  letI := S.semisimpleHasCoend H
  apply (cancel_mono (S.semisimpleCoendIso H).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, S.semisimpleCoendIso_ι_simple H]

end Paper18.Category.FiniteSemisimpleSkeleton
