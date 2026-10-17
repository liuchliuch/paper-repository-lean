import Paper20.FieldHecke

namespace Paper20.FieldHecke
open Module Paper20.HeckeTraceAlgebra
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

section Field
variable {F : Type*} [Field F]

/-- The actual presentation map into the original canonical regular
matrix model at the chosen genuine field parameter. -/
def regularRepresentation (r : ℕ) (z : F) :
    Paper20.PresentedHecke.Presented F r z →ₐ[F] fieldAlgebra r z :=
  Paper20.PresentedHecke.lift F r z
    (fun i => ⟨fieldT r z i,Algebra.subset_adjoin (Set.mem_range_self i)⟩)
    (by intro i; apply Subtype.ext; exact fieldT_quadratic r z i)
    (by intro i j h; apply Subtype.ext; exact fieldT_braid r z i j h)
    (by intro i j h; apply Subtype.ext; exact fieldT_commute r z i j h)

@[simp] theorem regularRepresentation_generator (r : ℕ) (z : F) (i : Fin (r-1)) :
    regularRepresentation r z (Paper20.PresentedHecke.generator F r z i)=
      ⟨fieldT r z i,Algebra.subset_adjoin (Set.mem_range_self i)⟩ :=
  Paper20.PresentedHecke.lift_generator _ _ _ _ _ _ _ i

/-- All actual regular matrices in the generated canonical model have
preimages in the honest presentation; the proof is actual adjoin induction. -/
theorem regularRepresentation_surjective (r : ℕ) (z : F) :
    Function.Surjective (regularRepresentation r z) := by
  have aux : ∀ A : FieldMat (F:=F) r, A ∈ fieldAlgebra r z →
      ∃ a, (regularRepresentation r z a).val=A := by
    intro A hA
    induction hA using Algebra.adjoin_induction with
    | mem A hA =>
      obtain ⟨i,rfl⟩ := hA
      exact ⟨Paper20.PresentedHecke.generator F r z i,
        congrArg Subtype.val (regularRepresentation_generator r z i)⟩
    | algebraMap c =>
      refine ⟨algebraMap F _ c,?_⟩
      rw [AlgHom.commutes]
      rfl
    | add A B hA hB ia ib =>
      obtain ⟨a,ha⟩ := ia
      obtain ⟨b,hb⟩ := ib
      refine ⟨a+b,?_⟩
      rw [map_add]
      change (regularRepresentation r z a).val+(regularRepresentation r z b).val=A+B
      rw [ha,hb]
    | mul A B hA hB ia ib =>
      obtain ⟨a,ha⟩ := ia
      obtain ⟨b,hb⟩ := ib
      refine ⟨a*b,?_⟩
      rw [map_mul]
      change (regularRepresentation r z a).val*(regularRepresentation r z b).val=A*B
      rw [ha,hb]
  intro A
  obtain ⟨a,ha⟩ := aux A.val A.property
  exact ⟨a,Subtype.ext ha⟩

instance fieldAlgebra_finite (r : ℕ) (z : F) : Module.Finite F (fieldAlgebra r z) :=
  Module.Finite.of_surjective (regularRepresentation r z).toLinearMap (regularRepresentation_surjective r z)

/-- The original regular field model has at least r! dimensions, proved
by the actual specialized basis and its unchanged identity columns. -/
theorem fieldAlgebra_finrank_ge (r : ℕ) (z : F) :
    r.factorial≤Module.finrank F (fieldAlgebra r z) := by
  have h := (basisElement_independent r z).fintype_card_le_finrank
  simpa only [standardBasis_index_card] using h

/-- No additional relation appears in the canonical regular model: the
presentation map is injective because the actual factorial word bound and
actual factorial independent identity columns force equal dimensions. -/
theorem regularRepresentation_injective (r : ℕ) (z : F) :
    Function.Injective (regularRepresentation r z) := by
  have hs := regularRepresentation_surjective r z
  have hr := LinearMap.finrank_range_le (regularRepresentation r z).toLinearMap
  have hrange : LinearMap.range (regularRepresentation r z).toLinearMap=⊤ :=
    LinearMap.range_eq_top.mpr hs
  rw [hrange,finrank_top] at hr
  have he : Module.finrank F (Paper20.PresentedHecke.Presented F r z)=
      Module.finrank F (fieldAlgebra r z) :=
    le_antisymm ((Paper20.PresentedHecke.presented_finrank_le F r z).trans
      (fieldAlgebra_finrank_ge r z)) hr
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank he
    (f:=(regularRepresentation r z).toLinearMap)).mpr hs

/-- A proved algebra isomorphism from the honest type-A presentation to
the original actual permutation-indexed canonical Hecke matrix model. -/
def regularEquiv (r : ℕ) (z : F) :
    Paper20.PresentedHecke.Presented F r z ≃ₐ[F] fieldAlgebra r z :=
  AlgEquiv.ofBijective (regularRepresentation r z)
    ⟨regularRepresentation_injective r z,regularRepresentation_surjective r z⟩

end Field
end
end Paper20.FieldHecke
