import Paper28.FactorTransferRecovery
import Paper28.PolyhedralCycleComparison

/-! Native transfer of cycles and invariance of their actual current
homology classes. The latter uses the proved exact polyhedral filling
part of 3.1 and the actual transfer boundary formula, so it applies to
every current-homologous competitor. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable (Std : PaperStandardInputs) {G : Type} [Group G] [DecidableEq G] [Countable G]
  {A B : Subgroup G} (T : BassSerreObject A B)
  (DG : SphericalQuotientCurrentData Std.currentCalculus G)
  (DA : SphericalQuotientCurrentData Std.currentCalculus A)
  (DB : SphericalQuotientCurrentData Std.currentCalculus B)

def transferredCycleA (k : ℕ) (P : PolyhedralCycle DG.simplex (k+1)) : PositiveCurrentCycles DA.algebra (k+1) :=
  ⟨freeProductTransferA Std DG DA T (k+1) P.current,by
    have h := bassSerreTransferA_boundary DG.lifted Std.currentCalculus T DA.M DA.algebra DG.simplex
      DG.gluing DA.massFaithful k P.current
    have hz : sphericalPolyhedralBoundary DG.simplex DG.lifted Std.currentCalculus DG.gluing (k+1) P.current = 0 :=
      Subtype.ext P.closed
    simpa only [hz,map_zero] using h⟩

def transferredCycleB (k : ℕ) (P : PolyhedralCycle DG.simplex (k+1)) : PositiveCurrentCycles DB.algebra (k+1) :=
  ⟨freeProductTransferB Std DG DB T (k+1) P.current,by
    have h := bassSerreTransferB_boundary DG.lifted Std.currentCalculus T DB.M DB.algebra DG.simplex
      DG.gluing DB.massFaithful k P.current
    have hz : sphericalPolyhedralBoundary DG.simplex DG.lifted Std.currentCalculus DG.gluing (k+1) P.current = 0 :=
      Subtype.ext P.closed
    simpa only [hz,map_zero] using h⟩

theorem transferredCycleA_class_invariant (k : ℕ) (P Q : PolyhedralCycle DG.simplex (k+1))
    (hPQ : P.homologyClass = Q.homologyClass) :
    positiveCurrentClass DA.algebra (k+1) (transferredCycleA Std T DG DA k P) =
      positiveCurrentClass DA.algebra (k+1) (transferredCycleA Std T DG DA k Q) := by
  obtain ⟨W,hW⟩ := polyhedral_cycle_homology_filling Std DG (k+1) P Q hPQ
  apply (positiveCurrentClass_eq_iff_boundary DA.algebra (k+1) _ _).mpr
  refine ⟨freeProductTransferA Std DG DA T (k+2) W,?_⟩
  have he := bassSerreTransferA_boundary DG.lifted Std.currentCalculus T DA.M DA.algebra DG.simplex
    DG.gluing DA.massFaithful (k+1) W
  change DA.algebra.boundary (k+2) (freeProductTransferA Std DG DA T (k+2) W) =
    freeProductTransferA Std DG DA T (k+1) (quotientPolyhedralBoundary Std DG (k+2) W) at he
  rw [hW,map_sub] at he
  exact he.symm

theorem transferredCycleB_class_invariant (k : ℕ) (P Q : PolyhedralCycle DG.simplex (k+1))
    (hPQ : P.homologyClass = Q.homologyClass) :
    positiveCurrentClass DB.algebra (k+1) (transferredCycleB Std T DG DB k P) =
      positiveCurrentClass DB.algebra (k+1) (transferredCycleB Std T DG DB k Q) := by
  obtain ⟨W,hW⟩ := polyhedral_cycle_homology_filling Std DG (k+1) P Q hPQ
  apply (positiveCurrentClass_eq_iff_boundary DB.algebra (k+1) _ _).mpr
  refine ⟨freeProductTransferB Std DG DB T (k+2) W,?_⟩
  have he := bassSerreTransferB_boundary DG.lifted Std.currentCalculus T DB.M DB.algebra DG.simplex
    DG.gluing DB.massFaithful (k+1) W
  change DB.algebra.boundary (k+2) (freeProductTransferB Std DG DB T (k+2) W) =
    freeProductTransferB Std DG DB T (k+1) (quotientPolyhedralBoundary Std DG (k+2) W) at he
  rw [hW,map_sub] at he
  exact he.symm

end Paper28
