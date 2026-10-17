import Paper28.TransferredCycleClasses
import Paper28.SphericalCycleGluing

/-! Recovery of the two actual Song comparison classes on the reference
polyhedral cycle. Current recovery is native; preservation by absolute
value is derived from ordinary Song naturality for the identity homomorphism.
-/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable (Std : PaperStandardInputs) {G : Type} [Group G] [DecidableEq G] [Countable G]
  {A B : Subgroup G} (T : BassSerreObject A B)
  (DG : SphericalQuotientCurrentData Std.currentCalculus G)
  (DA : SphericalQuotientCurrentData Std.currentCalculus A)
  (DB : SphericalQuotientCurrentData Std.currentCalculus B)

theorem factor_reference_transfer_classes (k : ℕ)
    (α : Std.groupHomology.group A (k+2)) (β : Std.groupHomology.group B (k+2))
    (P : PolyhedralCycle DA.simplex (k+1)) (Q : PolyhedralCycle DB.simplex (k+1))
    (hP : P.homologyClass = (quotientDataComparison Std DA).toCurrent (k+1) α)
    (hQ : Q.homologyClass = (quotientDataComparison Std DB).toCurrent (k+1) β) :
    positiveCurrentClass DA.algebra (k+1)
        (transferredCycleA Std T DG DA k (freeProductPolyhedralCycleSum Std DG DA DB (k+1) P Q)) =
      (quotientDataComparison Std DA).toCurrent (k+1) α ∧
    positiveCurrentClass DB.algebra (k+1)
        (transferredCycleB Std T DG DB k (freeProductPolyhedralCycleSum Std DG DA DB (k+1) P Q)) =
      (quotientDataComparison Std DB).toCurrent (k+1) β := by
  let P₀ := freeProductPolyhedralCycleSum Std DG DA DB (k+1) P Q
  have hA : freeProductTransferA Std DG DA T (k+1) P₀.current =
      (groupHomCurrentPush Std.currentCalculus DA.M DA.M DA.algebra DA.algebra (MonoidHom.id A)).push (k+2) P.current.val := by
    change freeProductTransferA Std DG DA T (k+1)
      (factorPolyhedralInclusionA Std DG DA (k+2) P.current+factorPolyhedralInclusionB Std DG DB (k+2) Q.current) = _
    rw [map_add,factorTransfer_recovery_AA,factorTransfer_recovery_BA,add_zero]
  have hB : freeProductTransferB Std DG DB T (k+1) P₀.current =
      (groupHomCurrentPush Std.currentCalculus DB.M DB.M DB.algebra DB.algebra (MonoidHom.id B)).push (k+2) Q.current.val := by
    change freeProductTransferB Std DG DB T (k+1)
      (factorPolyhedralInclusionA Std DG DA (k+2) P.current+factorPolyhedralInclusionB Std DG DB (k+2) Q.current) = _
    rw [map_add,factorTransfer_recovery_AB,factorTransfer_recovery_BB,zero_add]
  have heA : transferredCycleA Std T DG DA k P₀ =
      globalCurrentCyclesPush (groupHomCurrentPush Std.currentCalculus DA.M DA.M DA.algebra DA.algebra (MonoidHom.id A))
        (k+1) P.toCycle := Subtype.ext hA
  have heB : transferredCycleB Std T DG DB k P₀ =
      globalCurrentCyclesPush (groupHomCurrentPush Std.currentCalculus DB.M DB.M DB.algebra DB.algebra (MonoidHom.id B))
        (k+1) Q.toCycle := Subtype.ext hB
  constructor
  · change positiveCurrentClass DA.algebra (k+1) (transferredCycleA Std T DG DA k P₀) = _
    rw [heA]
    have h := Std.song.naturality DA.M DA.M DA.algebra DA.algebra (MonoidHom.id A) (k+1) α P.toCycle hP
    rw [Std.groupHomology.map_identity] at h
    exact h
  · change positiveCurrentClass DB.algebra (k+1) (transferredCycleB Std T DG DB k P₀) = _
    rw [heB]
    have h := Std.song.naturality DB.M DB.M DB.algebra DB.algebra (MonoidHom.id B) (k+1) β Q.toCycle hQ
    rw [Std.groupHomology.map_identity] at h
    exact h

end Paper28
