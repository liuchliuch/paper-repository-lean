import Paper28.FreeProductCurrentMaps
import Paper28.BassSerreFactorRawRecovery

/-! Concrete factor-current recovery on the actual quotient polyhedral
groups. Exact lifted presentations connect the canonical factor inclusion
to the native raw restriction theorem; no recovery assertion is an input.
-/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable (Std : PaperStandardInputs) {G : Type} [Group G] [DecidableEq G] [Countable G]
  {A B : Subgroup G} (T : BassSerreObject A B)
  (DG : SphericalQuotientCurrentData Std.currentCalculus G)
  (DA : SphericalQuotientCurrentData Std.currentCalculus A)
  (DB : SphericalQuotientCurrentData Std.currentCalculus B)

theorem factorTransfer_recovery_AA (k : ℕ) (P : sphericalPolyhedralCurrents DA.simplex (k+1)) :
    freeProductTransferA Std DG DA T k (factorPolyhedralInclusionA Std DG DA (k+1) P) =
      (groupHomCurrentPush Std.currentCalculus DA.M DA.M DA.algebra DA.algebra (MonoidHom.id A)).push (k+1) P.val := by
  obtain ⟨z,w,hz,hw,hlift⟩ := factorPolyhedralInclusionA_lifted Std DG DA (k+1) P
  rw [← hw]
  change bassSerreTransferA DG.lifted Std.currentCalculus T DA.M DA.algebra DG.simplex DG.gluing DA.massFaithful k
    (projectedSphericalChain DG.simplex (k+1) w) = _
  rw [bassSerreTransferA_presentation,hlift]
  have he := bassSerreRawTransfer_factorA_A T Std.hilbertGrouping DA.M DA.sphereAlgebra DG.sphereAlgebra
    DA.algebra Std.currentCalculus DA.massFaithful k (liftedSphericalChain DA.lifted (k+1) z)
  rw [DA.gluing.projected_compatibility,hz] at he
  exact he

theorem factorTransfer_recovery_AB (k : ℕ) (P : sphericalPolyhedralCurrents DA.simplex (k+1)) :
    freeProductTransferB Std DG DB T k (factorPolyhedralInclusionA Std DG DA (k+1) P) = 0 := by
  obtain ⟨z,w,_,hw,hlift⟩ := factorPolyhedralInclusionA_lifted Std DG DA (k+1) P
  rw [← hw]
  change bassSerreTransferB DG.lifted Std.currentCalculus T DB.M DB.algebra DG.simplex DG.gluing DB.massFaithful k
    (projectedSphericalChain DG.simplex (k+1) w) = _
  rw [bassSerreTransferB_presentation,hlift]
  exact bassSerreRawTransfer_factorA_B T Std.hilbertGrouping DB.M DA.sphereAlgebra DG.sphereAlgebra
    DB.algebra Std.currentCalculus DB.massFaithful k (liftedSphericalChain DA.lifted (k+1) z)

theorem factorTransfer_recovery_BA (k : ℕ) (P : sphericalPolyhedralCurrents DB.simplex (k+1)) :
    freeProductTransferA Std DG DA T k (factorPolyhedralInclusionB Std DG DB (k+1) P) = 0 := by
  obtain ⟨z,w,_,hw,hlift⟩ := factorPolyhedralInclusionB_lifted Std DG DB (k+1) P
  rw [← hw]
  change bassSerreTransferA DG.lifted Std.currentCalculus T DA.M DA.algebra DG.simplex DG.gluing DA.massFaithful k
    (projectedSphericalChain DG.simplex (k+1) w) = _
  rw [bassSerreTransferA_presentation,hlift]
  exact bassSerreRawTransfer_factorB_A T Std.hilbertGrouping DA.M DB.sphereAlgebra DG.sphereAlgebra
    DA.algebra Std.currentCalculus DA.massFaithful k (liftedSphericalChain DB.lifted (k+1) z)

theorem factorTransfer_recovery_BB (k : ℕ) (P : sphericalPolyhedralCurrents DB.simplex (k+1)) :
    freeProductTransferB Std DG DB T k (factorPolyhedralInclusionB Std DG DB (k+1) P) =
      (groupHomCurrentPush Std.currentCalculus DB.M DB.M DB.algebra DB.algebra (MonoidHom.id B)).push (k+1) P.val := by
  obtain ⟨z,w,hz,hw,hlift⟩ := factorPolyhedralInclusionB_lifted Std DG DB (k+1) P
  rw [← hw]
  change bassSerreTransferB DG.lifted Std.currentCalculus T DB.M DB.algebra DG.simplex DG.gluing DB.massFaithful k
    (projectedSphericalChain DG.simplex (k+1) w) = _
  rw [bassSerreTransferB_presentation,hlift]
  have he := bassSerreRawTransfer_factorB_B T Std.hilbertGrouping DB.M DB.sphereAlgebra DG.sphereAlgebra
    DB.algebra Std.currentCalculus DB.massFaithful k (liftedSphericalChain DB.lifted (k+1) z)
  rw [DB.gluing.projected_compatibility,hz] at he
  exact he

end Paper28
