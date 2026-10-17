import Paper28.FactorComparisonClasses
import Paper28.InfimumArgument

/-! Original Theorem 1.1. All competitors are actual compact integral
currents in the native spherical quotients. Native 3.1 supplies sharp
polyhedral competitors and exact fillings; native 3.2 supplies the actual
transfer and joint mass bound; native factor recovery identifies both
comparison classes. The final infimum is over actual current masses.
The dimension is written k+4 to express precisely n >= 4.
-/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable (Std : PaperStandardInputs) {G : Type} [Group G] [DecidableEq G] [Countable G]
  {A B : Subgroup G}
  (DG : SphericalQuotientCurrentData Std.currentCalculus G)
  (DA : SphericalQuotientCurrentData Std.currentCalculus A)
  (DB : SphericalQuotientCurrentData Std.currentCalculus B)

theorem spherical_volume_additivity_with_tree (T : BassSerreObject A B) (k : ℕ)
    (α : Std.groupHomology.group A (k+4)) (β : Std.groupHomology.group B (k+4)) :
    groupSphericalVolume Std.groupHomology Std.currentCalculus Std.song DG.M DG.algebra (k+3)
      (Std.groupHomology.map A.subtype (k+4) α+Std.groupHomology.map B.subtype (k+4) β) =
      groupSphericalVolume Std.groupHomology Std.currentCalculus Std.song DA.M DA.algebra (k+3) α+
      groupSphericalVolume Std.groupHomology Std.currentCalculus Std.song DB.M DB.algebra (k+3) β := by
  let a := (quotientDataComparison Std DA).toCurrent (k+3) α
  let b := (quotientDataComparison Std DB).toCurrent (k+3) β
  let c := (quotientDataComparison Std DG).toCurrent (k+3)
    (Std.groupHomology.map A.subtype (k+4) α+Std.groupHomology.map B.subtype (k+4) β)
  obtain ⟨PA,hPA⟩ := polyhedral_cycle_representative Std DA (k+3) α
  obtain ⟨PB,hPB⟩ := polyhedral_cycle_representative Std DB (k+3) β
  let P₀ := freeProductPolyhedralCycleSum Std DG DA DB (k+3) PA PB
  have hP₀ : P₀.homologyClass = c := freeProductPolyhedralCycleSum_class Std DG DA DB (k+3) α β PA PB hPA hPB
  have hFactor := factor_reference_transfer_classes Std T DG DA DB (k+2) α β PA PB hPA hPB
  change sInf (currentClassMasses DG.algebra (k+3) c) =
    sInf (currentClassMasses DA.algebra (k+3) a)+sInf (currentClassMasses DB.algebra (k+3) b)
  apply infimum_additivity_of_joint_approximation
    (currentClassMasses DA.algebra (k+3) a) (currentClassMasses DB.algebra (k+3) b)
    (currentClassMasses DG.algebra (k+3) c)
    (currentClassMasses_bddBelow _ _ _) (currentClassMasses_bddBelow _ _ _) (currentClassMasses_bddBelow _ _ _)
    (quotientComparison_mass_nonempty Std DA (k+3) α) (quotientComparison_mass_nonempty Std DB (k+3) β)
    (quotientComparison_mass_nonempty Std DG (k+3) _)
  · rintro mA ⟨CA,hCA,rfl⟩ mB ⟨CB,hCB,rfl⟩
    let CG := freeProductCycleSum Std DG DA DB (k+3) CA CB
    refine ⟨DG.algebra.mass CG.val,⟨CG,?_,rfl⟩,freeProductCycleSum_mass Std DG DA DB (k+3) CA CB⟩
    exact freeProductCycleSum_class Std DG DA DB (k+3) α β CA CB hCA hCB
  · rintro m ⟨C,hC,rfl⟩ ε hε
    obtain ⟨P,hPC,hMass⟩ := approximate_cycle_in_class Std DG (k+3) C ε hε
    have hPP₀ : P.homologyClass = P₀.homologyClass := hPC.trans (hC.trans hP₀.symm)
    let CA := transferredCycleA Std T DG DA (k+2) P
    let CB := transferredCycleB Std T DG DB (k+2) P
    have hCA : positiveCurrentClass DA.algebra (k+3) CA = a :=
      (transferredCycleA_class_invariant Std T DG DA (k+2) P P₀ hPP₀).trans hFactor.1
    have hCB : positiveCurrentClass DB.algebra (k+3) CB = b :=
      (transferredCycleB_class_invariant Std T DG DB (k+2) P P₀ hPP₀).trans hFactor.2
    have hJoint : DA.algebra.mass CA.val+DB.algebra.mass CB.val ≤ DG.algebra.mass P.current.val :=
      bassSerreTransfer_joint_mass DG.lifted Std.currentCalculus T DA.M DB.M DA.algebra DB.algebra DG.simplex
        DG.gluing DA.massFaithful DB.massFaithful DG.finiteArea Std.geodesicMass Std.fischer (k+3) (by omega) P.current
    exact ⟨DA.algebra.mass CA.val,⟨CA,hCA,rfl⟩,DB.algebra.mass CB.val,⟨CB,hCB,rfl⟩,hJoint.trans hMass⟩

theorem theorem_1_1 (Free : IsFreeProductOfSubgroups A B) (k : ℕ)
    (α : Std.groupHomology.group A (k+4)) (β : Std.groupHomology.group B (k+4)) :
    groupSphericalVolume Std.groupHomology Std.currentCalculus Std.song DG.M DG.algebra (k+3)
      (Std.groupHomology.map A.subtype (k+4) α+Std.groupHomology.map B.subtype (k+4) β) =
      groupSphericalVolume Std.groupHomology Std.currentCalculus Std.song DA.M DA.algebra (k+3) α+
      groupSphericalVolume Std.groupHomology Std.currentCalculus Std.song DB.M DB.algebra (k+3) β := by
  obtain ⟨T⟩ := Std.bassSerre.realization A B Free
  exact spherical_volume_additivity_with_tree Std DG DA DB T k α β

end Paper28
