import Paper28.PolyhedralCycleComparison

/-! Actual current-cycle gluing, comparison-class compatibility and
the upper mass bound. Song supplies only ordinary norm-folding naturality;
current addition and its mass estimate are native AK algebra consequences.
-/
set_option autoImplicit false
noncomputable section
namespace Paper28

theorem groupHomCurrentPush_mass_le (F : CanonicalGlobalCurrentCalculusInput)
    {G K : Type} [Group G] [Group K] [DecidableEq G] [DecidableEq K] [Countable G] [Countable K]
    (MG : SphericalQuotientMetricInput G) (MK : SphericalQuotientMetricInput K)
    (I : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient G) MG.metric)
    (J : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient K) MK.metric)
    (θ : G →* K) (n : ℕ) (C : I.Current n) :
    J.mass ((groupHomCurrentPush F MG MK I J θ).push n C) ≤ I.mass C := by
  letI := MG.metric
  letI := MK.metric
  have h := (groupHomCurrentPush F MG MK I J θ).mass_lipschitz_le n C 1
    (groupHomQuotientFold_lipschitz MG MK θ).lipschitzOnWith
  simpa only [NNReal.coe_one,one_pow,one_mul] using h

variable (Std : PaperStandardInputs) {G : Type} [Group G] [DecidableEq G] [Countable G]
  {A B : Subgroup G}
  (DG : SphericalQuotientCurrentData Std.currentCalculus G)
  (DA : SphericalQuotientCurrentData Std.currentCalculus A)
  (DB : SphericalQuotientCurrentData Std.currentCalculus B)

theorem quotientComparison_mass_nonempty (k : ℕ) (h : Std.groupHomology.group G (k+1)) :
    (currentClassMasses DG.algebra k ((quotientDataComparison Std DG).toCurrent k h)).Nonempty := by
  obtain ⟨C,hC⟩ := (quotientDataComparison Std DG).realizable k h
  exact ⟨DG.algebra.mass C.val,C,hC,rfl⟩

def freeProductCycleSum (k : ℕ) (C : PositiveCurrentCycles DA.algebra k) (D : PositiveCurrentCycles DB.algebra k) :
    PositiveCurrentCycles DG.algebra k :=
  globalCurrentCyclesPush (groupHomCurrentPush Std.currentCalculus DA.M DG.M DA.algebra DG.algebra A.subtype) k C+
    globalCurrentCyclesPush (groupHomCurrentPush Std.currentCalculus DB.M DG.M DB.algebra DG.algebra B.subtype) k D

theorem freeProductCycleSum_class (k : ℕ)
    (α : Std.groupHomology.group A (k+1)) (β : Std.groupHomology.group B (k+1))
    (C : PositiveCurrentCycles DA.algebra k) (D : PositiveCurrentCycles DB.algebra k)
    (hC : positiveCurrentClass DA.algebra k C = (quotientDataComparison Std DA).toCurrent k α)
    (hD : positiveCurrentClass DB.algebra k D = (quotientDataComparison Std DB).toCurrent k β) :
    positiveCurrentClass DG.algebra k (freeProductCycleSum Std DG DA DB k C D) =
      (quotientDataComparison Std DG).toCurrent k
        (Std.groupHomology.map A.subtype (k+1) α+Std.groupHomology.map B.subtype (k+1) β) := by
  have hA := Std.song.naturality DA.M DG.M DA.algebra DG.algebra A.subtype k α C hC
  have hB := Std.song.naturality DB.M DG.M DB.algebra DG.algebra B.subtype k β D hD
  change (positiveCurrentClassHom DG.algebra k) (_+_) = _
  rw [map_add,map_add]
  exact congrArg₂ (fun x y => x+y) hA hB

theorem freeProductCycleSum_mass (k : ℕ)
    (C : PositiveCurrentCycles DA.algebra k) (D : PositiveCurrentCycles DB.algebra k) :
    DG.algebra.mass (freeProductCycleSum Std DG DA DB k C D).val ≤ DA.algebra.mass C.val+DB.algebra.mass D.val := by
  exact (DG.algebra.mass_add_le _ _).trans (add_le_add
    (groupHomCurrentPush_mass_le Std.currentCalculus DA.M DG.M DA.algebra DG.algebra A.subtype (k+1) C.val)
    (groupHomCurrentPush_mass_le Std.currentCalculus DB.M DG.M DB.algebra DG.algebra B.subtype (k+1) D.val))

def freeProductPolyhedralCycleSum (k : ℕ) (P : PolyhedralCycle DA.simplex k) (Q : PolyhedralCycle DB.simplex k) :
    PolyhedralCycle DG.simplex k where
  current := factorPolyhedralInclusionA Std DG DA (k+1) P.current+factorPolyhedralInclusionB Std DG DB (k+1) Q.current
  closed := (freeProductCycleSum Std DG DA DB k P.toCycle Q.toCycle).property

theorem freeProductPolyhedralCycleSum_class (k : ℕ)
    (α : Std.groupHomology.group A (k+1)) (β : Std.groupHomology.group B (k+1))
    (P : PolyhedralCycle DA.simplex k) (Q : PolyhedralCycle DB.simplex k)
    (hP : P.homologyClass = (quotientDataComparison Std DA).toCurrent k α)
    (hQ : Q.homologyClass = (quotientDataComparison Std DB).toCurrent k β) :
    (freeProductPolyhedralCycleSum Std DG DA DB k P Q).homologyClass =
      (quotientDataComparison Std DG).toCurrent k
        (Std.groupHomology.map A.subtype (k+1) α+Std.groupHomology.map B.subtype (k+1) β) :=
  freeProductCycleSum_class Std DG DA DB k α β P.toCycle Q.toCycle hP hQ

end Paper28
