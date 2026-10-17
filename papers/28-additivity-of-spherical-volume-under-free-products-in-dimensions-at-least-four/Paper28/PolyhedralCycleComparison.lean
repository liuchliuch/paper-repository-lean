import Paper28.FreeProductCurrentMaps

/-! Actual polyhedral cycles, representatives supplied by native 3.1(i),
and exact polyhedral homology comparisons supplied by native 3.1(ii).
These are the source comparisons needed for arbitrary competitors. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {G : Type} [Group G] [DecidableEq G] [Countable G]
  {M : SphericalQuotientMetricInput G}
  {I : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient G) M.metric}
  (S : SphericalSimplexIntegrationInput M I.toCompactIntegralCurrentSupportInput)

structure PolyhedralCycle (k : ℕ) where
  current : sphericalPolyhedralCurrents S (k+1)
  closed : I.boundary k current.val = 0

def PolyhedralCycle.toCycle {k : ℕ} (P : PolyhedralCycle S k) : PositiveCurrentCycles I k := ⟨P.current.val,P.closed⟩

def PolyhedralCycle.homologyClass {k : ℕ} (P : PolyhedralCycle S k) : PositiveCurrentHomology I k :=
  positiveCurrentClass I k P.toCycle

variable (Std : PaperStandardInputs) (D : SphericalQuotientCurrentData Std.currentCalculus G)

theorem polyhedral_cycle_representative (k : ℕ) (h : Std.groupHomology.group G (k+1)) :
    ∃ P : PolyhedralCycle D.simplex k, P.homologyClass = (quotientDataComparison Std D).toCurrent k h := by
  obtain ⟨C,hC⟩ := (quotientDataComparison Std D).realizable k h
  obtain ⟨P,W,hP,hClosed,hHom,_⟩ := (quotientData_approximation Std D k).1 C.val C.property 1 (by norm_num)
  let Q : PolyhedralCycle D.simplex k := ⟨⟨P,hP⟩,hClosed⟩
  have he : positiveCurrentClass D.algebra k C = Q.homologyClass :=
    (positiveCurrentClass_eq_iff_boundary D.algebra k C Q.toCycle).mpr ⟨W,hHom⟩
  exact ⟨Q,he.symm.trans hC⟩

def quotientPolyhedralBoundary (k : ℕ) :
    sphericalPolyhedralCurrents D.simplex (k+1) →+ sphericalPolyhedralCurrents D.simplex k :=
  sphericalPolyhedralBoundary D.simplex D.lifted Std.currentCalculus D.gluing k

theorem polyhedral_cycle_homology_filling (k : ℕ) (P Q : PolyhedralCycle D.simplex k)
    (hPQ : P.homologyClass = Q.homologyClass) :
    ∃ W : sphericalPolyhedralCurrents D.simplex (k+2),
      quotientPolyhedralBoundary Std D (k+1) W = P.current-Q.current := by
  obtain ⟨C,hC⟩ := (positiveCurrentClass_eq_iff_boundary D.algebra k P.toCycle Q.toCycle).mp hPQ
  obtain ⟨W,hW,hBoundary⟩ := (quotientData_approximation Std D k).2 (P.current.val-Q.current.val)
    (AddSubgroup.sub_mem _ P.current.property Q.current.property) ⟨C,hC.symm⟩
  exact ⟨⟨W,hW⟩,Subtype.ext hBoundary⟩

theorem approximate_cycle_in_class (k : ℕ) (C : PositiveCurrentCycles D.algebra k) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : PolyhedralCycle D.simplex k,
      P.homologyClass = positiveCurrentClass D.algebra k C ∧ D.algebra.mass P.current.val ≤ D.algebra.mass C.val+ε := by
  obtain ⟨P,W,hP,hClosed,hHom,hMass⟩ := (quotientData_approximation Std D k).1 C.val C.property ε hε
  let Q : PolyhedralCycle D.simplex k := ⟨⟨P,hP⟩,hClosed⟩
  exact ⟨Q,((positiveCurrentClass_eq_iff_boundary D.algebra k C Q.toCycle).mpr ⟨W,hHom⟩).symm,hMass⟩

end Paper28
