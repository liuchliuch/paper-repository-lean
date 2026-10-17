import Paper23.CertificateSparse
import Paper23.LabelBoundary

/-! The transpose of the actual endpoint boundary. The finite coface expansion
allows sparse verification of a cocycle on every original three-cube. -/
namespace Paper23.CertificateChecks
open Cubical

@[simp] theorem prepend_coeff_same (a : GraphCell) (x : RawChain) (c : RawCube) :
    prepend a x (a :: c) = x c := by
  change Finsupp.mapDomain (List.cons a) x (List.cons a c) = _
  apply Finsupp.mapDomain_apply
  intro c d h
  exact (List.cons.inj h).2

theorem prepend_coeff_ne (a b : GraphCell) (x : RawChain) (c : RawCube)
    (hne : a ≠ b) : prepend a x (b :: c) = 0 := by
  change Finsupp.mapDomain (List.cons a) x (b :: c) = _
  apply Finsupp.mapDomain_notin_range
  rintro ⟨d,h⟩
  exact hne (List.cons.inj h).1

@[simp] theorem prepend_coeff_nil (a : GraphCell) (x : RawChain) : prepend a x [] = 0 := by
  change Finsupp.mapDomain (List.cons a) x [] = _
  apply Finsupp.mapDomain_notin_range
  rintro ⟨d,h⟩
  cases h

/-- Coefficient of a vertex in the oriented boundary of an edge. -/
def vertexIncidence (v : Vertex) (e : Edge) : ℤ :=
  (if (endpoints e).2 = v then 1 else 0) - (if (endpoints e).1 = v then 1 else 0)

noncomputable def vertexCofaces (v : Vertex) (c : RawCube) : RawChain :=
  ∑ e : Edge, vertexIncidence v e • basis (.edge e :: c)

@[simp] theorem vertexCofaces_coeff_nil (v : Vertex) (c : RawCube) :
    vertexCofaces v c [] = 0 := by
  classical
  simp [vertexCofaces,basis]

@[simp] theorem vertexCofaces_coeff_vertex (v w : Vertex) (c d : RawCube) :
    vertexCofaces v c (.vertex w :: d) = 0 := by
  classical
  simp [vertexCofaces,basis]

@[simp] theorem vertexCofaces_coeff_edge (v : Vertex) (c d : RawCube) (e : Edge) :
    vertexCofaces v c (.edge e :: d) = if c = d then vertexIncidence v e else 0 := by
  classical
  by_cases h : c = d <;> simp [vertexCofaces,basis,Finsupp.single_apply,List.cons.injEq,h]

/-- Cofaces with particle-label orientation, before the same diagonal
orientation change used for the original boundary. -/
noncomputable def labelCoBoundaryBasis : RawCube → RawChain
  | [] => 0
  | .vertex v :: c => vertexCofaces v c + prepend (.vertex v) (labelCoBoundaryBasis c)
  | .edge e :: c => -prepend (.edge e) (labelCoBoundaryBasis c)

@[simp] theorem labelCoBoundaryBasis_nil_coeff (c : RawCube) :
    labelCoBoundaryBasis c [] = 0 := by cases c with
  | nil => rfl
  | cons a c => cases a <;> simp [labelCoBoundaryBasis]

@[simp] theorem labelBoundaryBasis_coeff_nil (c : RawCube) :
    labelBoundaryBasis c [] = 0 := by cases c with
  | nil => rfl
  | cons a c => cases a <;> simp [labelBoundaryBasis,basis]

/-- Exact transpose identity on all raw labelled products. No configuration
validity assumption is needed for this endpoint incidence calculation. -/
theorem labelCoBoundary_adjoint (c d : RawCube) :
    labelCoBoundaryBasis c d = labelBoundaryBasis d c := by
  induction c generalizing d with
  | nil => cases d <;> simp [labelCoBoundaryBasis]
  | cons a c ih =>
    cases d with
    | nil => simp
    | cons b d =>
      cases a with
      | vertex v =>
        cases b with
        | vertex w =>
          by_cases h : v = w
          · subst w; simp [labelCoBoundaryBasis,labelBoundaryBasis,ih]
          · have hv : GraphCell.vertex v ≠ .vertex w := by simpa using h
            have hw := Ne.symm hv
            simp [labelCoBoundaryBasis,labelBoundaryBasis,prepend_coeff_ne _ _ _ _ hv,
              prepend_coeff_ne _ _ _ _ hw]
        | edge e =>
          have hve : GraphCell.vertex v ≠ .edge e := by simp
          have hev := Ne.symm hve
          by_cases h : c = d
          · subst d
            simp [labelCoBoundaryBasis,labelBoundaryBasis,vertexIncidence,basis,
              prepend_coeff_ne _ _ _ _ hve,prepend_coeff_ne _ _ _ _ hev,
              Finsupp.single_apply,List.cons.injEq,eq_comm]
          · simp [labelCoBoundaryBasis,labelBoundaryBasis,vertexIncidence,basis,
              prepend_coeff_ne _ _ _ _ hve,prepend_coeff_ne _ _ _ _ hev,h,Ne.symm h]
      | edge e =>
        cases b with
        | vertex v =>
          have hve : GraphCell.vertex v ≠ .edge e := by simp
          have hev := Ne.symm hve
          simp [labelCoBoundaryBasis,labelBoundaryBasis,
            prepend_coeff_ne _ _ _ _ hve,prepend_coeff_ne _ _ _ _ hev]
        | edge f =>
          by_cases h : e = f
          · subst f; simp [labelCoBoundaryBasis,labelBoundaryBasis,basis,ih]
          · have hef : GraphCell.edge e ≠ .edge f := by simpa using h
            have hfe := Ne.symm hef
            simp [labelCoBoundaryBasis,labelBoundaryBasis,basis,
              prepend_coeff_ne _ _ _ _ hef,prepend_coeff_ne _ _ _ _ hfe]

/-- The diagonal orientation map acts coefficient by coefficient. -/
theorem reorient_coeff (x : RawChain) (c : RawCube) :
    reorient x c = orientation c * x c := by
  have h : (Finsupp.lapply c : RawChain →ₗ[ℤ] ℤ).comp reorient =
      orientation c • (Finsupp.lapply c : RawChain →ₗ[ℤ] ℤ) := by
    apply Finsupp.lhom_ext
    intro d n
    change reorient (Finsupp.single d n) c = orientation c * (Finsupp.single d n) c
    have hs : Finsupp.single d n = n • basis d := by simp [basis]
    rw [hs, map_smul, reorient_basis]
    by_cases hd : d = c
    · subst d
      simp [basis,smul_smul,mul_comm]
    · simp [basis,Finsupp.single_apply,hd,Ne.symm hd]
  exact LinearMap.congr_fun h x

/-- Cofaces with the original increasing-moving-edge orientation. -/
noncomputable def coBoundaryBasis (c : RawCube) : RawChain :=
  orientation c • reorient (labelCoBoundaryBasis c)

/-- The transpose identity for the exact original boundary, including signs. -/
theorem coBoundary_adjoint (c d : RawCube) :
    coBoundaryBasis c d = boundary (basis d) c := by
  simp only [coBoundaryBasis,boundary,LinearMap.comp_apply,reorient_basis,
    map_smul,labelBoundary_basis,Finsupp.smul_apply,reorient_coeff,smul_eq_mul,
    labelCoBoundary_adjoint]
  ring

/-- Extend the transpose by integer linearity to finitely supported cochains. -/
noncomputable def coBoundary : RawChain →ₗ[ℤ] RawChain :=
  Finsupp.linearCombination ℤ coBoundaryBasis

@[simp] theorem coBoundary_basis (c : RawCube) :
    coBoundary (basis c) = coBoundaryBasis c := by simp [coBoundary,basis]

end Paper23.CertificateChecks
