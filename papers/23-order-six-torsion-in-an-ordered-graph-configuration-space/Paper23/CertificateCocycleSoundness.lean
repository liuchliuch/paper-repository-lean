import Paper23.CertificateLookup

/-! Soundness of detecting a cocycle through the sparse transpose of the
original boundary. The numerical transpose certificate remains an explicit
obligation, rather than a replacement assumption in the main theorem. -/
namespace Paper23.CertificateChecks
open Cubical

instance cubeDecidable (c : RawCube) : Decidable (IsCube c) :=
  inferInstanceAs (Decidable (c.length = 4 ∧ c.Pairwise ClosureDisjoint))

noncomputable def linearEvaluation (x : RawChain) :
    (RawChain →ₗ[ℤ] ℤ) →ₗ[ℤ] ℤ where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def pairing : RawChain →ₗ[ℤ] (RawChain →ₗ[ℤ] ℤ) :=
  Finsupp.linearCombination ℤ (fun c => (Finsupp.lapply c : RawChain →ₗ[ℤ] ℤ))

@[simp] theorem pairing_basis (c : RawCube) :
    pairing (basis c) = (Finsupp.lapply c : RawChain →ₗ[ℤ] ℤ) := by simp [pairing,basis]

@[simp] theorem pairing_right_basis (v : RawChain) (c : RawCube) :
    pairing v (basis c) = v c := by
  have h : (linearEvaluation (basis c)).comp pairing =
      (Finsupp.lapply c : RawChain →ₗ[ℤ] ℤ) := by
    apply Finsupp.lhom_ext
    intro d n
    have hs : Finsupp.single d n = n • basis d := by simp [basis]
    change pairing (Finsupp.single d n) (basis c) = (Finsupp.single d n) c
    rw [hs,map_smul,pairing_basis]
    by_cases hd : d = c
    · subst d; simp [basis]
    · simp [basis,Finsupp.single_apply,hd,Ne.symm hd]
  exact LinearMap.congr_fun h v

theorem coBoundary_pairing (v : RawChain) (d : RawCube) :
    coBoundary v d = pairing v (boundary (basis d)) := by
  have h : (Finsupp.lapply d : RawChain →ₗ[ℤ] ℤ).comp coBoundary =
      (linearEvaluation (boundary (basis d))).comp pairing := by
    apply Finsupp.lhom_ext
    intro c n
    have hs : Finsupp.single c n = n • basis c := by simp [basis]
    change coBoundary (Finsupp.single c n) d = pairing (Finsupp.single c n) (boundary (basis d))
    rw [hs,map_smul,map_smul,coBoundary_basis,pairing_basis]
    simp only [Finsupp.smul_apply,LinearMap.smul_apply,Finsupp.lapply_apply,smul_eq_mul]
    rw [coBoundary_adjoint]
  exact LinearMap.congr_fun h v

theorem pairing_coBoundary (v x : RawChain) :
    pairing (coBoundary v) x = pairing v (boundary x) := by
  have h : pairing (coBoundary v) = (pairing v).comp boundary := by
    apply Finsupp.lhom_ext
    intro c n
    have hs : Finsupp.single c n = n • basis c := by simp [basis]
    rw [hs]
    simp only [map_smul,LinearMap.comp_apply,pairing_right_basis]
    rw [coBoundary_pairing]
  exact LinearMap.congr_fun h x

noncomputable def modSix : ℤ →ₗ[ℤ] ZMod 6 :=
  (Int.castAddHom (ZMod 6)).toIntLinearMap

/-- On all genuine ordered chains, the cochain dictionary equals reduction
modulo six of the finite integral pairing. -/
theorem phi_eq_pairing (q : ℕ) (x : RawChain) (hx : x ∈ Chains q) :
    phi x = modSix (pairing phiVector x) := by
  let L := phi - modSix.comp (pairing phiVector)
  have hker : x ∈ LinearMap.ker L := by
    apply map_mem_supported (LinearMap.ker L) LinearMap.id ?_ x hx
    intro c hc
    change IsCube c ∧ degree c = q at hc
    change phi (basis c) - (pairing phiVector (basis c) : ZMod 6) = 0
    rw [phi_basis,pairing_right_basis,phiVector_coeff c hc.1.1]
    exact sub_self _
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp hker)

/-- Projection to the actual closed-closure-disjoint q-cubes. -/
noncomputable def restrictCubes (q : ℕ) : RawChain →ₗ[ℤ] RawChain := by
  classical
  exact Finsupp.linearCombination ℤ (fun c =>
    if IsCube c ∧ degree c = q then basis c else 0)

@[simp] theorem restrictCubes_basis (q : ℕ) (c : RawCube) :
    restrictCubes q (basis c) = if IsCube c ∧ degree c = q then basis c else 0 := by
  classical
  simp [restrictCubes,basis]

theorem restrictCubes_coeff (q : ℕ) (x : RawChain) (d : RawCube)
    (hd : IsCube d ∧ degree d = q) : restrictCubes q x d = x d := by
  classical
  have h : (Finsupp.lapply d : RawChain →ₗ[ℤ] ℤ).comp (restrictCubes q) =
      (Finsupp.lapply d : RawChain →ₗ[ℤ] ℤ) := by
    apply Finsupp.lhom_ext
    intro c n
    have hs : Finsupp.single c n = n • basis c := by simp [basis]
    change restrictCubes q (Finsupp.single c n) d = (Finsupp.single c n) d
    rw [hs,map_smul,restrictCubes_basis]
    by_cases hc : c = d
    · subst c
      simp [hd]
    · by_cases hv : IsCube c ∧ degree c = q <;>
        simp [hc,Ne.symm hc,hv,basis,Finsupp.single_apply]
  exact LinearMap.congr_fun h x

/-- A verified mod-six-zero projected transpose suffices to establish the
cocycle on every original three-chain, including outside the bounding support. -/
theorem cocycle_of_projected_transpose
    (checked : ∀ d : RawCube, modSix (restrictCubes 3 (coBoundary phiVector) d) = 0)
    (x : RawChain) (hx : x ∈ Chains 3) : phi (boundary x) = 0 := by
  rw [phi_eq_pairing 2 _ (boundary_mem_chains 2 x hx),← pairing_coBoundary]
  have hker : x ∈ LinearMap.ker (modSix.comp (pairing (coBoundary phiVector))) := by
    apply map_mem_supported _ LinearMap.id ?_ x hx
    intro c hc
    change IsCube c ∧ degree c = 3 at hc
    change modSix (pairing (coBoundary phiVector) (basis c)) = 0
    rw [pairing_right_basis,← restrictCubes_coeff 3 _ c hc]
    exact checked c
  exact hker

end Paper23.CertificateChecks
