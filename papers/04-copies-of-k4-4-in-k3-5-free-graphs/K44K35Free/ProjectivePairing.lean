import K44K35Free.Geometry
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The actual polarity and projective pairing maps on the paper's planes. -/
noncomputable section
namespace K44K35Free.Geometry
open Module Submodule

variable {F : Type*} [Field F]

def dotForm : LinearMap.BilinForm F (V F) := dotProductBilin F F

@[simp] theorem dotForm_apply (v w : V F) : dotForm v w = dotProduct v w := rfl

theorem dotForm_symm : (dotForm (F := F)).IsSymm := by
  exact ⟨fun v w => dotProduct_comm v w⟩

theorem dotForm_nondegenerate : (dotForm (F := F)).Nondegenerate := by
  intro v hv
  funext i
  have h := hv (Pi.single i 1)
  simpa [dotForm_apply, dotProduct_single] using h

/-- Orthogonal complementation maps projective planes to projective planes. -/
def polar (E : Plane F) : Plane F :=
  ⟨dotForm.orthogonal E.val, by
    rw [LinearMap.BilinForm.finrank_orthogonal dotForm_nondegenerate dotForm_symm.isRefl]
    simp [E.property, V]⟩

@[simp] theorem mem_polar (E : Plane F) (v : V F) :
    v ∈ (polar E).val ↔ ∀ w ∈ E.val, dotProduct w v = 0 := Iff.rfl

@[simp] theorem polar_polar (E : Plane F) : polar (polar E) = E := by
  apply Subtype.ext
  exact LinearMap.BilinForm.orthogonal_orthogonal dotForm_nondegenerate dotForm_symm.isRefl E.val

def polarEquiv : Plane F ≃ Plane F where
  toFun := polar
  invFun := polar
  left_inv := polar_polar
  right_inv := polar_polar

/-- The projective action of an invertible linear representative. -/
def mapPlane (T : V F ≃ₗ[F] V F) (E : Plane F) : Plane F :=
  ⟨E.val.map T.toLinearMap, by rw [T.finrank_map_eq]; exact E.property⟩

@[simp] theorem mem_mapPlane (T : V F ≃ₗ[F] V F) (E : Plane F) (v : V F) :
    v ∈ (mapPlane T E).val ↔ T.symm v ∈ E.val := by
  change v ∈ E.val.map T.toLinearMap ↔ _
  rw [Submodule.map_equiv_eq_comap_symm]
  rfl

@[simp] theorem mapPlane_symm (T : V F ≃ₗ[F] V F) (E : Plane F) :
    mapPlane T.symm (mapPlane T E) = E := by
  apply Subtype.ext
  ext v
  simp

@[simp] theorem mapPlane_refl (E : Plane F) : mapPlane (LinearEquiv.refl F (V F)) E = E := by
  apply Subtype.ext
  ext v
  simp

@[simp] theorem mapPlane_trans (T U : V F ≃ₗ[F] V F) (E : Plane F) :
    mapPlane (T.trans U) E = mapPlane U (mapPlane T E) := by
  apply Subtype.ext
  ext v
  simp

def mapPlaneEquiv (T : V F ≃ₗ[F] V F) : Plane F ≃ Plane F where
  toFun := mapPlane T
  invFun := mapPlane T.symm
  left_inv := mapPlane_symm T
  right_inv := mapPlane_symm T.symm

/-- Controlled left plane for a type-I block. -/
def leftDual (T : V F ≃ₗ[F] V F) : Plane F ≃ Plane F :=
  (mapPlaneEquiv T).trans polarEquiv

/-- Controlled right plane for a type-II block; the inverse left-plane pairing. -/
def rightDual (T : V F ≃ₗ[F] V F) : Plane F ≃ Plane F :=
  (leftDual T).symm

@[simp] theorem leftDual_apply (T : V F ≃ₗ[F] V F) (E : Plane F) :
    leftDual T E = polar (mapPlane T E) := rfl

@[simp] theorem rightDual_apply (T : V F ≃ₗ[F] V F) (E : Plane F) :
    rightDual T E = mapPlane T.symm (polar E) := rfl

/-- Equation (15), on the actual affine labels of S. -/
def Incidence (α : F) (c : Quartic F) (T : V F ≃ₗ[F] V F)
    (p r : Param F) : Prop := dotProduct (point α c p) (T (point α c r)) = 0

/-- Equal-dimensional subspaces are in the same orbit of the full linear group. -/
theorem exists_linearEquiv_map_eq {W : Type*} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (P Q : Submodule F W)
    (hdim : finrank F P = finrank F Q) :
    ∃ T : W ≃ₗ[F] W, P.map T.toLinearMap = Q := by
  obtain ⟨P', hP⟩ := P.exists_isCompl
  obtain ⟨Q', hQ⟩ := Q.exists_isCompl
  have hdim' : finrank F P' = finrank F Q' := by
    have h1 := finrank_add_eq_of_isCompl hP
    have h2 := finrank_add_eq_of_isCompl hQ
    omega
  let e : P ≃ₗ[F] Q := LinearEquiv.ofFinrankEq P Q hdim
  let e' : P' ≃ₗ[F] Q' := LinearEquiv.ofFinrankEq P' Q' hdim'
  let a := prodEquivOfIsCompl P P' hP
  let b := prodEquivOfIsCompl Q Q' hQ
  let T := a.symm.trans ((e.prodCongr e').trans b)
  have hT (p : P) : T p = (e p : W) := by
    simp [T, a, b, LinearEquiv.trans_apply,
      prodEquivOfIsCompl_symm_apply_left, coe_prodEquivOfIsCompl']
  refine ⟨T, ?_⟩
  apply le_antisymm
  · rintro v ⟨p, hp, rfl⟩
    have := (e ⟨p, hp⟩).property
    simpa only [← hT ⟨p, hp⟩] using this
  · intro q hq
    obtain ⟨p, hp⟩ := e.surjective ⟨q, hq⟩
    refine ⟨p, p.property, ?_⟩
    change T p = q
    rw [hT, hp]

/-- Transitivity on the actual projective planes, as used in (18), (22), (23). -/
theorem mapPlane_transitive (E D : Plane F) :
    ∃ T : V F ≃ₗ[F] V F, mapPlane T E = D := by
  obtain ⟨T, hT⟩ := exists_linearEquiv_map_eq E.val D.val (E.property.trans D.property.symm)
  exact ⟨T, Subtype.ext hT⟩

end K44K35Free.Geometry
