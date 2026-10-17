import PUT.CollisionQuerySimulation

/-! # Query compilation with arbitrary finite workspace -/
noncomputable section
namespace PUT.CollisionQuerySimulation
open PUT.QueryModel PUT.CollisionCircuit

variable {D : ℕ} [NeZero D]
variable {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]

/-- The canonical regrouping of two finite orthonormal registers. -/
def pairCurry : EuclideanSpace ℂ (I × B) ≃ₗᵢ[ℂ] Register I (EuclideanSpace ℂ B) :=
  (lift (show (I × B) ≃ (i : I) × B from
    { toFun := fun ⟨i,b⟩ => ⟨i,b⟩
      invFun := fun ⟨i,b⟩ => (i,b)
      left_inv := by rintro ⟨i,b⟩; rfl
      right_inv := by rintro ⟨i,b⟩; rfl })).trans
    (LinearIsometryEquiv.piLpCurry ℂ 2 (fun _ _ => ℂ))

def workspaceUnitary (U : EuclideanSpace ℂ B ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) :
    EuclideanSpace ℂ (I × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (I × B) :=
  ((pairCurry (I := I) (B := B)).trans (withWorkspace U)).trans
    (pairCurry (I := I) (B := B)).symm

@[simp] theorem workspaceUnitary_trans (U V : EuclideanSpace ℂ B ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) :
    workspaceUnitary (I := I) (U.trans V) =
      (workspaceUnitary (I := I) U).trans (workspaceUnitary (I := I) V) := by
  ext v ⟨i,b⟩
  rfl

@[simp] theorem workspaceUnitary_inverse (U : EuclideanSpace ℂ B ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) :
    workspaceUnitary (I := I) U.symm = (workspaceUnitary (I := I) U).symm := by
  simp only [workspaceUnitary, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.symm_symm, withWorkspace,
    LinearIsometryEquiv.piLpCongrRight_symm]
  rfl

/-- Regroup workspace, source, and the two standard-query registers. -/
def queryWorkspaceCurry : QuerySpace (I × B) D ≃ₗᵢ[ℂ] Register I (QuerySpace B D) :=
  (lift (Equiv.prodAssoc I B (Fin D × Fin D))).trans pairCurry

def queryWorkspaceUnitary (U : QuerySpace B D ≃ₗᵢ[ℂ] QuerySpace B D) :
    QuerySpace (I × B) D ≃ₗᵢ[ℂ] QuerySpace (I × B) D :=
  ((queryWorkspaceCurry (I := I) (B := B) (D := D)).trans (withWorkspace U)).trans
    (queryWorkspaceCurry (I := I) (B := B) (D := D)).symm

set_option maxRecDepth 4096 in
@[simp] theorem queryWorkspaceUnitary_trans (U V : QuerySpace B D ≃ₗᵢ[ℂ] QuerySpace B D) :
    queryWorkspaceUnitary (I := I) (U.trans V) =
      (queryWorkspaceUnitary (I := I) U).trans (queryWorkspaceUnitary (I := I) V) := by
  ext v ⟨⟨i,b⟩,a,z⟩
  rfl

@[simp] theorem queryWorkspaceUnitary_inverse (U : QuerySpace B D ≃ₗᵢ[ℂ] QuerySpace B D) :
    queryWorkspaceUnitary (I := I) U.symm = (queryWorkspaceUnitary (I := I) U).symm := by
  simp only [queryWorkspaceUnitary, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.symm_symm, withWorkspace,
    LinearIsometryEquiv.piLpCongrRight_symm]
  rfl

@[simp] theorem queryWorkspaceUnitary_standard (f : Fin D → Fin D) :
    queryWorkspaceUnitary (I := I) (lift (standard (B := B) f)) =
      lift (standard (B := I × B) f) := by
  ext v ⟨⟨i,b⟩,a,z⟩
  rfl

def Gate.workspace : Gate B D → Gate (I × B) D
  | .free U => .free (queryWorkspaceUnitary U)
  | .query q => .query q

def Program.workspace (w : Program B D) : Program (I × B) D := w.map Gate.workspace

@[simp] theorem Gate.workspace_operation (g : Gate B D) (f : Fin D → Fin D) :
    (g.workspace (I := I)).operation f = queryWorkspaceUnitary (g.operation f) := by
  cases g with
  | free U => rfl
  | query q =>
    cases q <;> simp only [Gate.workspace, Gate.operation, queryUnitary,
      queryWorkspaceUnitary_inverse, queryWorkspaceUnitary_standard]

@[simp] theorem Program.workspace_operation (w : Program B D) (f : Fin D → Fin D) :
    (w.workspace (I := I)).operation f = queryWorkspaceUnitary (w.operation f) := by
  induction w with
  | nil => ext v ⟨⟨i,b⟩,a,z⟩; rfl
  | cons g w hw =>
    unfold Program.workspace at hw
    simp only [Program.workspace, List.map_cons, Program.operation,
      Gate.workspace_operation, hw, queryWorkspaceUnitary_trans]

@[simp] theorem Program.workspace_queries (w : Program B D) :
    (w.workspace (I := I)).queries = w.queries := by
  simp only [Program.workspace, Program.queries, List.map_map]
  congr 2
  funext g
  cases g <;> rfl

/-- Clean standard-query ancillas commute with all workspace regroupings. -/
theorem queryWorkspaceCurry_clean (v : EuclideanSpace ℂ (I × B)) (i : I) :
    queryWorkspaceCurry (clean (D := D) v) i =
      clean (D := D) (pairCurry v i) := by
  ext ⟨b,a,z⟩
  change clean v ((i,b),a,z) = clean (pairCurry v i) (b,a,z)
  rw [clean_coordinate, clean_coordinate]
  rfl

/-- Arbitrary finite workspace adds no function queries. -/
def Implements.workspace {U} {m : ℕ} (h : Implements (B := B) (D := D) U m) :
    Implements (B := I × B) (fun f => workspaceUnitary (I := I) (U f)) m where
  program := h.program.workspace
  count := by rw [Program.workspace_queries, h.count]
  correct := by
    intro f v
    rw [Program.workspace_operation]
    apply (queryWorkspaceCurry (I := I) (B := B) (D := D)).injective
    simp only [queryWorkspaceUnitary, LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.apply_symm_apply]
    ext i : 1
    change h.program.operation f (queryWorkspaceCurry (clean v) i) = _
    rw [queryWorkspaceCurry_clean, h.correct, queryWorkspaceCurry_clean]
    congr 1

end PUT.CollisionQuerySimulation
