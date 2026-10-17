import Paper25.RestorationKraus
import Paper25.SourceHistory

/-! From the actual source channel and its marginal restoration hypothesis to
the exact Liouville column identity (3), with the doubled registers reordered
as `W,Wbar,C,Cbar`. -/
noncomputable section
namespace Paper25

/-- Operator coordinates for an arbitrary register type. -/
def operatorVec {V : Type*} (X : Matrix V V ℂ) : V × V → ℂ := fun p => X p.1 p.2

/-- The generic rectangular block column `|ω⟩ ⊗ I`. -/
def operatorKronColumn {A B : Type*} [DecidableEq B] (ω : A → ℂ) :
    Matrix (A × B) B ℂ := fun p j => ω p.1 * if p.2 = j then 1 else 0

/-- Source Liouville matrix in doubled-work, doubled-catalyst order. -/
def sourceLiouville {W V : Type*} [Fintype W] [Fintype V]
    [DecidableEq W] [DecidableEq V] (C : KrausChannel (W × V)) :
    Matrix ((W × W) × (V × V)) ((W × W) × (V × V)) ℂ :=
  fun p q => C.liouville ((p.1.1,p.2.1),(p.1.2,p.2.2))
    ((q.1.1,q.2.1),(q.1.2,q.2.2))

/-- Reordering the doubled registers is a matrix reindexing. -/
lemma sourceLiouville_eq_submatrix {W V : Type*} [Fintype W] [Fintype V]
    [DecidableEq W] [DecidableEq V] (C : KrausChannel (W × V)) :
    sourceLiouville C = C.liouville.submatrix
      (reshuffleEquiv (α := W) (β := W) (γ := V) (δ := V))
      (reshuffleEquiv (α := W) (β := W) (γ := V) (δ := V)) := rfl

/-- Finite enumeration followed by the fixed doubled-register reordering. -/
lemma sourceLiouville_reindex_eq_raw {W V κ : Type*} [Fintype W] [Fintype V]
    [DecidableEq W] [DecidableEq V]
    (C : KrausChannel (W × V)) (e : κ ≃ (W × W) × (V × V)) :
    (sourceLiouville C).submatrix e e = C.liouville.submatrix
      (e.trans (reshuffleEquiv (α := W) (β := W) (γ := V) (δ := V)))
      (e.trans (reshuffleEquiv (α := W) (β := W) (γ := V) (δ := V))) := rfl

/-- Every consecutive reordered source-channel product has the genuine CPTP
Frobenius bound, in the exact coordinate system used by the reduction. -/
theorem sourceLiouville_cptpFrobBound {W V κ : Type*}
    [Fintype W] [Fintype V] [Fintype κ]
    [DecidableEq W] [DecidableEq V] [DecidableEq κ]
    (C : ℕ → KrausChannel (W × V)) (e : κ ≃ (W × W) × (V × V)) (T : ℕ) :
    CPTPFrobBound (fun t => (sourceLiouville (C t)).submatrix e e) T
      (Fintype.card W * Fintype.card V) := by
  have h := KrausChannel.cptpFrobBound_reindex C
    (e.trans (reshuffleEquiv (α := W) (β := W) (γ := V) (δ := V))) T
  simpa only [sourceLiouville_reindex_eq_raw, Fintype.card_prod] using h

/-- The doubled-register reordering respects actual channel composition. -/
theorem sourceLiouville_comp {W V : Type*} [Fintype W] [Fintype V]
    [DecidableEq W] [DecidableEq V] (C D : KrausChannel (W × V)) :
    sourceLiouville (C.comp D) = sourceLiouville C * sourceLiouville D := by
  rw [sourceLiouville_eq_submatrix, C.liouville_comp D,
    sourceLiouville_eq_submatrix C, sourceLiouville_eq_submatrix D,
    Matrix.submatrix_mul_equiv]


/-- The reordered source matrix is the actual temporal channel product. -/
theorem sourceLiouville_sequence {W V : Type*} [Fintype W] [Fintype V]
    [DecidableEq W] [DecidableEq V]
    (C : ℕ → KrausChannel (W × V)) (start len : ℕ) :
    sourceLiouville (KrausChannel.sequence C start len) =
      chainProd (fun t => sourceLiouville (C t)) start len := by
  induction len with
  | zero =>
    rw [KrausChannel.sequence, sourceLiouville_eq_submatrix,
      KrausChannel.liouville_identity, chainProd_zero]
    exact Matrix.submatrix_one_equiv _
  | succ len ih =>
    rw [KrausChannel.sequence, sourceLiouville_comp, ih, chainProd_succ]

/-- Finite enumeration commutes with the time-ordered matrix product. -/
lemma chainProd_submatrix_equiv {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (S : ℕ → Matrix A A ℂ) (e : B ≃ A) (start len : ℕ) :
    chainProd (fun t => (S t).submatrix e e) start len =
      (chainProd S start len).submatrix e e := by
  induction len with
  | zero => simp only [chainProd_zero]; exact (Matrix.submatrix_one_equiv e).symm
  | succ len ih => rw [chainProd_succ, chainProd_succ, ih, Matrix.submatrix_mul_equiv]


lemma operatorKronColumn_initial_mul {W V : Type*} [Fintype W] [Fintype V]
    [DecidableEq W] [DecidableEq V]
    (S : Matrix ((W × W) × (V × V)) ((W × W) × (V × V)) ℂ)
    (w₀ : W) (p : (W × W) × (V × V)) (j : V × V) :
    (S * operatorKronColumn (B := V × V) (operatorVec (Matrix.single w₀ w₀ (1 : ℂ)))) p j =
      S p ((w₀,w₀),j) := by
  classical
  simp [Matrix.mul_apply, operatorKronColumn, operatorVec, Matrix.single,
    Fintype.sum_prod_type, ite_and, Prod.ext_iff]

/-- Product form of the true source channel implies equation (3). -/
theorem sourceLiouville_restoration_column {W V : Type*} [Fintype W] [Fintype V]
    [DecidableEq W] [DecidableEq V]
    (C : KrausChannel (W × V)) (w₀ : W) (η : Matrix W W ℂ)
    (hproduct : ∀ X,
      C.act (Matrix.kronecker (Matrix.single w₀ w₀ 1) X) = Matrix.kronecker η X) :
    sourceLiouville C * operatorKronColumn (operatorVec (Matrix.single w₀ w₀ 1)) =
      operatorKronColumn (operatorVec η) := by
  classical
  ext p j
  rw [operatorKronColumn_initial_mul]
  change C.liouville ((p.1.1,p.2.1),(p.1.2,p.2.2)) ((w₀,j.1),(w₀,j.2)) = _
  rw [← C.act_single]
  have hs : Matrix.single (w₀,j.1) (w₀,j.2) (1 : ℂ) =
      Matrix.kronecker (Matrix.single w₀ w₀ 1) (Matrix.single j.1 j.2 1) := by
    rw [Matrix.kronecker, Matrix.single_kronecker_single]
    simp
  rw [hs, hproduct]
  simp [Matrix.kronecker, Matrix.kroneckerMap, operatorKronColumn, operatorVec,
    Matrix.single, Prod.ext_iff, eq_comm]

/-- Equation (3) is invariant under finite enumeration of the doubled register
coordinates. This is the `ExactRestoration` form consumed by the history trace
identity. -/
theorem exactRestoration_of_operator_column {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] {m n : ℕ}
    (S : Matrix (A × B) (A × B) ℂ) (ω η : A → ℂ)
    (h : S * operatorKronColumn ω = operatorKronColumn η)
    (eA : Fin m ≃ A) (eB : Fin n ≃ B) :
    ExactRestoration (S.submatrix (eA.prodCongr eB) (eA.prodCongr eB))
      (ω ∘ eA) (η ∘ eA) := by
  classical
  have hcol (v : A → ℂ) :
      (operatorKronColumn (B := B) v).submatrix (eA.prodCongr eB) eB =
        kronColId (v ∘ eA) := by
    ext p j
    simp [operatorKronColumn, kronColId, eB.injective.eq_iff]
  unfold ExactRestoration
  rw [← hcol ω, Matrix.submatrix_mul_equiv, h, hcol η]

/-- Full source restoration, including its density work output and the exact
Liouville identity required in the catalytic trace argument. -/
theorem lemma_2_source_exactRestoration {W V : Type*} [Fintype W] [Fintype V]
    [DecidableEq W] [DecidableEq V] {m n : ℕ}
    (C : KrausChannel (W × V)) (w₀ : W) (v₀ : V)
    (hrestore : ∀ ρ, IsDensity ρ →
      workPartialTrace (C.act (Matrix.kronecker (Matrix.single w₀ w₀ 1) ρ)) = ρ)
    (eW : Fin m ≃ W × W) (eV : Fin n ≃ V × V) :
    ∃ η : Matrix W W ℂ, IsDensity η ∧
      (∀ X, C.act (Matrix.kronecker (Matrix.single w₀ w₀ 1) X) = Matrix.kronecker η X) ∧
      ExactRestoration ((sourceLiouville C).submatrix (eW.prodCongr eV) (eW.prodCongr eV))
        (operatorVec (Matrix.single w₀ w₀ 1) ∘ eW) (operatorVec η ∘ eW) := by
  obtain ⟨η,hη,hprod⟩ := lemma_2_source_channel_restoration C w₀ v₀ hrestore
  exact ⟨η,hη,hprod,exactRestoration_of_operator_column _ _ _
    (sourceLiouville_restoration_column C w₀ η hprod) eW eV⟩

/-- The exact restoration hypothesis consumed by the history inverse follows
from the true final source channel's marginal restoration on density operators. -/
theorem lemma_2_source_history_exactRestoration {W V : Type*}
    [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V] {m n T : ℕ}
    (C : ℕ → KrausChannel (W × V)) (w₀ : W) (v₀ : V)
    (hrestore : ∀ ρ, IsDensity ρ →
      workPartialTrace ((KrausChannel.sequence C 0 T).act
        (Matrix.kronecker (Matrix.single w₀ w₀ 1) ρ)) = ρ)
    (eW : Fin m ≃ W × W) (eV : Fin n ≃ V × V) :
    ∃ η : Matrix W W ℂ, IsDensity η ∧
      ExactRestoration (chainProd (fun t => (sourceLiouville (C t)).submatrix
        (eW.prodCongr eV) (eW.prodCongr eV)) 0 T)
        (operatorVec (Matrix.single w₀ w₀ 1) ∘ eW) (operatorVec η ∘ eW) := by
  obtain ⟨η,hη,hprod,hcol⟩ := lemma_2_source_exactRestoration
    (KrausChannel.sequence C 0 T) w₀ v₀ hrestore eW eV
  refine ⟨η,hη,?_⟩
  rw [sourceLiouville_sequence] at hcol
  rw [chainProd_submatrix_equiv]
  exact hcol

end Paper25
