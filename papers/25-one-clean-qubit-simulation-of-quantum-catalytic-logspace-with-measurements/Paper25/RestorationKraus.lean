import Paper25.RestorationChoi
import Paper25.SourceChannels

/-! Lemma 2 for an explicit rectangular Kraus map, and therefore for the source
channel after its initialized work input is fixed. -/
noncomputable section
open scoped ComplexOrder ComplexConjugate
namespace Paper25

/-- A finite rectangular Kraus family acts on all input operators. -/
def rectangularKrausMap {ι ο κ : Type*} [Fintype ι] [Fintype κ]
    (K : κ → Matrix ο ι ℂ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ where
  toFun X := ∑ r, K r * X * (K r).conjTranspose
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

/-- The Choi positivity used in the restoration theorem follows from the actual
Kraus action; it is not an extra product-form hypothesis. -/
theorem restorationChoi_rectangularKrausMap_posSemidef {W V κ : Type*}
    [Fintype W] [Fintype V] [Fintype κ] [DecidableEq V]
    (K : κ → Matrix (W × V) V ℂ) :
    (restorationChoi (rectangularKrausMap K)).PosSemidef := by
  classical
  have h := (krausChoi_posSemidef K).submatrix
    (fun p : W × (V × V) => ((p.1,p.2.1),p.2.2))
  convert h using 1
  ext p q
  simp [restorationChoi, rectangularKrausMap, krausChoi, Matrix.sum_apply, Matrix.mul_apply, Matrix.single, ite_and]

/-- **Lemma 2 for Kraus semantics.** A completely positive map restoring the
catalyst marginal of every state has one fixed work state and acts as tensoring
with that state on every operator. -/
theorem lemma_2_kraus_restoration_generic {W V κ : Type*}
    [Fintype W] [Fintype V] [Fintype κ] [DecidableEq W] [DecidableEq V]
    (v₀ : V) (K : κ → Matrix (W × V) V ℂ)
    (hrestore : ∀ ρ, IsDensity ρ →
      workPartialTrace (rectangularKrausMap K ρ) = ρ) :
    ∃ η : Matrix W W ℂ, IsDensity η ∧
      ∀ X, rectangularKrausMap K X = Matrix.kronecker η X :=
  lemma_2_from_marginal_restoration_generic v₀ (rectangularKrausMap K)
    (restorationChoi_rectangularKrausMap_posSemidef K) hrestore

/-- Numeric-index version of the Kraus restoration theorem. -/
theorem lemma_2_kraus_restoration {k d : ℕ} (hd : 0 < d) {κ : Type*} [Fintype κ]
    (K : κ → Matrix (Fin k × Fin d) (Fin d) ℂ)
    (hrestore : ∀ ρ, IsDensity ρ →
      workPartialTrace (rectangularKrausMap K ρ) = ρ) :
    ∃ η : Matrix (Fin k) (Fin k) ℂ, IsDensity η ∧
      ∀ X, rectangularKrausMap K X = Matrix.kronecker η X :=
  lemma_2_kraus_restoration_generic ⟨0,hd⟩ K hrestore

/-- Fixing the initialized work input gives a rectangular Kraus family from
catalyst to work plus catalyst. -/
def preparedKraus {W V : Type*} [Fintype W] [Fintype V]
    [DecidableEq W] [DecidableEq V]
    (C : KrausChannel (W × V)) (w₀ : W) : C.Outcome → Matrix (W × V) V ℂ :=
  fun r a i => C.kraus r a (w₀,i)

/-- Preparing a unit basis vector preserves Kraus completeness, so the
rectangular prepared map is trace preserving independently of restoration. -/
theorem preparedKraus_complete {W V : Type*} [Fintype W] [Fintype V]
    [DecidableEq W] [DecidableEq V]
    (C : KrausChannel (W × V)) (w₀ : W) :
    (∑ r, (preparedKraus C w₀ r).conjTranspose * preparedKraus C w₀ r) =
      (1 : Matrix V V ℂ) := by
  classical
  ext i j
  have hc := congrArg (fun M : Matrix (W × V) (W × V) ℂ => M (w₀,i) (w₀,j)) C.complete
  simpa [preparedKraus, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply] using hc

/-- The prepared Kraus action is exactly the source channel on its clean work
input, for every catalyst operator. -/
theorem preparedKraus_action {W V : Type*} [Fintype W] [Fintype V]
    [DecidableEq W] [DecidableEq V]
    (C : KrausChannel (W × V)) (w₀ : W) (X : Matrix V V ℂ) :
    rectangularKrausMap (preparedKraus C w₀) X =
      C.act (Matrix.kronecker (Matrix.single w₀ w₀ 1) X) := by
  classical
  ext a b
  simp [rectangularKrausMap, preparedKraus, KrausChannel.act, Matrix.sum_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap, Matrix.single,
    Matrix.conjTranspose_apply, ite_and, Finset.sum_mul]

/-- Exact restoration of the actual source channel with a clean initialized
work input gives a single density operator on the entire final work register. -/
theorem lemma_2_source_channel_restoration {W V : Type*} [Fintype W] [Fintype V]
    [DecidableEq W] [DecidableEq V]
    (C : KrausChannel (W × V)) (w₀ : W) (v₀ : V)
    (hrestore : ∀ ρ, IsDensity ρ →
      workPartialTrace (C.act (Matrix.kronecker (Matrix.single w₀ w₀ 1) ρ)) = ρ) :
    ∃ η : Matrix W W ℂ, IsDensity η ∧ ∀ X,
      C.act (Matrix.kronecker (Matrix.single w₀ w₀ 1) X) = Matrix.kronecker η X := by
  obtain ⟨η,hη,hprod⟩ := lemma_2_kraus_restoration_generic v₀ (preparedKraus C w₀)
    (by intro ρ hρ; rw [preparedKraus_action]; exact hrestore ρ hρ)
  exact ⟨η,hη,fun X => by rw [← preparedKraus_action]; exact hprod X⟩

end Paper25
