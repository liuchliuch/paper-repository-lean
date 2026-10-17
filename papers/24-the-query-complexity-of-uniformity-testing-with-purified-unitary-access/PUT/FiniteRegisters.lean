import PUT.Main
import PUT.ReflectionOracle
import PUT.OperatorBridge
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Finite registers for the paper's hard instances

The integer choice of garbage size, polynomial physical dimension, and
actual isometric embedding into a qubit basis are proved here.  The generic
unitary extension acts as minus the identity on unused dimensions.
-/

noncomputable section
namespace PUT.FiniteRegisters
open MeasureTheory
open scoped InnerProductSpace

/-- The actual integer garbage dimension selected in Section 4. -/
def garbageSize (A : ℝ) : ℕ := ⌈16 * A ^ 2 * LA A⌉₊

theorem LA_le_four_mul {A : ℝ} (hA : 1 ≤ A) : LA A ≤ 4 * A := by
  have hs : 1 ≤ Real.sqrt A := (Real.one_le_sqrt).mpr hA
  have hsq := Real.sq_sqrt (show 0 ≤ A by linarith)
  unfold LA
  nlinarith [sq_nonneg (Real.sqrt A - 1)]

theorem garbageSize_sufficient {A : ℝ} (_hA : 1 ≤ A) :
    16 * A ^ 2 * LA A ≤ (garbageSize A : ℝ) := Nat.le_ceil _

theorem garbageSize_pos {A : ℝ} (hA : 1 ≤ A) : 0 < garbageSize A := by
  have hLA : 0 < LA A := by unfold LA; positivity
  have h := garbageSize_sufficient hA
  have hpos : (0 : ℝ) < garbageSize A := by nlinarith [sq_nonneg (A - 1)]
  exact_mod_cast hpos

theorem garbageSize_le_cubic {A : ℝ} (hA : 1 ≤ A) :
    (garbageSize A : ℝ) ≤ 64 * A ^ 3 + 1 := by
  have hnonneg : 0 ≤ 16 * A ^ 2 * LA A := by unfold LA; positivity
  have hc := (Nat.ceil_lt_add_one hnonneg).le
  have hl := mul_le_mul_of_nonneg_left (LA_le_four_mul hA) (by positivity : 0 ≤ 16 * A ^ 2)
  change (⌈16 * A ^ 2 * LA A⌉₊ : ℝ) ≤ _
  nlinarith only [hc, hl]

theorem cutoffLow_le_dimension {a d : ℝ} (ha : 0 < a) (hd : 0 < d) (had : a ≤ d) :
    cutoffLow a d ≤ max d a :=
  ((div_le_one hd).mp (low_regime_div a d ha hd had)).trans (le_max_left _ _)

theorem cutoffHigh_le_max (a d : ℝ) : cutoffHigh a d ≤ max d a := le_max_right _ _

theorem cutoffLow_one_le {a d : ℝ} (ha : 1 ≤ a) (hd : 1 ≤ d) : 1 ≤ cutoffLow a d := by
  unfold cutoffLow
  apply Real.one_le_rpow
  · have ha2 : (1 : ℝ) ≤ a ^ 2 := one_le_pow₀ ha
    exact one_le_mul_of_one_le_of_one_le hd ha2
  · norm_num

theorem cutoffHigh_one_le {a d : ℝ} (ha : 1 ≤ a) : 1 ≤ cutoffHigh a d := ha

/-- The optional label copy has `d² M` output basis vectors, and one
additional designated input basis vector. -/
def copiedDimension (d M : ℕ) : ℕ := 1 + d ^ 2 * M

def accuracySize (ε : ℝ) : ℕ := ⌈1 / ε⌉₊

theorem accuracySize_one_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ accuracySize ε := by
  have he : (1 : ℝ) ≤ 1 / ε := (one_le_div hε).mpr hε1
  have hc : (1 : ℝ) ≤ accuracySize ε := he.trans (Nat.le_ceil _)
  exact_mod_cast hc

theorem scale_le_accuracySize_sq {ε : ℝ} (hε : 0 < ε) :
    dirichletScale ε ≤ (accuracySize ε : ℝ) ^ 2 := by
  have hc : (1 / ε : ℝ) ≤ accuracySize ε := Nat.le_ceil _
  have hn : (0 : ℝ) ≤ accuracySize ε := Nat.cast_nonneg _
  have hi : 0 ≤ (1 / ε : ℝ) := by positivity
  have hsq : (1 / ε : ℝ) ^ 2 ≤ (accuracySize ε : ℝ) ^ 2 :=
    pow_le_pow_left₀ hi hc 2
  have hbase : (1 / (48 * ε) : ℝ) ≤ 1 / ε := by
    apply one_div_le_one_div_of_le hε
    linarith
  have hb0 : (0 : ℝ) ≤ 1 / (48 * ε) := by positivity
  have hsmall := pow_le_pow_left₀ hb0 hbase 2
  have hscale : dirichletScale ε = (1 / (48 * ε)) ^ 2 := by
    unfold dirichletScale
    simp only [zpow_neg, zpow_ofNat]
    rw [one_div, inv_pow]
  rw [hscale]
  exact hsmall.trans hsq

/-- A fixed polynomial dimension bound, including the optional copied
label. No asymptotic register estimate is assumed. -/
theorem copiedDimension_polynomial {d : ℕ} (hd : 2 ≤ d) {ε A : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hA : 1 ≤ A)
    (hAd : A ≤ max (d : ℝ) (dirichletScale ε)) :
    copiedDimension d (garbageSize A) ≤ 66 * d ^ 5 * accuracySize ε ^ 6 := by
  let n := accuracySize ε
  have hn : 1 ≤ n := accuracySize_one_le hε hε1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hscale : dirichletScale ε ≤ (n : ℝ) ^ 2 := scale_le_accuracySize_sq hε
  have hmax : max (d : ℝ) (dirichletScale ε) ≤ (d : ℝ) * (n : ℝ) ^ 2 := by
    apply max_le
    · nlinarith [sq_nonneg ((n : ℝ) - 1)]
    · have : (n : ℝ) ^ 2 ≤ (d : ℝ) * (n : ℝ) ^ 2 := by nlinarith [sq_nonneg (n : ℝ)]
      exact hscale.trans this
  have hAB : A ≤ (d : ℝ) * (n : ℝ) ^ 2 := hAd.trans hmax
  have hp : A ^ 3 ≤ ((d : ℝ) * (n : ℝ) ^ 2) ^ 3 :=
    pow_le_pow_left₀ (by linarith) hAB 3
  have hm := garbageSize_le_cubic hA
  have hm' : (garbageSize A : ℝ) ≤ 65 * (d : ℝ) ^ 3 * (n : ℝ) ^ 6 := by
    have hdn : (1 : ℝ) ≤ (d : ℝ) ^ 3 * (n : ℝ) ^ 6 := by
      have hd3 : (1 : ℝ) ≤ (d : ℝ) ^ 3 := one_le_pow₀ (by linarith)
      have hn6 : (1 : ℝ) ≤ (n : ℝ) ^ 6 := one_le_pow₀ hnR
      nlinarith
    nlinarith [hp]
  have hdn : (1 : ℝ) ≤ (d : ℝ) ^ 5 * (n : ℝ) ^ 6 := by
    have hd5 : (1 : ℝ) ≤ (d : ℝ) ^ 5 := one_le_pow₀ (by linarith)
    have hn6 : (1 : ℝ) ≤ (n : ℝ) ^ 6 := one_le_pow₀ hnR
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hm' (sq_nonneg (d : ℝ))
  have hreal : (1 : ℝ) + (d : ℝ) ^ 2 * (garbageSize A : ℝ) ≤
      66 * (d : ℝ) ^ 5 * (n : ℝ) ^ 6 := by nlinarith only [hmul, hdn]
  exact_mod_cast hreal

/-- A conservative explicit number of qubits, expressed with ceiling logs. -/
def qubits (d : ℕ) (ε : ℝ) : ℕ :=
  7 + 5 * Nat.clog 2 d + 6 * Nat.clog 2 (accuracySize ε)

theorem polynomial_le_qubit_capacity (d n : ℕ) :
    66 * d ^ 5 * n ^ 6 ≤ 2 ^ (7 + 5 * Nat.clog 2 d + 6 * Nat.clog 2 n) := by
  have hd := Nat.le_pow_clog (by norm_num : 1 < 2) d
  have hn := Nat.le_pow_clog (by norm_num : 1 < 2) n
  have hd5 := Nat.pow_le_pow_left hd 5
  have hn6 := Nat.pow_le_pow_left hn 6
  calc
    66 * d ^ 5 * n ^ 6 ≤ 128 * (2 ^ Nat.clog 2 d) ^ 5 * (2 ^ Nat.clog 2 n) ^ 6 := by
      gcongr
      norm_num
    _ = _ := by simp only [← pow_mul, pow_add]; ring

theorem copiedDimension_le_qubit_capacity {d : ℕ} (hd : 2 ≤ d) {ε A : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hA : 1 ≤ A)
    (hAd : A ≤ max (d : ℝ) (dirichletScale ε)) :
    copiedDimension d (garbageSize A) ≤ 2 ^ qubits d ε :=
  (copiedDimension_polynomial hd hε hε1 hA hAd).trans
    (polynomial_le_qubit_capacity d (accuracySize ε))

section CoordinateEmbedding
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Map a finite orthonormal basis injectively into another actual
Euclidean basis, extending linearly with zero unused coordinates. -/
def basisEmbedding (f : ι ↪ κ) : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ := by
  let b := EuclideanSpace.basisFun ι ℂ
  let c := EuclideanSpace.basisFun κ ℂ
  let L := b.toBasis.constr ℂ (fun i => c (f i))
  refine L.isometryOfOrthonormal (v := b.toBasis) b.orthonormal ?_
  have hfun : L ∘ b.toBasis = c ∘ f := by
    funext i
    exact b.toBasis.constr_basis ℂ _ i
  rw [hfun]
  exact c.orthonormal.comp f f.injective

omit [DecidableEq ι] [DecidableEq κ] in
theorem basisEmbedding_basis (f : ι ↪ κ) (i : ι) :
    basisEmbedding f (EuclideanSpace.basisFun ι ℂ i) = EuclideanSpace.basisFun κ ℂ (f i) := by
  change (EuclideanSpace.basisFun ι ℂ).toBasis.constr ℂ
    (fun j => EuclideanSpace.basisFun κ ℂ (f j)) (EuclideanSpace.basisFun ι ℂ i) = _
  exact (EuclideanSpace.basisFun ι ℂ).toBasis.constr_basis ℂ _ i

theorem basisEmbedding_single (f : ι ↪ κ) (i : ι) :
    basisEmbedding f (EuclideanSpace.single i 1) = EuclideanSpace.single (f i) 1 := by
  simpa only [EuclideanSpace.basisFun_apply] using basisEmbedding_basis f i

theorem basisEmbedding_expansion (f : ι ↪ κ) (x : EuclideanSpace ℂ ι) :
    basisEmbedding f x = ∑ i, x i • EuclideanSpace.single (f i) 1 := by
  conv_lhs => rw [← (EuclideanSpace.basisFun ι ℂ).sum_repr x]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, basisEmbedding_single]

end CoordinateEmbedding

/-- An actual isometric embedding of an `N`-dimensional physical space
into the computational basis of `q` qubits whenever `N ≤ 2^q`. -/
def qubitEmbedding (N q : ℕ) (h : N ≤ 2 ^ q) :
    EuclideanSpace ℂ (Fin N) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (2 ^ q)) :=
  basisEmbedding (Fin.castLEEmb h)

/-- Encoding any finite coordinate type into a qubit basis. -/
def finiteQubitEmbedding (ι : Type*) [Fintype ι] [DecidableEq ι]
    (q : ℕ) (h : Fintype.card ι ≤ 2 ^ q) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (2 ^ q)) :=
  basisEmbedding ((Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb h))

abbrev CopiedIndex (d M : ℕ) := Unit ⊕ (Fin d × Fin d × Fin M)
abbrev CopiedSpace (d M : ℕ) := EuclideanSpace ℂ (CopiedIndex d M)

theorem copiedIndex_card (d M : ℕ) : Fintype.card (CopiedIndex d M) = copiedDimension d M := by
  simp [CopiedIndex, copiedDimension, pow_two, mul_assoc]

/-- The paper's known coordinate injection, including the designated
input coordinate. -/
def copiedIndexEmbedding (d M : ℕ) : HQ d M ↪ CopiedIndex d M where
  toFun := Sum.map id (fun ij => garbageEmbed d M ij.1 ij.2)
  inj' := by
    exact Sum.map_injective.mpr ⟨Function.injective_id, garbageEmbed_injective d M⟩

def copyEmbedding (d M : ℕ) :
    QueryModel.PurificationSpace d M →ₗᵢ[ℂ] CopiedSpace d M :=
  basisEmbedding (copiedIndexEmbedding d M)

theorem copyEmbedding_basis (d M : ℕ) (q : HQ d M) :
    copyEmbedding d M (EuclideanSpace.single q 1) =
      EuclideanSpace.single (copiedIndexEmbedding d M q) 1 := by
  simpa only [copyEmbedding, EuclideanSpace.basisFun_apply] using
    basisEmbedding_basis (copiedIndexEmbedding d M) q

def copiedQubitEmbedding {d : ℕ} (hd : 2 ≤ d) {ε A : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hA : 1 ≤ A)
    (hAd : A ≤ max (d : ℝ) (dirichletScale ε)) :
    CopiedSpace d (garbageSize A) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (2 ^ qubits d ε)) :=
  finiteQubitEmbedding _ (qubits d ε) (by
    rw [copiedIndex_card]
    exact copiedDimension_le_qubit_capacity hd hε hε1 hA hAd)

/-- Conditional garbage vectors in different copied-label blocks are
orthogonal, for arbitrary complex garbage amplitudes. -/
def labelGarbageEmbedding {d M : ℕ} (i : Fin d) :
    EuclideanSpace ℂ (Fin M) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin d × Fin M) :=
  basisEmbedding ⟨fun j => (i, j), fun _ _ h => (Prod.mk.inj h).2⟩

theorem copied_garbage_orthogonal {d M : ℕ} {i k : Fin d} (hik : i ≠ k)
    (x y : EuclideanSpace ℂ (Fin M)) :
    inner ℂ (labelGarbageEmbedding i x) (labelGarbageEmbedding k y) = 0 := by
  unfold labelGarbageEmbedding
  rw [basisEmbedding_expansion, basisEmbedding_expansion]
  simp [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, hik]

theorem accuracy_clog_le_log {ε : ℝ} (hε : 0 < ε) :
    Nat.clog 2 (accuracySize ε) ≤ ⌈Real.logb 2 (1 / ε)⌉₊ := by
  apply (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).mpr
  unfold accuracySize
  apply Nat.ceil_le.mpr
  have hlog : Real.logb 2 (1 / ε) ≤ (⌈Real.logb 2 (1 / ε)⌉₊ : ℝ) := Nat.le_ceil _
  have hp := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < 1 / ε)).mp hlog
  simpa only [Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat] using hp

/-- The promised logarithmic oracle-qubit bound with explicit constants. -/
theorem qubits_log_bound {d : ℕ} (hd : 2 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (qubits d ε : ℝ) ≤ 18 + 5 * Real.logb 2 d + 6 * Real.logb 2 (1 / ε) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hi : (1 : ℝ) ≤ 1 / ε := (one_le_div hε).mpr hε1
  have hld : 0 ≤ Real.logb 2 d := Real.logb_nonneg (by norm_num) hdR
  have hle : 0 ≤ Real.logb 2 (1 / ε) := Real.logb_nonneg (by norm_num) hi
  have hceil_d := (Nat.ceil_lt_add_one hld).le
  have hceil_e := (Nat.ceil_lt_add_one hle).le
  have hclog := accuracy_clog_le_log hε
  have hclogR : (Nat.clog 2 (accuracySize ε) : ℝ) ≤
      (⌈Real.logb 2 (1 / ε)⌉₊ : ℝ) := by exact_mod_cast hclog
  have hdlog : ⌈Real.logb 2 (d : ℝ)⌉₊ = Nat.clog 2 d := Real.natCeil_logb_natCast 2 d
  rw [hdlog] at hceil_d
  unfold qubits
  push_cast
  linarith

section UnitaryExtension
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Conjugation on the embedded space and minus identity on its orthogonal
complement, as an actual continuous linear operator. -/
def unitaryExtensionMap (J : H →ₗᵢ[ℂ] K) (U : H ≃ₗᵢ[ℂ] H) : K →L[ℂ] K :=
  J.toContinuousLinearMap ∘L (U : H →L[ℂ] H) ∘L J.toContinuousLinearMap.adjoint +
    J.toContinuousLinearMap ∘L J.toContinuousLinearMap.adjoint - ContinuousLinearMap.id ℂ K

theorem unitaryExtensionMap_apply (J : H →ₗᵢ[ℂ] K) (U : H ≃ₗᵢ[ℂ] H) (y : K) :
    unitaryExtensionMap J U y =
      J (U (J.toContinuousLinearMap.adjoint y)) + J (J.toContinuousLinearMap.adjoint y) - y := rfl

theorem adjoint_unitaryExtension_apply (J : H →ₗᵢ[ℂ] K) (U : H ≃ₗᵢ[ℂ] H) (y : K) :
    J.toContinuousLinearMap.adjoint (unitaryExtensionMap J U y) =
      U (J.toContinuousLinearMap.adjoint y) := by
  simp only [unitaryExtensionMap_apply, map_add, map_sub,
    OperatorBridge.adjoint_preparation_apply]
  abel

theorem unitaryExtension_inverse_apply (J : H →ₗᵢ[ℂ] K) (U : H ≃ₗᵢ[ℂ] H) (y : K) :
    unitaryExtensionMap J U.symm (unitaryExtensionMap J U y) = y := by
  rw [unitaryExtensionMap_apply]
  simp only [adjoint_unitaryExtension_apply, LinearIsometryEquiv.symm_apply_apply]
  rw [unitaryExtensionMap_apply]
  abel

theorem unitaryExtensionMap_adjoint (J : H →ₗᵢ[ℂ] K) (U : H ≃ₗᵢ[ℂ] H) :
    (unitaryExtensionMap J U).adjoint = unitaryExtensionMap J U.symm := by
  ext y
  simp [unitaryExtensionMap, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_assoc]

def unitaryExtensionIsometry (J : H →ₗᵢ[ℂ] K) (U : H ≃ₗᵢ[ℂ] H) : K →ₗᵢ[ℂ] K :=
  { (unitaryExtensionMap J U).toLinearMap with
    norm_map' := (unitaryExtensionMap J U).norm_map_iff_adjoint_comp_self.mpr (by
      rw [unitaryExtensionMap_adjoint]
      ext y
      exact unitaryExtension_inverse_apply J U y) }

/-- The construction is an actual surjective unitary, rather than an
informal restriction to the image of the embedding. -/
def extendUnitary (J : H →ₗᵢ[ℂ] K) (U : H ≃ₗᵢ[ℂ] H) : K ≃ₗᵢ[ℂ] K :=
  LinearIsometryEquiv.ofSurjective (unitaryExtensionIsometry J U) (fun y =>
    ⟨unitaryExtensionMap J U.symm y, by
      simpa only [LinearIsometryEquiv.symm_symm] using unitaryExtension_inverse_apply J U.symm y⟩)

theorem extendUnitary_on_image (J : H →ₗᵢ[ℂ] K) (U : H ≃ₗᵢ[ℂ] H) (x : H) :
    extendUnitary J U (J x) = J (U x) := by
  change unitaryExtensionMap J U (J x) = _
  simp [unitaryExtensionMap_apply, OperatorBridge.adjoint_preparation_apply]

/-- The unused orthogonal coordinates receive the same known action `-I`
for every unknown oracle. -/
theorem extendUnitary_on_complement (J : H →ₗᵢ[ℂ] K) (U : H ≃ₗᵢ[ℂ] H) (y : K)
    (hy : ∀ x : H, inner ℂ (J x) y = 0) : extendUnitary J U y = -y := by
  have hja : J.toContinuousLinearMap.adjoint y = 0 := by
    apply ext_inner_left ℂ
    intro x
    rw [inner_zero_right, ContinuousLinearMap.adjoint_inner_right]
    exact hy x
  change unitaryExtensionMap J U y = _
  simp [unitaryExtensionMap_apply, hja]

theorem unitaryExtension_difference (J : H →ₗᵢ[ℂ] K) (U V : H ≃ₗᵢ[ℂ] H) :
    (extendUnitary J U : K →L[ℂ] K) - (extendUnitary J V : K →L[ℂ] K) =
      J.toContinuousLinearMap ∘L ((U : H →L[ℂ] H) - (V : H →L[ℂ] H)) ∘L
        J.toContinuousLinearMap.adjoint := by
  ext y
  change unitaryExtensionMap J U y - unitaryExtensionMap J V y = _
  simp only [unitaryExtensionMap_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub]
  abel

/-- Full-operator query differences cannot increase on adding unused qubit
coordinates. In particular, they vanish on the orthogonal complement. -/
theorem norm_unitaryExtension_difference_le (J : H →ₗᵢ[ℂ] K) (U V : H ≃ₗᵢ[ℂ] H) :
    ‖(extendUnitary J U : K →L[ℂ] K) - (extendUnitary J V : K →L[ℂ] K)‖ ≤
      ‖(U : H →L[ℂ] H) - (V : H →L[ℂ] H)‖ := by
  rw [unitaryExtension_difference]
  have hJ : ‖J.toContinuousLinearMap‖ ≤ 1 := J.norm_toContinuousLinearMap_le
  have hJa : ‖J.toContinuousLinearMap.adjoint‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using hJ
  calc
    _ ≤ ‖J.toContinuousLinearMap‖ *
        ‖((U : H →L[ℂ] H) - (V : H →L[ℂ] H)) ∘L J.toContinuousLinearMap.adjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖J.toContinuousLinearMap‖ *
        (‖(U : H →L[ℂ] H) - (V : H →L[ℂ] H)‖ * ‖J.toContinuousLinearMap.adjoint‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ 1 * (‖(U : H →L[ℂ] H) - (V : H →L[ℂ] H)‖ * 1) := by gcongr
    _ = _ := by ring

end UnitaryExtension

section QueryDifferenceExtension
variable {H₀ H₁ K₀ K₁ : Type*}
  [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup K₀] [InnerProductSpace ℂ K₀] [CompleteSpace K₀]
  [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [CompleteSpace K₁]

omit [CompleteSpace H₀] [CompleteSpace K₀] in
/-- Sandwiching between isometries and adjoints is contractive in the full
operator norm, including arbitrary input vectors. -/
theorem norm_embedding_sandwich_le (J₀ : H₀ →ₗᵢ[ℂ] K₀) (J₁ : H₁ →ₗᵢ[ℂ] K₁)
    (D : H₁ →L[ℂ] H₀) :
    ‖J₀.toContinuousLinearMap ∘L D ∘L J₁.toContinuousLinearMap.adjoint‖ ≤ ‖D‖ := by
  have h₀ : ‖J₀.toContinuousLinearMap‖ ≤ 1 := J₀.norm_toContinuousLinearMap_le
  have h₁ : ‖J₁.toContinuousLinearMap.adjoint‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using J₁.norm_toContinuousLinearMap_le
  calc
    _ ≤ ‖J₀.toContinuousLinearMap‖ * ‖D ∘L J₁.toContinuousLinearMap.adjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖J₀.toContinuousLinearMap‖ * (‖D‖ * ‖J₁.toContinuousLinearMap.adjoint‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ 1 * (‖D‖ * 1) := by gcongr
    _ = ‖D‖ := by ring

/-- Complement blocks of the adversary commute with the common `-I`
oracle action. Thus the actual adversary query difference is the embedded
original difference, with zero contribution from the complementary block.
The two hypotheses state orthogonality of the complementary block, not a
presumed query-norm estimate. -/
theorem adversary_query_difference_extension
    (J₀ : H₀ →ₗᵢ[ℂ] K₀) (J₁ : H₁ →ₗᵢ[ℂ] K₁)
    (U₀ : H₀ ≃ₗᵢ[ℂ] H₀) (U₁ : H₁ ≃ₗᵢ[ℂ] H₁)
    (Γ : H₁ →L[ℂ] H₀) (C : K₁ →L[ℂ] K₀)
    (hC₀ : ∀ y, J₀.toContinuousLinearMap.adjoint (C y) = 0)
    (hC₁ : ∀ x, C (J₁ x) = 0) :
    let G := J₀.toContinuousLinearMap ∘L Γ ∘L J₁.toContinuousLinearMap.adjoint + C
    G ∘L (extendUnitary J₁ U₁ : K₁ →L[ℂ] K₁) -
      (extendUnitary J₀ U₀ : K₀ →L[ℂ] K₀) ∘L G =
        J₀.toContinuousLinearMap ∘L
          (Γ ∘L (U₁ : H₁ →L[ℂ] H₁) - (U₀ : H₀ →L[ℂ] H₀) ∘L Γ) ∘L
            J₁.toContinuousLinearMap.adjoint := by
  dsimp only
  ext y
  change (J₀ (Γ (J₁.toContinuousLinearMap.adjoint (unitaryExtensionMap J₁ U₁ y))) +
    C (unitaryExtensionMap J₁ U₁ y)) -
      unitaryExtensionMap J₀ U₀ (J₀ (Γ (J₁.toContinuousLinearMap.adjoint y)) + C y) = _
  rw [adjoint_unitaryExtension_apply]
  simp only [unitaryExtensionMap_apply, map_add, map_sub, hC₀, hC₁,
    OperatorBridge.adjoint_preparation_apply, map_zero,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply]
  abel

theorem norm_adversary_query_difference_extension_le
    (J₀ : H₀ →ₗᵢ[ℂ] K₀) (J₁ : H₁ →ₗᵢ[ℂ] K₁)
    (U₀ : H₀ ≃ₗᵢ[ℂ] H₀) (U₁ : H₁ ≃ₗᵢ[ℂ] H₁)
    (Γ : H₁ →L[ℂ] H₀) (C : K₁ →L[ℂ] K₀)
    (hC₀ : ∀ y, J₀.toContinuousLinearMap.adjoint (C y) = 0)
    (hC₁ : ∀ x, C (J₁ x) = 0) :
    let G := J₀.toContinuousLinearMap ∘L Γ ∘L J₁.toContinuousLinearMap.adjoint + C
    ‖G ∘L (extendUnitary J₁ U₁ : K₁ →L[ℂ] K₁) -
      (extendUnitary J₀ U₀ : K₀ →L[ℂ] K₀) ∘L G‖ ≤
        ‖Γ ∘L (U₁ : H₁ →L[ℂ] H₁) - (U₀ : H₀ →L[ℂ] H₀) ∘L Γ‖ := by
  dsimp only
  rw [adversary_query_difference_extension J₀ J₁ U₀ U₁ Γ C hC₀ hC₁]
  exact norm_embedding_sandwich_le _ _ _

end QueryDifferenceExtension

/-- The concrete paper reflection, including the copied-label embedding,
fits the proven logarithmic number of actual qubits. -/
def physicalQubitEmbedding {d : ℕ} (hd : 2 ≤ d) {ε A : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hA : 1 ≤ A)
    (hAd : A ≤ max (d : ℝ) (dirichletScale ε)) :
    QueryModel.PurificationSpace d (garbageSize A) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin (2 ^ qubits d ε)) :=
  (copiedQubitEmbedding hd hε hε1 hA hAd).comp (copyEmbedding d (garbageSize A))

/-- The actual full reflected oracle on the encoded finite register
prepares precisely the encoded purification on its known designated input.
Its behavior on every unused coordinate is fixed by `extendUnitary`. -/
theorem finite_reflection_realization {d : ℕ} (hd : 2 ≤ d) {ε A : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hA : 1 ≤ A)
    (hAd : A ≤ max (d : ℝ) (dirichletScale ε)) :
    ∃ (q : ℕ) (J : QueryModel.PurificationSpace d (garbageSize A) →ₗᵢ[ℂ]
        EuclideanSpace ℂ (Fin (2 ^ q))),
      (q : ℝ) ≤ 18 + 5 * Real.logb 2 d + 6 * Real.logb 2 (1 / ε) ∧
      ∀ (p : Fin d → ℝ) (θ : Fin d → Fin (garbageSize A) → ℝ),
        (∀ i, 0 ≤ p i) → (∑ i, p i = 1) →
          extendUnitary J (ReflectionOracle.unitary p θ)
              (J (QueryModel.zeroState d (garbageSize A))) =
            J (ReflectionOracle.euclid (vExt p (garbageSize A) θ)) := by
  refine ⟨qubits d ε, physicalQubitEmbedding hd hε hε1 hA hAd,
    qubits_log_bound hd hε hε1, ?_⟩
  intro p θ hp hsum
  rw [extendUnitary_on_image,
    ReflectionOracle.unitary_prepares p θ (garbageSize_pos hA) hp hsum]

/-- The collision construction has `d` labels and at most `d` garbage
coordinates, so it needs only a logarithmic number of oracle qubits. -/
def collisionQubits (d : ℕ) : ℕ := 2 + 2 * Nat.clog 2 d

theorem collision_capacity {d : ℕ} (hd : 2 ≤ d) :
    Fintype.card (HQ d d) ≤ 2 ^ collisionQubits d := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : 1 ≤ d ^ 2 := one_le_pow₀ hd1
  have hp := Nat.le_pow_clog (by norm_num : 1 < 2) d
  unfold collisionQubits
  calc
    Fintype.card (HQ d d) = 1 + d ^ 2 := by simp [HQ, pow_two]
    _ ≤ 4 * d ^ 2 := by omega
    _ ≤ 4 * (2 ^ Nat.clog 2 d) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp 2)
    _ = _ := by simp only [← pow_mul, pow_add]; ring

def collisionQubitEmbedding {d : ℕ} (hd : 2 ≤ d) :
    QueryModel.PurificationSpace d d →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin (2 ^ collisionQubits d)) :=
  finiteQubitEmbedding (HQ d d) (collisionQubits d) (collision_capacity hd)

theorem collision_qubits_log_bound {d : ℕ} (hd : 2 ≤ d) :
    (collisionQubits d : ℝ) ≤ 4 + 2 * Real.logb 2 d := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hlog : 0 ≤ Real.logb 2 d := Real.logb_nonneg (by norm_num) hdR
  have hceil := (Nat.ceil_lt_add_one hlog).le
  have hdlog : ⌈Real.logb 2 (d : ℝ)⌉₊ = Nat.clog 2 d := Real.natCeil_logb_natCast 2 d
  rw [hdlog] at hceil
  unfold collisionQubits
  push_cast
  linarith

end PUT.FiniteRegisters
