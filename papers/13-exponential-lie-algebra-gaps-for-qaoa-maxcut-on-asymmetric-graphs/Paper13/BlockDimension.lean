import Paper13.MatrixDimension
import Paper13.InvariantBlocks
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators

/-- Two real copies of a skew-Hermitian subspace embed in any complex space containing it. -/
def skewPairMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℝ (Matrix ι ι ℂ)) (C : Submodule ℂ (Matrix ι ι ℂ))
    (hC : ∀ A ∈ L, A ∈ C) : (L × L) →ₗ[ℝ] C where
  toFun p := ⟨p.1.val + Complex.I • p.2.val, C.add_mem (hC _ p.1.property) (C.smul_mem _ (hC _ p.2.property))⟩
  map_add' p q := by apply Subtype.ext; simp [smul_add, add_add_add_comm]
  map_smul' r p := by
    apply Subtype.ext
    change r • p.1.val + Complex.I • (r • p.2.val) = r • (p.1.val + Complex.I • p.2.val)
    rw [smul_add, smul_comm Complex.I r p.2.val]

lemma skewPairMap_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℝ (Matrix ι ι ℂ)) (C : Submodule ℂ (Matrix ι ι ℂ))
    (hC : ∀ A ∈ L, A ∈ C) (hskew : ∀ A ∈ L, Aᴴ = -A) :
    Function.Injective (skewPairMap L C hC) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm
  · rintro ⟨A,B⟩ hp
    have hz : A.val + Complex.I • B.val = 0 := congrArg Subtype.val hp
    have hs := congrArg Matrix.conjTranspose hz
    simp only [conjTranspose_add, conjTranspose_smul, hskew _ A.property,
      hskew _ B.property, conjTranspose_zero] at hs
    have hstar : star (Complex.I : ℂ) = -Complex.I := by simp
    rw [hstar, neg_smul, smul_neg, neg_neg] at hs
    have hA2 : (2 : ℂ) • A.val = 0 := by
      calc _ = (A.val + Complex.I • B.val) - (-A.val + Complex.I • B.val) := by module
           _ = 0 := by rw [hz, hs]; simp
    have hA : A.val = 0 := (smul_eq_zero.mp hA2).resolve_left (by norm_num)
    have hB : B.val = 0 := by
      rw [hA, zero_add] at hz
      exact (smul_eq_zero.mp hz).resolve_left Complex.I_ne_zero
    exact Prod.ext (Subtype.ext hA) (Subtype.ext hB)
  · exact bot_le

/-- A real skew-Hermitian subspace has at most the complex dimension of a containing complex space. -/
theorem skew_finrank_le_complex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℝ (Matrix ι ι ℂ)) (C : Submodule ℂ (Matrix ι ι ℂ))
    (hC : ∀ A ∈ L, A ∈ C) (hskew : ∀ A ∈ L, Aᴴ = -A) :
    Module.finrank ℝ L ≤ Module.finrank ℂ C := by
  have h := LinearMap.finrank_le_finrank_of_injective (skewPairMap_injective L C hC hskew)
  rw [Module.finrank_prod, finrank_real_of_complex] at h
  omega

/-- Complex matrices commuting with a specified family of blocks. -/
def blockCommutant {ι β : Type*} [Fintype ι] (R : β → Matrix ι ι ℂ) :
    Submodule ℂ (Matrix ι ι ℂ) where
  carrier := {A | ∀ b, A * R b = R b * A}
  zero_mem' := by intro b; simp
  add_mem' := by intro A B hA hB b; rw [add_mul, mul_add, hA b, hB b]
  smul_mem' := by intro z A hA b; rw [Matrix.smul_mul, Matrix.mul_smul, hA b]

/-- Restrict a matrix in the commutant to one block range. -/
def blockRestriction {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (R : β → Matrix ι ι ℂ) (b : β) :
    blockCommutant R →ₗ[ℂ]
      Module.End ℂ (LinearMap.range (Matrix.toLin' (R b))) where
  toFun A :=
    { toFun := fun w => ⟨A.val.mulVec w.val, by
        obtain ⟨v,hv⟩ := w.property
        change (R b).mulVec v = w.val at hv
        refine ⟨A.val.mulVec v, ?_⟩
        change (R b).mulVec (A.val.mulVec v) = A.val.mulVec w.val
        rw [Matrix.mulVec_mulVec, ← A.property b, ← Matrix.mulVec_mulVec, hv]⟩
      map_add' := by intro x y; apply Subtype.ext; simp [Matrix.mulVec_add]
      map_smul' := by intro z x; apply Subtype.ext; simp [Matrix.mulVec_smul] }
  map_add' A B := by apply LinearMap.ext; intro w; apply Subtype.ext; simp [Matrix.add_mulVec]
  map_smul' z A := by apply LinearMap.ext; intro w; apply Subtype.ext; simp [Matrix.smul_mulVec]

/-- The joint restriction map into all block endomorphism spaces. -/
def allBlockRestrictions {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (R : β → Matrix ι ι ℂ) : blockCommutant R →ₗ[ℂ]
      (∀ b, Module.End ℂ (LinearMap.range (Matrix.toLin' (R b)))) :=
  LinearMap.pi (blockRestriction R)

lemma allBlockRestrictions_injective {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (R : β → Matrix ι ι ℂ) (hsum : ∑ b, R b = 1) :
    Function.Injective (allBlockRestrictions R) := by
  intro A B hAB
  apply Subtype.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  have hb (b : β) : A.val.mulVec ((R b).mulVec v) = B.val.mulVec ((R b).mulVec v) := by
    have h := congrFun hAB b
    have hh := DFunLike.congr_fun h ⟨(R b).mulVec v, ⟨v,rfl⟩⟩
    exact congrArg Subtype.val hh
  change A.val.mulVec v = B.val.mulVec v
  calc _ = A.val.mulVec ((∑ b, R b).mulVec v) := by rw [hsum, Matrix.one_mulVec]
       _ = B.val.mulVec ((∑ b, R b).mulVec v) := by simp only [Matrix.sum_mulVec, Matrix.mulVec_sum, hb]
       _ = B.val.mulVec v := by rw [hsum, Matrix.one_mulVec]

/-- The block-diagonal dimension bound, for actual commuting matrices and actual block ranks. -/
theorem blockCommutant_finrank_le {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (R : β → Matrix ι ι ℂ) (hsum : ∑ b, R b = 1) :
    Module.finrank ℂ (blockCommutant R) ≤
      ∑ b, (Module.finrank ℂ (LinearMap.range (Matrix.toLin' (R b))))^2 := by
  have h := LinearMap.finrank_le_finrank_of_injective (allBlockRestrictions_injective R hsum)
  have hf (b : β) : Module.Free ℂ (Module.End ℂ (LinearMap.range (Matrix.toLin' (R b)))) := inferInstance
  letI := hf
  rw [Module.finrank_pi_fintype] at h
  simpa only [Module.End, Module.finrank_linearMap, pow_two] using h
/-- The trace functional on the complex block commutant. -/
def blockTrace {ι β : Type*} [Fintype ι] (R : β → Matrix ι ι ℂ) :
    blockCommutant R →ₗ[ℂ] ℂ := (Matrix.traceLinearMap ι ℂ (α := ℂ)).comp (blockCommutant R).subtype

lemma blockTrace_surjective {ι β : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (R : β → Matrix ι ι ℂ) : Function.Surjective (blockTrace R) := by
  intro z
  refine ⟨⟨(z / Fintype.card ι) • (1 : Matrix ι ι ℂ), ?_⟩, ?_⟩
  · intro b
    simp [Matrix.smul_mul, Matrix.mul_smul]
  · change Matrix.trace ((z / Fintype.card ι) • (1 : Matrix ι ι ℂ)) = z
    rw [Matrix.trace_smul, Matrix.trace_one]
    change z / (Fintype.card ι : ℂ) * (Fintype.card ι : ℂ) = z
    apply div_mul_cancel₀
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι).ne'

/-- Matrices commuting with all blocks and globally traceless. -/
def blockTraceless {ι β : Type*} [Fintype ι] (R : β → Matrix ι ι ℂ) :
    Submodule ℂ (Matrix ι ι ℂ) := blockCommutant R ⊓ LinearMap.ker (Matrix.traceLinearMap ι ℂ (α := ℂ))

def blockTracelessEquiv {ι β : Type*} [Fintype ι] (R : β → Matrix ι ι ℂ) :
    blockTraceless R ≃ₗ[ℂ] LinearMap.ker (blockTrace R) where
  toFun A := ⟨⟨A.val,A.property.1⟩,A.property.2⟩
  invFun A := ⟨A.val.val,⟨A.val.property,A.property⟩⟩
  left_inv A := rfl
  right_inv A := rfl
  map_add' A B := rfl
  map_smul' z A := rfl

/-- Global tracelessness removes exactly one complex dimension from the block commutant. -/
lemma blockTraceless_finrank_add_one {ι β : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (R : β → Matrix ι ι ℂ) :
    Module.finrank ℂ (blockTraceless R) + 1 = Module.finrank ℂ (blockCommutant R) := by
  rw [(blockTracelessEquiv R).finrank_eq]
  have h := (blockTrace R).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (blockTrace_surjective R)] at h
  simp only [finrank_top, Module.finrank_self] at h
  omega

/-- The real skew-Hermitian, globally traceless algebra preserving a complete
family of commuting blocks has dimension at most the squared block ranks minus one. -/
theorem traceless_skew_block_bound {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] [Fintype β] (L : Submodule ℝ (Matrix ι ι ℂ)) (R : β → Matrix ι ι ℂ)
    (hsum : ∑ b, R b = 1) (hskew : ∀ A ∈ L, Aᴴ = -A)
    (hcomm : ∀ A ∈ L, ∀ b, A*R b = R b*A) (htrace : ∀ A ∈ L, Matrix.trace A = 0) :
    Module.finrank ℝ L ≤ (∑ b, (Module.finrank ℂ (LinearMap.range (Matrix.toLin' (R b))))^2) - 1 := by
  have hLC : ∀ A ∈ L, A ∈ blockTraceless R := by
    intro A hA
    exact ⟨hcomm A hA, htrace A hA⟩
  have hL := skew_finrank_le_complex L (blockTraceless R) hLC hskew
  have htr := blockTraceless_finrank_add_one R
  have hblocks := blockCommutant_finrank_le R hsum
  omega
end Paper13

