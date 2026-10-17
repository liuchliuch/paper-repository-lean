import Paper22.TestingPrograms
import Paper22.MatrixDuality
import Paper22.CompactConeDuality
import Paper22.ProgramsCompact

/-! Strong duality of the actual fixed-distribution testing program, proved by
compact convex separation and the Hermitian trace representation. -/
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator Pointwise
open Matrix Set
noncomputable section
namespace Paper22
local instance strongDualityMatrixCStarAlgebra (d : ℕ) :
    CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) where
variable {n d : ℕ}

/-- All Hermitian families of binary effects. -/
def hermitianEffectFamilies (n d : ℕ) : Set (Fin n → HermitianMatrix d) :=
  Set.pi Set.univ (fun _ => {T | IsEffect (T : Matrix (Fin d) (Fin d) ℂ)})

theorem isCompact_hermitianEffectFamilies (n d : ℕ) :
    IsCompact (hermitianEffectFamilies n d) := by
  have hclosed : IsClosed (selfAdjoint (Matrix (Fin d) (Fin d) ℂ) :
      Set (Matrix (Fin d) (Fin d) ℂ)) := isClosed_eq continuous_star continuous_id
  exact isCompact_univ_pi fun _ => hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_effects (d := d))

theorem convex_hermitianEffectFamilies (n d : ℕ) :
    Convex ℝ (hermitianEffectFamilies n d) := by
  intro T hT S hS a b ha hb hab x _
  have hTx := hT x (mem_univ x)
  have hSx := hS x (mem_univ x)
  constructor
  · exact add_nonneg (hTx.1.posSemidef.smul ha).nonneg (hSx.1.posSemidef.smul hb).nonneg
  · have h := add_le_add (matrix_smul_mono ha hTx.2) (matrix_smul_mono hb hSx.2)
    simpa only [← add_smul, hab, one_smul] using h

/-- The resource usage and error of a Hermitian effect family. -/
def fixedTestingMap (V : CQChannel n d) (q : Fin n → ℝ)
    (T : Fin n → HermitianMatrix d) : HermitianMatrix d × ℝ :=
  (∑ x, q x • T x, programObjective V.states q (fun x => T x))

theorem continuous_fixedTestingMap (V : CQChannel n d) (q : Fin n → ℝ) :
    Continuous (fixedTestingMap V q) := by
  unfold fixedTestingMap programObjective
  fun_prop

/-- The matrix error is affine under real convex combinations of test families. -/
theorem programObjective_convex_combination (V : CQChannel n d) (q : Fin n → ℝ)
    (T S : Fin n → Matrix (Fin d) (Fin d) ℂ) {a b : ℝ} (hab : a+b=1) :
    programObjective V.states q (fun x => a • T x + b • S x) =
      a * programObjective V.states q T + b * programObjective V.states q S := by
  have hI : a • (1 : Matrix (Fin d) (Fin d) ℂ) + b • 1 = 1 := by
    rw [← add_smul, hab, one_smul]
  have heq (x : Fin n) : 1-(a • T x+b • S x) = a • (1-T x)+b • (1-S x) := by
    calc 1-(a • T x+b • S x) =
          (a • 1+b • 1)-(a • T x+b • S x) := by rw [hI]
         _ = _ := by simp only [smul_sub]; abel
  unfold programObjective
  simp_rw [heq, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, Complex.smul_re, smul_eq_mul, mul_add]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro x _ <;> ring

theorem fixedTestingMap_convex_combination (V : CQChannel n d) (q : Fin n → ℝ)
    (T S : Fin n → HermitianMatrix d) {a b : ℝ} (hab : a+b=1) :
    fixedTestingMap V q (a • T+b • S) =
      a • fixedTestingMap V q T+b • fixedTestingMap V q S := by
  apply Prod.ext
  · change (∑ x, q x • (a • T x+b • S x)) = a • (∑ x, q x • T x)+b • (∑ x, q x • S x)
    simp only [smul_add, smul_smul, Finset.sum_add_distrib, Finset.smul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro x _ <;> rw [mul_comm]
  · exact programObjective_convex_combination V q (fun x => T x) (fun x => S x) hab

def fixedTestingAttainable (V : CQChannel n d) (q : Fin n → ℝ) :
    Set (HermitianMatrix d × ℝ) := fixedTestingMap V q '' hermitianEffectFamilies n d

theorem isCompact_fixedTestingAttainable (V : CQChannel n d) (q : Fin n → ℝ) :
    IsCompact (fixedTestingAttainable V q) :=
  (isCompact_hermitianEffectFamilies n d).image (continuous_fixedTestingMap V q)

theorem convex_fixedTestingAttainable (V : CQChannel n d) (q : Fin n → ℝ) :
    Convex ℝ (fixedTestingAttainable V q) := by
  rintro _ ⟨T,hT,rfl⟩ _ ⟨S,hS,rfl⟩ a b ha hb hab
  exact ⟨a • T+b • S, convex_hermitianEffectFamilies n d hT hS ha hb hab,
    fixedTestingMap_convex_combination V q T S hab⟩

def hermitianPositiveCone (d : ℕ) : Set (HermitianMatrix d) :=
  {B | 0 ≤ (B : Matrix (Fin d) (Fin d) ℂ)}

theorem isClosed_hermitianPositiveCone (d : ℕ) : IsClosed (hermitianPositiveCone d) :=
  isClosed_le continuous_const continuous_subtype_val

theorem convex_hermitianPositiveCone (d : ℕ) : Convex ℝ (hermitianPositiveCone d) := by
  intro A hA B hB a b ha hb _
  exact add_nonneg (hA.posSemidef.smul ha).nonneg (hB.posSemidef.smul hb).nonneg

/-- If every positive-matrix dual value is at most a, an actual decoding family
achieves error at most a under the operator resource constraint. -/
theorem fixedTesting_dual_upper (V : CQChannel n d) (q : Fin n → ℝ)
    (hq : ∑ x, q x = 1) {c a : ℝ} (hc : 0 ≤ c)
    (hdual : ∀ B : Matrix (Fin d) (Fin d) ℂ, 0 ≤ B →
      (∑ x, q x * testingRisk (V.states x) B) - c * B.trace.re ≤ a) :
    ∃ T : Fin n → Matrix (Fin d) (Fin d) ℂ,
      (∀ x, IsEffect (T x)) ∧ (∑ x, q x • T x) ≤ c • 1 ∧
      programObjective V.states q T ≤ a := by
  let I : HermitianMatrix d := ⟨1,IsSelfAdjoint.one _⟩
  let C := hermitianPositiveCone d
  let K := fixedTestingAttainable V q
  have hzero : ((0 : HermitianMatrix d),(1:ℝ)) ∈ K := by
    refine ⟨0,?_,?_⟩
    · intro x _
      exact IsEffect.zero
    · apply Prod.ext
      · simp [fixedTestingMap]
      · exact programObjective_zero V hq
  by_contra hno
  have hout : (c • I,a) ∉ K+(C ×ˢ Ici 0) := by
    rintro ⟨_,⟨T,hT,rfl⟩,z,hz,heq⟩
    apply hno
    refine ⟨fun x => T x,fun x => hT x (mem_univ x),?_,?_⟩
    · have he := congrArg (fun w : HermitianMatrix d × ℝ =>
        (w.1 : Matrix (Fin d) (Fin d) ℂ)) heq
      have he' : (∑ x, q x • (T x : Matrix (Fin d) (Fin d) ℂ)) +
          (z.1 : Matrix (Fin d) (Fin d) ℂ) = c • 1 := by
        simpa [fixedTestingMap,I] using he
      rw [← he']
      exact le_add_of_nonneg_right hz.1
    · have he := congrArg Prod.snd heq
      change programObjective V.states q (fun x => T x)+z.2=a at he
      have hn : 0 ≤ z.2 := hz.2
      linarith
  obtain ⟨g,β,hβ,hg,hsep⟩ := compact_cone_dual_certificate
    (convex_fixedTestingAttainable V q) (isCompact_fixedTestingAttainable V q)
    (convex_hermitianPositiveCone d) (isClosed_hermitianPositiveCone d)
    (show (0 : HermitianMatrix d) ∈ C from by change (0 : Matrix (Fin d) (Fin d) ℂ) ≤ 0; rfl)
    (fun hr _ hX => (hX.posSemidef.smul hr).nonneg) hzero
    (show c • I ∈ C from (PosSemidef.one.smul hc).nonneg) hout
  obtain ⟨G,hG⟩ := exists_hermitianTraceFunctional g.toLinearMap
  have hgtrace (X : HermitianMatrix d) :
      g X = ((G : Matrix (Fin d) (Fin d) ℂ)*X).trace.re := by
    exact (congrArg (fun f : Module.Dual ℝ (HermitianMatrix d) => f X) hG).symm
  have hGpos : 0 ≤ (G : Matrix (Fin d) (Fin d) ℂ) := by
    apply (hermitian_nonneg_iff_trace_mul_nonneg G.prop).mpr
    intro X hX
    exact (hgtrace ⟨X,IsSelfAdjoint.of_nonneg hX⟩) ▸ hg _ hX
  let B : Matrix (Fin d) (Fin d) ℂ := β⁻¹ • (G : Matrix (Fin d) (Fin d) ℂ)
  have hB : 0 ≤ B := (hGpos.posSemidef.smul (inv_nonneg.mpr hβ.le)).nonneg
  have hGB : (G : Matrix (Fin d) (Fin d) ℂ) = β • B := by
    simp only [B, smul_smul, mul_inv_cancel₀ hβ.ne', one_smul]
  let T : Fin n → HermitianMatrix d := fun x =>
    ⟨positiveTest (V.states x-B),IsSelfAdjoint.of_nonneg (positiveTest_isEffect _).1⟩
  have hT : T ∈ hermitianEffectFamilies n d := fun x _ => positiveTest_isEffect _
  have hineq := hsep (fixedTestingMap V q T) ⟨T,hT,rfl⟩
  have hnorm : g (c • I) = β * (c * B.trace.re) := by
    rw [hgtrace, hGB]
    simp [I, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
    ring
  have hresource : g (∑ x, q x • T x) = β * (∑ x, q x * (B*T x).trace.re) := by
    rw [hgtrace, hGB]
    simp only [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
    congr 1
    simp [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, Matrix.mul_smul,
      Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  have hrisk : (∑ x, q x * testingRisk (V.states x) B) =
      programObjective V.states q (fun x => T x)+∑ x, q x * (B*T x).trace.re := by
    calc _ = ∑ x, q x * testError (V.states x) B (T x) := by
           apply Finset.sum_congr rfl
           intro x _
           rw [show (T x : Matrix (Fin d) (Fin d) ℂ) = positiveTest (V.states x-B) from rfl,
             testError_positiveTest (V.isDensity x).posSemidef.nonneg hB]
         _ = _ := by simp only [testError, programObjective, mul_add, Finset.sum_add_distrib]
  change g (c • I)+β*a < g (∑ x, q x • T x)+
    β * programObjective V.states q (fun x => T x) at hineq
  rw [hnorm,hresource] at hineq
  have hbound := hdual B hB
  rw [hrisk] at hbound
  nlinarith

/-- The actual MC error is bounded above by any common upper bound for its
positive-matrix testing dual values at one input distribution. -/
theorem epsMC_le_of_testingDual (V : CQChannel n d)
    {q : Fin n → ℝ} (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1)
    {L a : ℝ} (hL : 0 ≤ L)
    (hdual : ∀ B : Matrix (Fin d) (Fin d) ℂ, 0 ≤ B →
      testingDualObjective V L q B ≤ a) : epsMC V L ≤ a := by
  obtain ⟨T,hT,hresource,herror⟩ := fixedTesting_dual_upper V q hq1
    (one_div_nonneg.mpr hL) hdual
  exact (epsMC_le_objective V ⟨hq0,hq1,hT,hresource⟩).trans herror

end Paper22
end
