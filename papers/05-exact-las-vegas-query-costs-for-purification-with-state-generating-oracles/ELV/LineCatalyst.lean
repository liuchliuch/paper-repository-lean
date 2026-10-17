import ELV.LineCircuit
import ELV.RayVectors
import Mathlib.Analysis.SpecificLimits.Normed

/-! Actual square summable geometric catalysts for the fixed line walk. -/
noncomputable section
namespace ELV.Line
open ELV.Stabilize ELV.Query
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma geometric_term_norm (q : ℝ) (k : ℕ) : ‖(-(q : ℂ)^2)^k‖ ^ 2 = (q^4)^k := by
  have hb : ‖-(q : ℂ)^2‖ = q^2 := by simp [norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [norm_pow,hb]
  simp only [← pow_mul]
  congr 1
  omega

/-- Even-site coefficients a_k=(-q^2)^k. -/
def geometric (q : ℝ) (hq : q^2 < 1) : lp (fun _ : ℕ => ℂ) 2 :=
  ⟨fun k => (-(q : ℂ)^2)^k,by
    apply memℓp_gen
    have hq4 : q^4 < 1 := by nlinarith [sq_nonneg q,sq_nonneg (q^2)]
    have hg : Summable (fun k : ℕ => ‖(-(q : ℂ)^2)^k‖ ^ 2) := by
      simpa only [geometric_term_norm] using
        (summable_geometric_of_lt_one (by positivity : 0 ≤ q^4) hq4)
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hg⟩

@[simp] lemma geometric_zero (q : ℝ) (hq : q^2 < 1) : geometric q hq 0 = 1 := rfl
@[simp] lemma geometric_succ (q : ℝ) (hq : q^2 < 1) (k : ℕ) :
    geometric q hq (k+1) = -(q : ℂ)^2 * geometric q hq k := by
  change (-(q : ℂ)^2)^(k+1) = -(q : ℂ)^2 * (-(q : ℂ)^2)^k
  rw [pow_succ']

theorem geometric_norm_sq (q : ℝ) (hq : q^2 < 1) : ‖geometric q hq‖ ^ 2 = 1 / (1-q^4) := by
  rw [lp_norm_sq]
  change (∑' k, ‖(-(q : ℂ)^2)^k‖ ^ 2) = _
  simp_rw [geometric_term_norm]
  have hq4 : q^4 < 1 := by nlinarith [sq_nonneg q,sq_nonneg (q^2)]
  simpa [one_div] using tsum_geometric_of_lt_one (by positivity : 0 ≤ q^4) hq4

lemma tensor_norm_sq (f : lp (fun _ : ℕ => ℂ) 2) (v : E) :
    ‖tensorVector f v‖ ^ 2 = ‖f‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [lp_norm_sq,lp_norm_sq]
  change (∑' k, ‖f k • v‖ ^ 2) = _
  simp_rw [norm_smul,mul_pow]
  exact tsum_mul_right

/-- Coupling: even sites a_k s, odd sites a_k q t. -/
def coupling (q : ℝ) (hq : q^2 < 1) (s t : E) : LineSpace E :=
  lpSum.symm (WithLp.toLp 2 (tensorVector (geometric q hq) s,
    tensorVector (geometric q hq) ((q : ℂ) • t)))

@[simp] lemma coupling_even (q : ℝ) (hq : q^2 < 1) (s t : E) (k : ℕ) :
    coupling q hq s t (Sum.inl k) = geometric q hq k • s := rfl
@[simp] lemma coupling_odd (q : ℝ) (hq : q^2 < 1) (s t : E) (k : ℕ) :
    coupling q hq s t (Sum.inr k) = geometric q hq k • ((q : ℂ) • t) := rfl

def origin (s : E) : LineSpace E := lp.single 2 (Sum.inl 0) s

def catalyst (q : ℝ) (hq : q^2 < 1) (s t : E) : LineSpace E := coupling q hq s t - origin s

lemma coupling_norm_sq (q : ℝ) (hq : q^2 < 1) (s t : E) (hs : ‖s‖ = 1) (ht : ‖t‖ = 1) :
    ‖coupling q hq s t‖ ^ 2 = 1/(1-q^2) := by
  unfold coupling
  rw [LinearIsometryEquiv.norm_map,WithLp.prod_norm_sq_eq_of_L2]
  change ‖tensorVector (geometric q hq) s‖ ^ 2 +
    ‖tensorVector (geometric q hq) ((q : ℂ) • t)‖ ^ 2 = _
  rw [tensor_norm_sq,tensor_norm_sq,geometric_norm_sq]
  simp only [hs,ht,norm_smul,norm_one,mul_one,one_pow]
  have hq4 : 1-q^4 ≠ 0 := by nlinarith [sq_nonneg q,sq_nonneg (q^2)]
  have hq2 : 1-q^2 ≠ 0 := by linarith
  have hn : ‖(q : ℂ)‖ ^ 2 = q^2 := by simp [Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [hn]
  field_simp
  <;> ring

lemma origin_inner_coupling (q : ℝ) (hq : q^2 < 1) (s t : E) (hs : ‖s‖ = 1) :
    inner ℂ (origin s) (coupling q hq s t) = 1 := by
  rw [origin,lp.inner_single_left,coupling_even,geometric_zero,one_smul]
  simp [inner_self_eq_norm_sq_to_K,hs]

lemma catalyst_orthogonal (q : ℝ) (hq : q^2 < 1) (s t : E) (hs : ‖s‖ = 1) :
    inner ℂ (origin s) (catalyst q hq s t) = 0 := by
  rw [catalyst,inner_sub_right,origin_inner_coupling q hq s t hs]
  have ho : ‖origin s‖ = 1 := by simpa [origin] using hs
  simp [inner_self_eq_norm_sq_to_K,ho]

/-- The exact catalyst norm, without defining a cost to be the target answer. -/
theorem catalyst_norm_sq (q : ℝ) (hq : q^2 < 1) (s t : E) (hs : ‖s‖ = 1) (ht : ‖t‖ = 1) :
    ‖catalyst q hq s t‖ ^ 2 = q^2/(1-q^2) := by
  have ho : ‖origin s‖ = 1 := by simpa [origin] using hs
  have hi : inner ℂ (coupling q hq s t) (origin s) = 1 := by
    rw [← inner_conj_symm,origin_inner_coupling q hq s t hs]
    simp
  rw [catalyst,@norm_sub_sq ℂ,coupling_norm_sq q hq s t hs ht,ho,hi]
  norm_num
  have hn : 1-q^2 ≠ 0 := by linarith
  field_simp [hn]
  <;> ring

lemma coupling_zero (s t : E) : coupling 0 (by norm_num) s t = origin s := by
  apply Subtype.ext
  funext i
  cases i with
  | inl k =>
    cases k with
    | zero => simp [coupling_even,geometric,origin,lp.single_apply,Pi.single_apply]
    | succ k => simp [coupling_even,geometric,origin,lp.single_apply,Pi.single_apply]
  | inr k => simp [coupling_odd,origin,lp.single_apply,Pi.single_apply]

lemma catalyst_zero (s t : E) : catalyst 0 (by norm_num) s t = 0 := by
  rw [catalyst,coupling_zero,sub_self]

end ELV.Line
