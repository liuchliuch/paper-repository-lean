import ELV.FockWitness
import ELV.SignedGram

/-! Legal boundary oracles in every nonzero workspace, including arbitrary
unitary completion of a prescribed unit generated state. -/
noncomputable section
namespace ELV.Model
variable {n : ℕ} [NeZero n]

def activeIndex (n : ℕ) [NeZero n] : Fin (2*n) := ⟨n, by have := NeZero.pos n; omega⟩
def answerOne (n : ℕ) [NeZero n] : Mspace n :=
  (EuclideanSpace.basisFun (Fin (2*n)) ℂ) (activeIndex n)

lemma activeIndex_ne_zero (n : ℕ) [NeZero n] : activeIndex n ≠ 0 := by
  intro h
  have h' := congrArg Fin.val h
  have := NeZero.pos n
  simp [activeIndex] at h'
  omega

lemma answerOne_norm (n : ℕ) [NeZero n] : ‖answerOne n‖ = 1 :=
  (EuclideanSpace.basisFun (Fin (2*n)) ℂ).orthonormal.norm_eq_one _

lemma known_answer_inner (n : ℕ) [NeZero n] : inner ℂ (knownInput n) (answerOne n) = 0 :=
  (EuclideanSpace.basisFun (Fin (2*n)) ℂ).orthonormal.inner_eq_zero (activeIndex_ne_zero n).symm

def twoAmplitudes (a b : ℝ) : Mspace n := (a : ℂ) • knownInput n + (b : ℂ) • answerOne n

lemma twoAmplitudes_inner (a b c d : ℝ) :
    inner ℂ (twoAmplitudes (n := n) a b) (twoAmplitudes c d) = (a*c+b*d : ℝ) := by
  have hs : inner ℂ (knownInput n) (knownInput n) = 1 := by
    simp [inner_self_eq_norm_sq_to_K,knownInput_norm]
  have ht : inner ℂ (answerOne n) (answerOne n) = 1 := by
    simp [inner_self_eq_norm_sq_to_K,answerOne_norm]
  have hts : inner ℂ (answerOne n) (knownInput n) = 0 := by
    rw [← inner_conj_symm,known_answer_inner]
    simp
  simp only [twoAmplitudes,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
    Complex.conj_ofReal,hs,ht,hts,known_answer_inner,Complex.ofReal_add,Complex.ofReal_mul]
  ring

theorem twoAmplitudes_norm_sq (a b : ℝ) : ‖twoAmplitudes (n := n) a b‖ ^ 2 = a^2+b^2 := by
  have hr := congrArg Complex.re (twoAmplitudes_inner (n := n) a b a b)
  simpa [inner_self_eq_norm_sq_to_K,← Complex.ofReal_pow,pow_two] using hr

/-- Every unit generated state is the image of the known input under an
actual finite-dimensional unitary oracle. -/
theorem exists_oracle_of_unit (v : Mspace n) (hv : ‖v‖ = 1) :
    ∃ O : Oracle n, O.phi = v := by
  let a : Unit → Mspace n := fun _ => knownInput n
  let b : Unit → Mspace n := fun _ => v
  have hg : Gram.EqualGram a b := by
    intro x y
    simp [a,b,inner_self_eq_norm_sq_to_K,knownInput_norm,hv]
  let L := (Submodule.span ℂ (Set.range b)).subtypeₗᵢ.comp (Gram.spanIsometry hg).toLinearIsometry
  let O : Oracle n := ⟨L.extend.toLinearMap,L.extend.norm_map⟩
  refine ⟨O,?_⟩
  have hx : knownInput n ∈ Submodule.span ℂ (Set.range a) :=
    Submodule.subset_span ⟨(),rfl⟩
  change L.extend (knownInput n) = v
  have he := L.extend_apply (⟨knownInput n,hx⟩ : Submodule.span ℂ (Set.range a))
  rw [he]
  exact Gram.spanIsometry_apply hg ()

lemma twoAmplitudes_probability (a b : ℝ) :
    Rescale.mass (twoAmplitudes (n := n) a b) = b^2 := by
  classical
  unfold Rescale.mass
  rw [Finset.sum_eq_single (activeIndex n)]
  · have hne := activeIndex_ne_zero n
    simp [twoAmplitudes,knownInput,answerOne,EuclideanSpace.basisFun_apply,
      EuclideanSpace.single_apply,activeIndex,Fin.ext_iff,NeZero.ne n]
  · intro i _ hi
    by_cases hhigh : n ≤ i.val
    · have h0 : i ≠ 0 := by
        intro hz
        have := NeZero.pos n
        simp [hz] at hhigh
        omega
      simp [twoAmplitudes,knownInput,answerOne,EuclideanSpace.basisFun_apply,
        EuclideanSpace.single_apply,hhigh,hi,h0]
    · simp [hhigh]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

/-- Explicit low and high legal instances with overlap mu (4.12). -/
theorem boundary_pair (gap : Gap) :
    ∃ Om Op : Costs.promisedFamily n gap.δ,
      Costs.label gap.δ Om = 0 ∧ Costs.label gap.δ Op = 1 ∧
      inner ℂ Om.val.phi Op.val.phi = (gap.mu : ℂ) := by
  let vm : Mspace n := twoAmplitudes (Real.sqrt gap.high) (Real.sqrt gap.ell)
  let vp : Mspace n := twoAmplitudes (Real.sqrt gap.ell) (Real.sqrt gap.high)
  have hvm : ‖vm‖ = 1 := by
    have hn : ‖vm‖ ^ 2 = 1 := by
      rw [twoAmplitudes_norm_sq,Real.sq_sqrt gap.high_nonneg,Real.sq_sqrt gap.ell_nonneg]
      linarith [gap.ell_add_high]
    nlinarith [norm_nonneg vm]
  have hvp : ‖vp‖ = 1 := by
    have hn : ‖vp‖ ^ 2 = 1 := by
      rw [twoAmplitudes_norm_sq,Real.sq_sqrt gap.ell_nonneg,Real.sq_sqrt gap.high_nonneg]
      exact gap.ell_add_high
    nlinarith [norm_nonneg vp]
  obtain ⟨Om,hm⟩ := exists_oracle_of_unit vm hvm
  obtain ⟨Op,hp⟩ := exists_oracle_of_unit vp hvp
  have hpm : Om.p = gap.ell := by
    change Rescale.mass Om.phi = _
    rw [hm,twoAmplitudes_probability,Real.sq_sqrt gap.ell_nonneg]
  have hpp : Op.p = gap.high := by
    change Rescale.mass Op.phi = _
    rw [hp,twoAmplitudes_probability,Real.sq_sqrt gap.high_nonneg]
  let om : Costs.promisedFamily n gap.δ := ⟨Om,Or.inl hpm.le⟩
  let op : Costs.promisedFamily n gap.δ := ⟨Op,Or.inr hpp.ge⟩
  refine ⟨om,op,?_,?_,?_⟩
  · change (if Om.p ≤ (1/2 : ℝ) then (0 : Fin 2) else 1) = 0
    apply if_pos
    rw [hpm,Gap.ell]
    linarith [gap.δ_pos]
  · change (if Op.p ≤ (1/2 : ℝ) then (0 : Fin 2) else 1) = 1
    apply if_neg
    rw [hpp,Gap.high]
    linarith [gap.δ_pos]
  · change inner ℂ Om.phi Op.phi = _
    rw [hm,hp,twoAmplitudes_inner]
    congr 1
    rw [gap.mu_eq_two_sqrt,Real.sqrt_mul gap.ell_nonneg]
    ring

end ELV.Model
