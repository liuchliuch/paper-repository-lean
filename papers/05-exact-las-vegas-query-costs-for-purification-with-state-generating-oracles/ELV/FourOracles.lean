import ELV.FourFilter

/-! Four explicit legal completions in every nonzero workspace. The same
boundary rotation is used on each garbage coordinate; this gives the same
sharp four-instance filter as the active-plane embedding. -/
noncomputable section
set_option maxRecDepth 2000
namespace ELV.FourOracles
open ELV.Stabilize ELV.Model ELV.Rotation ELV.Query ELV.Costs
variable {n : ℕ} [NeZero n]

lemma chart_fst (v : Mspace n) (i : Fin n) :
    (answerChart n v).fst i = v ⟨i.val,by have:=i.isLt; omega⟩ := rfl
lemma chart_snd (v : Mspace n) (i : Fin n) :
    (answerChart n v).snd i = v ⟨n+i.val,by have:=i.isLt; omega⟩ := rfl

lemma chart_known : answerChart n (knownInput n) =
    WithLp.toLp 2 ((EuclideanSpace.basisFun (Fin n) ℂ) 0,0) := by
  apply (WithLp.equiv 2 (_ × _)).injective
  apply Prod.ext
  · ext i
    change (answerChart n (knownInput n)).fst i = (EuclideanSpace.basisFun (Fin n) ℂ 0) i
    rw [chart_fst]
    simp only [knownInput,EuclideanSpace.basisFun_apply,EuclideanSpace.single_apply]
    congr 1
    apply propext
    simp only [Fin.ext_iff,Fin.val_zero]
  · ext i
    change (answerChart n (knownInput n)).snd i = 0
    rw [chart_snd]
    have hn := NeZero.pos n
    simp only [knownInput,EuclideanSpace.basisFun_apply,EuclideanSpace.single_apply]
    rw [if_neg (by intro h; have hh:=congrArg Fin.val h; simp only [Fin.val_zero] at hh; omega)]

lemma chart_answer : answerChart n (answerOne n) =
    WithLp.toLp 2 (0,(EuclideanSpace.basisFun (Fin n) ℂ) 0) := by
  apply (WithLp.equiv 2 (_ × _)).injective
  apply Prod.ext
  · ext i
    change (answerChart n (answerOne n)).fst i = 0
    rw [chart_fst]
    simp only [answerOne,EuclideanSpace.basisFun_apply,EuclideanSpace.single_apply]
    rw [if_neg (by intro h; have hh:=congrArg Fin.val h; change i.val=n at hh; omega)]
  · ext i
    change (answerChart n (answerOne n)).snd i = (EuclideanSpace.basisFun (Fin n) ℂ 0) i
    rw [chart_snd]
    simp only [answerOne,EuclideanSpace.basisFun_apply,EuclideanSpace.single_apply]
    congr 1
    apply propext
    simp only [Fin.ext_iff,activeIndex,Fin.val_zero]
    omega

def fullRotation (a b : ℝ) (h : a^2+b^2=1) : Mspace n ≃ₗᵢ[ℂ] Mspace n :=
  (answerChart n).trans ((Rotation.unitary a b h).trans (answerChart n).symm)

lemma fullRotation_known (a b : ℝ) (h : a^2+b^2=1) :
    fullRotation (n:=n) a b h (knownInput n) = twoAmplitudes a b := by
  apply (answerChart n).injective
  simp only [fullRotation,LinearIsometryEquiv.trans_apply,LinearIsometryEquiv.apply_symm_apply,
    chart_known,Rotation.unitary_apply,twoAmplitudes,map_add,map_smul,chart_answer]
  apply (WithLp.equiv 2 (_ × _)).injective
  apply Prod.ext <;> simp [rotate]

def ofUnitary (U : Mspace n ≃ₗᵢ[ℂ] Mspace n) : Oracle n := ⟨U.toLinearMap,U.norm_map⟩
@[simp] lemma ofUnitary_unitary (U : Mspace n ≃ₗᵢ[ℂ] Mspace n) : (ofUnitary U).unitary = U := by
  ext v
  rfl

def a (gap : Gap) (c : Bool) : ℝ := if c then Real.sqrt gap.ell else Real.sqrt gap.high
def b (gap : Gap) (c : Bool) : ℝ := if c then Real.sqrt gap.high else Real.sqrt gap.ell
lemma circle (gap : Gap) (c : Bool) : (a gap c)^2+(b gap c)^2=1 := by
  cases c <;> simp [a,b,Real.sq_sqrt gap.ell_nonneg,Real.sq_sqrt gap.high_nonneg] <;>
    linarith [gap.ell_add_high]

def base (gap : Gap) (n : ℕ) [NeZero n] (c : Bool) : Mspace n ≃ₗᵢ[ℂ] Mspace n :=
  fullRotation (a gap c) (b gap c) (circle gap c)

def signed {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : E ≃ₗᵢ[ℂ] E) (ε : Bool) : E ≃ₗᵢ[ℂ] E :=
  if ε then (LinearIsometryEquiv.neg ℂ).trans U else U

@[simp] lemma signed_false {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : E ≃ₗᵢ[ℂ] E) : signed U false = U := rfl
@[simp] lemma signed_true_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : E ≃ₗᵢ[ℂ] E) (v : E) : signed U true v = -U v := by
  simp [signed]
@[simp] lemma signed_true_symm_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : E ≃ₗᵢ[ℂ] E) (v : E) : (signed U true).symm v = -U.symm v := rfl

def oracle (gap : Gap) (n : ℕ) [NeZero n] (c ε : Bool) : Oracle n := ofUnitary (signed (base gap n c) ε)

lemma generated (gap : Gap) (c ε : Bool) :
    (oracle gap n c ε).phi = if ε then -twoAmplitudes (a gap c) (b gap c) else
      twoAmplitudes (a gap c) (b gap c) := by
  cases ε <;> simp [oracle,Oracle.phi,ofUnitary,base,fullRotation_known]

lemma probability (gap : Gap) (c ε : Bool) : (oracle gap n c ε).p = if c then gap.high else gap.ell := by
  change Rescale.mass (oracle gap n c ε).phi = _
  rw [generated]
  have hn (v : Mspace n) : Rescale.mass (-v)=Rescale.mass v := by simp [Rescale.mass]
  cases ε <;> simp only [Bool.false_eq_true,ite_false,ite_true,hn,twoAmplitudes_probability]
  all_goals cases c <;> simp [b,Real.sq_sqrt gap.ell_nonneg,Real.sq_sqrt gap.high_nonneg]

def input (gap : Gap) (n : ℕ) [NeZero n] (c ε : Bool) : promisedFamily n gap.δ :=
  ⟨oracle gap n c ε,by
    cases c
    · exact Or.inl (by rw [probability]; exact le_refl _)
    · exact Or.inr (by rw [probability]; exact le_refl _)⟩

lemma instance_label (gap : Gap) (c ε : Bool) : label gap.δ (input gap n c ε) = if c then 1 else 0 := by
  change (if (oracle gap n c ε).p ≤ 1/2 then (0 : Fin 2) else 1) = _
  rw [probability]
  cases c <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · exact if_pos (by dsimp [Gap.ell]; linarith [gap.δ_pos])
  · exact if_neg (by dsimp [Gap.high]; linarith [gap.δ_pos])

/-- Signs of both query directions change together, as required by actual inverse access. -/
lemma query_sign (gap : Gap) (C : Type*) (c ε : Bool) :
    bidirectional C (oracle gap n c ε) = signed (bidirectional C (oracle gap n c false)) ε := by
  cases ε
  · rfl
  · ext v i
    apply (WithLp.equiv 2 (_ × _)).injective
    apply Prod.ext <;> simp [bidirectional,oracle,signed,amplify,pairCongr]

/-- The relative forward and inverse rotations have real part mu. -/
lemma base_relative (gap : Gap) (z : Mspace n) :
    (base gap n false).symm (base gap n true z) +
      (base gap n true).symm (base gap n false z) = (2*gap.mu : ℂ) • z := by
  apply (answerChart n).injective
  simp only [map_add,map_smul,base,fullRotation,LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_trans,LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.symm_apply_apply,Rotation.unitary_apply,Rotation.unitary_symm_apply]
  rw [rotate_comp,rotate_comp]
  have hm : a gap false*a gap true+b gap false*b gap true = gap.mu := by
    simp only [a,b,Bool.false_eq_true,ite_false,ite_true]
    rw [gap.mu_eq_two_sqrt,Real.sqrt_mul gap.ell_nonneg]
    ring
  have hm' : a gap true*a gap false+b gap true*b gap false = gap.mu := by
    nlinarith [hm]
  simp only [mul_neg,neg_mul,sub_neg_eq_add]
  rw [hm,hm']
  have hb : -(b gap true)*a gap false+a gap true*b gap false =
      -(-(b gap false)*a gap true+a gap false*b gap true) := by ring
  simp only [neg_mul] at hb
  rw [hb,rotate_symmetric]

lemma base_relative_inverse (gap : Gap) (z : Mspace n) :
    base gap n false ((base gap n true).symm z) +
      base gap n true ((base gap n false).symm z) = (2*gap.mu : ℂ) • z := by
  have hh := congrArg (base gap n false) (base_relative gap ((base gap n false).symm z))
  simp only [map_add,map_smul,LinearIsometryEquiv.apply_symm_apply] at hh
  simpa only [add_comm] using hh

/-- The computed relative-rotation identity survives arbitrary ancillary
controls and the actual forward/inverse direct sum. -/
lemma query_relative (gap : Gap) (C : Type*) (v : OracleQuerySpace n C) :
    let P := bidirectional C (oracle gap n false false)
    let Q := bidirectional C (oracle gap n true false)
    (Q.trans P.symm) v + (Q.trans P.symm).symm v = (2*gap.mu : ℂ) • v := by
  dsimp only
  simp only [bidirectional,oracle,ofUnitary_unitary,signed_false]
  ext i
  apply (WithLp.equiv 2 (_ × _)).injective
  apply Prod.ext
  · change (base gap n false).symm (base gap n true (v i).fst) +
      (base gap n true).symm (base gap n false (v i).fst) = (2*gap.mu : ℂ) • (v i).fst
    exact base_relative gap _
  · change base gap n false ((base gap n true).symm (v i).snd) +
      base gap n true ((base gap n false).symm (v i).snd) = (2*gap.mu : ℂ) • (v i).snd
    exact base_relative_inverse gap _

end ELV.FourOracles
