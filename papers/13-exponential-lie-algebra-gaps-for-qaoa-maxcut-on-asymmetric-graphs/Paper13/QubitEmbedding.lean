import Paper13.AssemblyBasis
import Paper13.GraphDynamics
import Mathlib.Logic.Equiv.Set
noncomputable section
namespace Paper13
open Matrix
open scoped Kronecker
attribute [local instance] Classical.propDecidable

abbrev OutsideRegister {m n : ℕ} (f : Fin m ↪ Fin n) := {v : Fin n // v ∉ Set.range f}

def registerVertexSplit {m n : ℕ} (f : Fin m ↪ Fin n) : Fin m ⊕ OutsideRegister f ≃ Fin n where
  toFun := Sum.elim f Subtype.val
  invFun v := if h : ∃ i, f i=v then Sum.inl (Classical.choose h) else Sum.inr ⟨v,h⟩
  left_inv x := by
    cases x with
    | inl i =>
      have hv : ∃ j, f j=f i := ⟨i,rfl⟩
      simp only [Sum.elim_inl,dif_pos hv]
      congr 1
      apply f.injective
      exact Classical.choose_spec hv
    | inr v =>
      change (if h : ∃ i, f i=v.val then Sum.inl (Classical.choose h) else Sum.inr ⟨v.val,h⟩) = Sum.inr v
      have hn : ¬ ∃ i, f i = v.val := v.property
      rw [dif_neg hn]
  right_inv v := by
    change Sum.elim f Subtype.val (if h : ∃ i, f i=v then Sum.inl (Classical.choose h) else Sum.inr ⟨v,h⟩) = v
    split_ifs with h
    · exact Classical.choose_spec h
    · rfl

def registerBasis {m n : ℕ} (f : Fin m ↪ Fin n) :
    (QubitBasis m × (OutsideRegister f → Fin 2)) ≃ QubitBasis n :=
  (Equiv.sumArrowEquivProdArrow (Fin m) (OutsideRegister f) (Fin 2)).symm.trans
    (Equiv.arrowCongr (registerVertexSplit f) (Equiv.refl (Fin 2)))

lemma registerBasis_inside {m n : ℕ} (f : Fin m ↪ Fin n)
    (x : QubitBasis m × (OutsideRegister f → Fin 2)) (i : Fin m) : registerBasis f x (f i)=x.1 i := by
  change Sum.elim x.1 x.2 ((registerVertexSplit f).symm (f i)) = x.1 i
  have hi : f i = registerVertexSplit f (Sum.inl i) := rfl
  rw [hi,Equiv.symm_apply_apply]
  rfl

lemma registerBasis_outside {m n : ℕ} (f : Fin m ↪ Fin n)
    (x : QubitBasis m × (OutsideRegister f → Fin 2)) (i : OutsideRegister f) : registerBasis f x i.val=x.2 i := by
  change Sum.elim x.1 x.2 ((registerVertexSplit f).symm i.val) = x.2 i
  have hi : i.val = registerVertexSplit f (Sum.inr i) := rfl
  rw [hi,Equiv.symm_apply_apply]
  rfl

/-- Embedding any finite register is an actual complex algebra homomorphism. -/
def registerLift {m n : ℕ} (f : Fin m ↪ Fin n) : Op m →ₐ[ℂ] Op n where
  toFun A := Matrix.reindexAlgEquiv ℂ ℂ (registerBasis f) (A ⊗ₖ (1 : Matrix (OutsideRegister f → Fin 2) (OutsideRegister f → Fin 2) ℂ))
  map_zero' := by simp
  map_one' := by simp [Matrix.one_kronecker_one]
  map_add' A B := by rw [Matrix.add_kronecker, map_add]
  map_mul' A B := by
    rw [← map_mul, ← Matrix.mul_kronecker_mul, one_mul]
  commutes' z := by simp [Algebra.algebraMap_eq_smul_one,Matrix.smul_kronecker,Matrix.one_kronecker_one]

lemma register_outside_iff {m n : ℕ} (f : Fin m ↪ Fin n) (i : Fin m)
    (x y : QubitBasis m × (OutsideRegister f → Fin 2)) :
    (∀ w, w ≠ f i → registerBasis f x w=registerBasis f y w) ↔
      (∀ j, j ≠ i → x.1 j=y.1 j) ∧ x.2=y.2 := by
  constructor
  · intro h
    constructor
    · intro j hj
      have hn : f j ≠ f i := fun he => hj (f.injective he)
      simpa only [registerBasis_inside] using h (f j) hn
    · funext w
      have hn : w.val ≠ f i := fun he => w.property ⟨i,he.symm⟩
      simpa only [registerBasis_outside] using h w.val hn
  · rintro ⟨hi,ho⟩ w hw
    obtain ⟨j,hj⟩ := (registerVertexSplit f).surjective w
    cases j with
    | inl j =>
      change f j=w at hj
      subst w
      rw [registerBasis_inside,registerBasis_inside]
      exact hi j (fun he => hw (congrArg f he))
    | inr j =>
      change j.val=w at hj
      subst w
      rw [registerBasis_outside,registerBasis_outside,ho]

lemma registerLift_embed {m n : ℕ} (f : Fin m ↪ Fin n) (i : Fin m) (A : Op1) :
    registerLift f (embed A i)=embed A (f i) := by
  apply (Matrix.reindexAlgEquiv ℂ ℂ (registerBasis f).symm).injective
  have he : Matrix.reindexAlgEquiv ℂ ℂ (registerBasis f).symm (registerLift f (embed A i)) =
      embed A i ⊗ₖ (1 : Matrix (OutsideRegister f → Fin 2) (OutsideRegister f → Fin 2) ℂ) := by
    exact (Matrix.reindexAlgEquiv ℂ ℂ (registerBasis f)).symm_apply_apply _
  rw [he]
  ext x y
  change embed A i x.1 y.1 * (1 : Matrix (OutsideRegister f → Fin 2) (OutsideRegister f → Fin 2) ℂ) x.2 y.2 =
    embed A (f i) (registerBasis f x) (registerBasis f y)
  simp only [embed,register_outside_iff,registerBasis_inside,Matrix.one_apply]
  split_ifs <;> simp_all

lemma registerLift_X {m n : ℕ} (f : Fin m ↪ Fin n) (i : Fin m) : registerLift f (Xv i)=Xv (f i) :=
  registerLift_embed f i pauliX

lemma registerLift_Z {m n : ℕ} (f : Fin m ↪ Fin n) (i : Fin m) : registerLift f (Zv i)=Zv (f i) :=
  registerLift_embed f i pauliZ

lemma registerLift_ZZ {m n : ℕ} (f : Fin m ↪ Fin n) (i j : Fin m) : registerLift f (ZZ i j)=ZZ (f i) (f j) := by
  simp only [ZZ,map_mul,registerLift_Z]

/-- A graph embedding transports every genuinely generated Lie element. -/
theorem registerLift_lie {m n : ℕ} (f : Fin m ↪ Fin n) (G : SimpleGraph (Fin m)) (H : SimpleGraph (Fin n))
    (hG : ∀ i j, G.Adj i j → H.Adj (f i) (f j)) :
    ∀ A ∈ graphMa G, registerLift f A ∈ graphMa H := by
  let L : Submodule ℝ (Op m) := (graphMa H).comap ((registerLift f).toLinearMap.restrictScalars ℝ)
  apply lieClosure_le (L := L)
  · rintro A (⟨v,rfl⟩ | ⟨e,he,rfl⟩)
    · change registerLift f (Complex.I • Xv v) ∈ graphMa H
      rw [map_smul,registerLift_X]
      exact subset_lieClosure (Or.inl ⟨f v,rfl⟩)
    · have ha : G.Adj e.1 e.2 := (Finset.mem_filter.mp he).2.2
      have hfa := hG _ _ ha
      have hne : f e.1 ≠ f e.2 := hfa.ne
      change registerLift f (Complex.I • ZZ e.1 e.2) ∈ graphMa H
      rw [map_smul,registerLift_ZZ]
      apply subset_lieClosure
      right
      rcases lt_or_gt_of_ne hne with h | h
      · exact ⟨(f e.1,f e.2),by simp [graphEdges,h,hfa],rfl⟩
      · refine ⟨(f e.2,f e.1),by simp [graphEdges,h,H.symm hfa],?_⟩
        congr 1
        exact (Zv_commute _ _).eq
  · intro A B hA hB
    change registerLift f (A*B-B*A) ∈ graphMa H
    rw [map_sub,map_mul,map_mul]
    exact lieClosure_comm hA hB
end Paper13
