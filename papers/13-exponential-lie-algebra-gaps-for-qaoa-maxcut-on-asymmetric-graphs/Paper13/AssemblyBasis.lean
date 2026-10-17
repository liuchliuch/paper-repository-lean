import Paper13.TensorControls
import Paper13.GraphOperators
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators

/-- The canonical regrouping of the kh qubits into k copies of h qubits. -/
def assemblyBasis (k h : ℕ) : (Fin k → QubitBasis h) ≃ QubitBasis (k*h) where
  toFun x i := x (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  invFun x v u := x (finProdFinEquiv (v,u))
  left_inv x := by
    funext v u
    change (Function.uncurry x) (finProdFinEquiv.symm (finProdFinEquiv (v,u))) = x v u
    rw [Equiv.symm_apply_apply]
    rfl
  right_inv x := by
    funext i
    change x (finProdFinEquiv (finProdFinEquiv.symm i)) = x i
    rw [Equiv.apply_symm_apply]

@[simp] lemma assemblyBasis_site {k h : ℕ} (x : Fin k → QubitBasis h) (v : Fin k) (u : Fin h) :
    assemblyBasis k h x (finProdFinEquiv (v,u)) = x v u := by
  change (Function.uncurry x) (finProdFinEquiv.symm (finProdFinEquiv (v,u))) = x v u
  rw [Equiv.symm_apply_apply]
  rfl

/-- Regroup the actual matrices, without changing their Hilbert space or dynamics. -/
def assemblyReindex (k h : ℕ) : Op (k*h) ≃ₐ[ℂ]
    Matrix (Fin k → QubitBasis h) (Fin k → QubitBasis h) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (assemblyBasis k h).symm

lemma assemblyReindex_apply (k h : ℕ) (A : Op (k*h)) (x y : Fin k → QubitBasis h) :
    assemblyReindex k h A x y = A (assemblyBasis k h x) (assemblyBasis k h y) := rfl

lemma assembly_outside_iff {k h : ℕ} (v : Fin k) (u : Fin h) (x y : Fin k → QubitBasis h) :
    (∀ i : Fin (k*h), i ≠ finProdFinEquiv (v,u) →
      assemblyBasis k h x i = assemblyBasis k h y i) ↔
    (∀ w, w ≠ v → x w = y w) ∧ (∀ t, t ≠ u → x v t = y v t) := by
  constructor
  · intro hi
    constructor
    · intro w hw
      funext t
      have hn : finProdFinEquiv (w,t) ≠ finProdFinEquiv (v,u) := by
        intro he
        exact hw (congrArg Prod.fst (finProdFinEquiv.injective he))
      simpa only [assemblyBasis_site] using hi (finProdFinEquiv (w,t)) hn
    · intro t ht
      have hn : finProdFinEquiv (v,t) ≠ finProdFinEquiv (v,u) := by
        intro he
        exact ht (congrArg Prod.snd (finProdFinEquiv.injective he))
      simpa only [assemblyBasis_site] using hi (finProdFinEquiv (v,t)) hn
  · rintro ⟨hc,hl⟩ i hi
    obtain ⟨⟨w,t⟩,rfl⟩ := finProdFinEquiv.surjective i
    rw [assemblyBasis_site,assemblyBasis_site]
    by_cases hw : w = v
    · subst w
      apply hl
      intro ht
      subst t
      exact hi rfl
    · exact congrFun (hc w hw) t

/-- A Pauli control on an actual graph vertex becomes its local copy embedding. -/
theorem assemblyReindex_embed {k h : ℕ} (v : Fin k) (u : Fin h) (A : Op1) :
    assemblyReindex k h (embed A (finProdFinEquiv (v,u))) = liftSite v (embed A u) := by
  ext x y
  simp only [assemblyReindex_apply, embed, liftSite_entry, assembly_outside_iff]
  have hv : assemblyBasis k h x (finProdFinEquiv (v,u)) = x v u := by exact assemblyBasis_site _ _ _
  have hw : assemblyBasis k h y (finProdFinEquiv (v,u)) = y v u := by exact assemblyBasis_site _ _ _
  rw [hv,hw]
  split_ifs <;> simp_all

lemma assemblyReindex_X {k h : ℕ} (v : Fin k) (u : Fin h) :
    assemblyReindex k h (Xv (finProdFinEquiv (v,u))) = liftSite v (Xv u) := assemblyReindex_embed v u pauliX

lemma assemblyReindex_Z {k h : ℕ} (v : Fin k) (u : Fin h) :
    assemblyReindex k h (Zv (finProdFinEquiv (v,u))) = liftSite v (Zv u) := assemblyReindex_embed v u pauliZ

lemma assemblyReindex_ZZ {k h : ℕ} (v w : Fin k) (u t : Fin h) :
    assemblyReindex k h (ZZ (finProdFinEquiv (v,u)) (finProdFinEquiv (w,t))) =
      liftSite v (Zv u) * liftSite w (Zv t) := by
  simp only [ZZ,map_mul,assemblyReindex_Z]

/-- The actual shared mixer is the sum of the gadget mixers. -/
theorem assemblyReindex_mixer (k h : ℕ) :
    assemblyReindex k h (HXFull (k*h)) = ∑ v : Fin k, liftSite v (HXFull h) := by
  rw [HXFull,map_sum]
  have hsum := finProdFinEquiv.sum_comp (fun i : Fin (k*h) => assemblyReindex k h (Xv i))
  rw [← hsum,Fintype.sum_prod_type]
  simp only [assemblyReindex_X]
  apply Finset.sum_congr rfl
  intro v hv
  exact (liftSite_sum v Finset.univ (fun u : Fin h => Xv u)).symm
lemma assemblyBasis_flip (k h : ℕ) (x : Fin k → QubitBasis h) :
    assemblyBasis k h (fun v => flipState (x v)) = flipState (assemblyBasis k h x) := by
  rfl

/-- Regrouping preserves the literal global bit flip. -/
theorem assemblyReindex_bitFlip (k h : ℕ) :
    assemblyReindex k h (bitFlip (k*h)) = tensorMatrix (fun _ : Fin k => bitFlip h) := by
  ext x y
  rw [assemblyReindex_apply]
  change (if assemblyBasis k h y = flipState (assemblyBasis k h x) then (1 : ℂ) else 0) =
    ∏ v, bitFlip h (x v) (y v)
  have he : assemblyBasis k h y = flipState (assemblyBasis k h x) ↔ y = (fun v => flipState (x v)) := by
    rw [← assemblyBasis_flip]
    exact (assemblyBasis k h).injective.eq_iff
  simp only [he]
  by_cases hy : y = (fun v => flipState (x v))
  · subst y
    simp [bitFlip]
  · rw [if_neg hy]
    obtain ⟨v,hv⟩ := Function.ne_iff.mp hy
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    exact if_neg hv

lemma assemblyReindex_conjTranspose {k h : ℕ} (A : Op (k*h)) :
    assemblyReindex k h Aᴴ = (assemblyReindex k h A)ᴴ := by
  ext x y
  rfl

lemma assemblyReindex_trace {k h : ℕ} (A : Op (k*h)) :
    Matrix.trace (assemblyReindex k h A) = Matrix.trace A := by
  change (∑ x, A (assemblyBasis k h x) (assemblyBasis k h x)) = ∑ y, A y y
  exact (assemblyBasis k h).sum_comp (fun x => A x x)
end Paper13

