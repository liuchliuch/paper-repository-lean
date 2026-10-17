import Paper13.GraphDynamics
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def coordinateAction {n : ℕ} (φ : Equiv.Perm (Fin n)) : Op n ≃ₐ[ℂ] Op n :=
  Matrix.reindexAlgEquiv ℂ ℂ (Equiv.arrowCongr φ (Equiv.refl (Fin 2)))
lemma coordinateAction_entry {n : ℕ} (φ : Equiv.Perm (Fin n)) (A : Op n) (x y : QubitBasis n) :
    coordinateAction φ A x y=A (x ∘ φ) (y ∘ φ) := rfl

lemma coordinateAction_embed {n : ℕ} (φ : Equiv.Perm (Fin n)) (A : Op1) (v : Fin n) :
    coordinateAction φ (embed A v)=embed A (φ v) := by
  ext x y
  rw [coordinateAction_entry]
  have hoff : (∀ w, w≠v → (x ∘ φ) w=(y ∘ φ) w) ↔ ∀ w, w≠φ v → x w=y w := by
    constructor
    · intro h w hw
      obtain ⟨z,rfl⟩ := φ.surjective w
      exact h z (fun he => hw (congrArg φ he))
    · intro h w hw
      exact h (φ w) (fun he => hw (φ.injective he))
  by_cases h : ∀ w, w≠v → (x ∘ φ) w=(y ∘ φ) w
  · have h' := hoff.mp h
    have h'' : ∀ w, w≠v → x (φ w)=y (φ w) := h
    simp only [embed,Function.comp_apply,if_pos h'',if_pos h']
  · have h' : ¬∀ w, w≠φ v → x w=y w := fun h' => h (hoff.mpr h')
    have h'' : ¬∀ w, w≠v → x (φ w)=y (φ w) := h
    simp only [embed,Function.comp_apply,if_neg h'',if_neg h']

lemma coordinateAction_X {n : ℕ} (φ : Equiv.Perm (Fin n)) (v : Fin n) :
    coordinateAction φ (Xv v)=Xv (φ v) := coordinateAction_embed φ pauliX v
lemma coordinateAction_Z {n : ℕ} (φ : Equiv.Perm (Fin n)) (v : Fin n) :
    coordinateAction φ (Zv v)=Zv (φ v) := coordinateAction_embed φ pauliZ v
lemma coordinateAction_ZZ {n : ℕ} (φ : Equiv.Perm (Fin n)) (u v : Fin n) :
    coordinateAction φ (ZZ u v)=ZZ (φ u) (φ v) := by simp only [ZZ,map_mul,coordinateAction_Z]
lemma coordinateAction_mixer {n : ℕ} (φ : Equiv.Perm (Fin n)) : coordinateAction φ (HXFull n)=HXFull n := by
  simp only [HXFull,map_sum,coordinateAction_X]
  exact Equiv.sum_comp φ Xv

lemma graphCost_double {n : ℕ} (G : SimpleGraph (Fin n)) :
    (∑ e : Fin n × Fin n, if G.Adj e.1 e.2 then ZZ e.1 e.2 else 0)=graphCost G+graphCost G := by
  have hh (e : Fin n × Fin n) : (if G.Adj e.1 e.2 then ZZ e.1 e.2 else 0)=
      (if e.1<e.2 ∧ G.Adj e.1 e.2 then ZZ e.1 e.2 else 0)+
      (if e.2<e.1 ∧ G.Adj e.1 e.2 then ZZ e.1 e.2 else 0) := by
    rcases lt_trichotomy e.1 e.2 with h | h | h
    · simp [h,not_lt_of_ge h.le]
    · simp [h]
    · simp [h,not_lt_of_ge h.le]
  rw [Finset.sum_congr rfl (fun e _ => hh e),Finset.sum_add_distrib]
  have hforward : (∑ e : Fin n × Fin n, if e.1<e.2 ∧ G.Adj e.1 e.2 then ZZ e.1 e.2 else 0)=graphCost G := by
    simp only [graphCost,graphEdges,Finset.sum_filter]
  rw [hforward]
  congr 1
  rw [←hforward]
  apply Fintype.sum_equiv (Equiv.prodComm (Fin n) (Fin n))
  intro e
  change (if e.2<e.1 ∧ G.Adj e.1 e.2 then ZZ e.1 e.2 else 0)=
    (if e.2<e.1 ∧ G.Adj e.2 e.1 then ZZ e.2 e.1 else 0)
  rw [G.adj_comm e.2 e.1]
  split_ifs
  · exact (Zv_commute _ _).eq
  · rfl

lemma coordinateAction_cost {n : ℕ} (G : SimpleGraph (Fin n)) (φ : G ≃g G) :
    coordinateAction φ.toEquiv (graphCost G)=graphCost G := by
  have hh := congrArg (coordinateAction φ.toEquiv) (graphCost_double G)
  simp only [map_sum,map_add,apply_ite,map_zero,coordinateAction_ZZ] at hh
  have hsum : (∑ e : Fin n × Fin n, if G.Adj e.1 e.2 then ZZ (φ e.1) (φ e.2) else 0)=
      ∑ e : Fin n × Fin n, if G.Adj e.1 e.2 then ZZ e.1 e.2 else 0 := by
    calc
      _ = ∑ e : Fin n × Fin n, if G.Adj (φ e.1) (φ e.2) then ZZ (φ e.1) (φ e.2) else 0 := by
        apply Finset.sum_congr rfl
        intro e he
        rw [φ.map_rel_iff]
      _ = _ := Equiv.sum_comp (Equiv.prodCongr φ.toEquiv φ.toEquiv) (fun e => if G.Adj e.1 e.2 then ZZ e.1 e.2 else 0)
  have hh' := hsum.symm.trans hh
  rw [graphCost_double] at hh'
  ext x y
  have he := congrArg (fun A : Op n => A x y) hh' 
  change graphCost G x y+graphCost G x y = coordinateAction φ.toEquiv (graphCost G) x y+coordinateAction φ.toEquiv (graphCost G) x y at he
  linear_combination (-1/2 : ℂ)*he

lemma graphFixed_iff_action {n : ℕ} (G : SimpleGraph (Fin n)) (A : Op n) :
    A ∈ graphFixed G ↔ ∀ φ : G ≃g G, coordinateAction φ.toEquiv A=A := by
  constructor
  · intro h φ; ext x y; exact h φ x y
  · intro h φ x y; exact congrArg (fun B : Op n => B x y) (h φ)

/-- Shared controls are fixed by every actual graph automorphism. -/
theorem graphStd_le_fixed {n : ℕ} (G : SimpleGraph (Fin n)) : graphStd G ≤ graphFixed G := by
  apply lieClosure_le
  · intro A hA
    change A ∈ graphFixed G
    rw [graphFixed_iff_action]
    rcases mem_stdGens_iff.mp hA with rfl | rfl
    · intro φ
      simp only [iMul,map_smul,coordinateAction_mixer]
    · intro φ
      simp only [iMul,map_smul,coordinateAction_cost]
  · intro A B hA hB
    rw [graphFixed_iff_action] at hA hB ⊢
    intro φ
    simp only [comm,map_sub,map_mul,hA φ,hB φ]

/-- The standard-to-natural inclusion holds for all graphs, before imposing rigidity. -/
theorem graphStd_le_nat {n : ℕ} (G : SimpleGraph (Fin n)) : graphStd G ≤ graphNat G :=
  le_inf (graphStd_le_ma G) (graphStd_le_fixed G)
end Paper13
