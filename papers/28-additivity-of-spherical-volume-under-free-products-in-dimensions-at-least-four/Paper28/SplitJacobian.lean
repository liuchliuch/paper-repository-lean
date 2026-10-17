import Paper28.SplitRight
import Paper28.JacobianIsometries

/-! The sharp joint bound for the canonical differentials of the two
complementary coordinate partitions. It is derived from the actual folding
estimate, with every zero-coordinate stratum included. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Paper28
attribute [local irreducible] frameJacobian
open WithLp
open scoped InnerProductSpace
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem split_partitions_nJacobian (hFischer : FischerInput)
    (u : EuclideanSpace ℝ (α ⊕ (Unit ⊕ β)))
    (S : Submodule ℝ (EuclideanSpace ℝ (α ⊕ (Unit ⊕ β))))
    (hn : 4 ≤ Module.finrank ℝ S)
    (htan : ∀ v : S, ⟪u, v.val⟫_ℝ = 0)
    (hzero : ∀ i, u i = 0 → ∀ v : S, v.val i = 0) :
    frameJacobian (fun v : S => shadowDifferential splitLeft u v.val) +
      frameJacobian (fun v : S => shadowDifferential splitRight u v.val) ≤ 1 := by
  classical
  let A := coordinateTriple (Equiv.refl (α ⊕ (Unit ⊕ β)))
  let S' := S.map A.toLinearEquiv.toLinearMap
  let e : S ≃ₗᵢ[ℝ] S' := A.submoduleMap S
  have hdim : 4 ≤ Module.finrank ℝ S' := by rw [← e.toLinearEquiv.finrank_eq]; exact hn
  have ht : ∀ v : S', ⟪A u, v.val⟫_ℝ = 0 := by
    intro v
    obtain ⟨w, rfl⟩ := e.surjective v
    change ⟪A u, A w.val⟫_ℝ = 0
    rw [A.inner_map_map]
    exact htan w
  have hL : (A u).snd = 0 → ∀ v : S', v.val.snd = 0 := by
    intro hx v
    obtain ⟨w, rfl⟩ := e.surjective v
    change (A w.val).snd = 0
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · have hz : u (.inr (.inl ())) = 0 := congrArg (fun q => q.fst) hx
      exact hzero _ hz w
    · ext b
      have hy : u (.inr (.inr b)) = 0 := congrArg (fun q => q.snd b) hx
      exact hzero _ hy w
  have hR : (reverseTriple (A u)).snd = 0 → ∀ v : S', (reverseTriple v.val).snd = 0 := by
    intro hx v
    obtain ⟨w, rfl⟩ := e.surjective v
    change (reverseTriple (A w.val)).snd = 0
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · have hz : u (.inr (.inl ())) = 0 := congrArg (fun q => q.fst) hx
      exact hzero _ hz w
    · ext a
      have hy : u (.inl a) = 0 := congrArg (fun q => q.snd a) hx
      exact hzero _ hy w
  have hfL : PreservesFrameSums (fun v : S' => normFoldDerivative (A u) v.val) := by
    intro v a
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
  have hfR : PreservesFrameSums (fun v : S' => rightFoldDerivative (A u) v.val) := by
    intro v a
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
  have hJL : frameJacobian (fun v : S => shadowDifferential splitLeft u v.val) =
      frameJacobian (fun v : S' => normFoldDerivative (A u) v.val) := by
    calc
      _ = frameJacobian (fun v : S => normFoldDerivative (A u) (e v).val) := by
        apply frameJacobian_congr_inner
        intro v w
        exact splitLeft_differential_inner u v.val w.val
          (fun a ha => hzero (.inl a) ha v) (fun a ha => hzero (.inl a) ha w)
      _ = _ := by
        conv_rhs => rw [frameJacobian_eq_gram_basis
          (fun v : S' => normFoldDerivative (A u) v.val) hfL
          ((stdOrthonormalBasis ℝ S).map e)]
        conv_lhs => unfold frameJacobian
        rfl
  have hJR : frameJacobian (fun v : S => shadowDifferential splitRight u v.val) =
      frameJacobian (fun v : S' => rightFoldDerivative (A u) v.val) := by
    calc
      _ = frameJacobian (fun v : S => rightFoldDerivative (A u) (e v).val) := by
        apply frameJacobian_congr_inner
        intro v w
        exact splitRight_differential_inner u v.val w.val
          (fun b hb => hzero (.inr (.inr b)) hb v)
          (fun b hb => hzero (.inr (.inr b)) hb w)
      _ = _ := by
        conv_rhs => rw [frameJacobian_eq_gram_basis
          (fun v : S' => rightFoldDerivative (A u) v.val) hfR
          ((stdOrthonormalBasis ℝ S).map e)]
        conv_lhs => unfold frameJacobian
        rfl
  rw [hJL, hJR]
  exact two_foldings_nJacobian_stratified hFischer (A u) S' hdim ht hL hR

end Paper28
