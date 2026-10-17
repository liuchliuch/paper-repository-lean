import Paper28.BassSerreObjectInput
import Paper28.TreeBranchNaturality
import Mathlib.Algebra.Group.Action.Sum

/-! Actual left translation of the coset tree, the representative-change
cocycle, and native equivariance of its branch labels. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open SimpleGraph
variable {G : Type} [Group G] {A B : Subgroup G}

theorem bassSerre_coset_pair_translate_iff (γ : G) (a : G ⧸ A) (b : G ⧸ B) :
    (∃ g : G, QuotientGroup.mk g = γ • a ∧ QuotientGroup.mk g = γ • b) ↔
      ∃ g : G, QuotientGroup.mk g = a ∧ QuotientGroup.mk g = b := by
  constructor
  · rintro ⟨g,ha,hb⟩
    refine ⟨γ⁻¹*g,?_,?_⟩
    · simpa only [← MulAction.Quotient.smul_mk,smul_eq_mul,inv_smul_smul] using congrArg (fun x : G ⧸ A => γ⁻¹ • x) ha
    · simpa only [← MulAction.Quotient.smul_mk,smul_eq_mul,inv_smul_smul] using congrArg (fun x : G ⧸ B => γ⁻¹ • x) hb
  · rintro ⟨g,ha,hb⟩
    refine ⟨γ*g,?_,?_⟩
    · simpa only [← MulAction.Quotient.smul_mk,smul_eq_mul] using congrArg (fun x : G ⧸ A => γ • x) ha
    · simpa only [← MulAction.Quotient.smul_mk,smul_eq_mul] using congrArg (fun x : G ⧸ B => γ • x) hb

def bassSerreTranslate (γ : G) : bassSerreGraph A B ≃g bassSerreGraph A B where
  toEquiv := MulAction.toPerm γ
  map_rel_iff' := by
    intro v w
    cases v <;> cases w <;>
      simp only [MulAction.toPerm_apply,Sum.smul_inl,Sum.smul_inr,bassSerreGraph,bassSerreAdj]
    · exact bassSerre_coset_pair_translate_iff γ _ _
    · exact bassSerre_coset_pair_translate_iff γ _ _

theorem bassSerreTranslate_edge (γ g : G) :
    (bassSerreTranslate (A := A) (B := B) γ).mapEdgeSet (bassSerreEdge A B g) = bassSerreEdge A B (γ*g) := by
  apply Subtype.ext
  rfl

def cosetTranslationCocycle (A : Subgroup G) (γ : G) (v : G ⧸ A) : A :=
  ⟨(γ • v).out⁻¹*(γ*v.out),by
    apply QuotientGroup.leftRel_apply.mp
    apply Quotient.exact
    calc
      QuotientGroup.mk (γ • v).out = (γ • v : G ⧸ A) := QuotientGroup.out_eq' _
      _ = QuotientGroup.mk (γ*v.out) := by
        rw [← smul_eq_mul,← MulAction.Quotient.smul_mk,QuotientGroup.out_eq']⟩

theorem cosetTranslationCocycle_formula (γ : G) (v : G ⧸ A) :
    (γ • v).out*(cosetTranslationCocycle A γ v).val = γ*v.out := by
  simp [cosetTranslationCocycle]

theorem bassSerreLabelA_translate (T : BassSerreObject A B) (γ : G) (v : G ⧸ A) (a : A) :
    T.leftLabel (γ • v) (cosetTranslationCocycle A γ v*a) =
      (bassSerreTranslate (A := A) (B := B) γ).mapNeighborSet (.inl v) (T.leftLabel v a) := by
  apply Subtype.ext
  rw [T.leftLabel_formula]
  change bassSerreRight A B ((γ • v).out*((cosetTranslationCocycle A γ v).val*a.val)) =
    γ • (T.leftLabel v a).val
  rw [T.leftLabel_formula,← mul_assoc,cosetTranslationCocycle_formula]
  simp only [bassSerreRight,Sum.smul_inr,MulAction.Quotient.smul_mk,smul_eq_mul,mul_assoc]

theorem bassSerreBranchA_translate (T : BassSerreObject A B) (γ : G) (v : G ⧸ A) (g : G) :
    bassSerreBranchA T (γ • v) (γ*g) = cosetTranslationCocycle A γ v*bassSerreBranchA T v g := by
  apply (T.leftLabel (γ • v)).injective
  rw [bassSerreLabelA_translate]
  simp only [bassSerreBranchA,Equiv.apply_symm_apply]
  rw [← bassSerreTranslate_edge γ g]
  exact treeBranch_automorphism _ T.isTree (bassSerreTranslate γ) (.inl v) (bassSerreEdge A B g)

theorem bassSerreLabelB_translate (T : BassSerreObject A B) (γ : G) (v : G ⧸ B) (b : B) :
    T.rightLabel (γ • v) (cosetTranslationCocycle B γ v*b) =
      (bassSerreTranslate (A := A) (B := B) γ).mapNeighborSet (.inr v) (T.rightLabel v b) := by
  apply Subtype.ext
  rw [T.rightLabel_formula]
  change bassSerreLeft A B ((γ • v).out*((cosetTranslationCocycle B γ v).val*b.val)) =
    γ • (T.rightLabel v b).val
  rw [T.rightLabel_formula,← mul_assoc,cosetTranslationCocycle_formula]
  simp only [bassSerreLeft,Sum.smul_inl,MulAction.Quotient.smul_mk,smul_eq_mul,mul_assoc]

theorem bassSerreBranchB_translate (T : BassSerreObject A B) (γ : G) (v : G ⧸ B) (g : G) :
    bassSerreBranchB T (γ • v) (γ*g) = cosetTranslationCocycle B γ v*bassSerreBranchB T v g := by
  apply (T.rightLabel (γ • v)).injective
  rw [bassSerreLabelB_translate]
  simp only [bassSerreBranchB,Equiv.apply_symm_apply]
  rw [← bassSerreTranslate_edge γ g]
  exact treeBranch_automorphism _ T.isTree (bassSerreTranslate γ) (.inr v) (bassSerreEdge A B g)

end Paper28
