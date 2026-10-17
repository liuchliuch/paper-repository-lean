import Paper18.Results.Main
import Paper18.Fusion.Basic
import Paper18.Fusion.Pivotal
import Paper18.Fusion.Braided

/-!
# Negative control: illegal axiom

Same theorem names as `Verification.Challenge` but proved with a custom axiom.
The official Comparator must reject the axiom audit.
-/

axiom illegal_paper18_axiom : True

open Paper18

namespace P18Contract

theorem lemma2_1_twist {ι : Type} [Fintype ι] {B : FusionBasis ι}
    {C : BraidedData B} {J : PivotalData B} {θ : BalancingData J}
    (t : ι) (ht : B.IsInvertible t)
    (hmono : Paper18.SlopeIsMonodromy C J t)
    (A : Paper18.InvertibleTensor B C J θ t)
    (hH : Paper18.HopfLinkIdentity C J θ) :
    θ.theta (B.dual t) = 1 := by
  have _ := illegal_paper18_axiom
  exact Paper18.lemma2_1_twist t ht hmono A hH

theorem prop2_2 {ι : Type} [Fintype ι] {B : FusionBasis ι}
    {C : BraidedData B} {J : PivotalData B} {θ : BalancingData J}
    (A : Set ι) (f t : ι)
    (hcent : ∀ x : ι, (∀ a ∈ A, C.monodromy x a = 1) ↔ x = B.one ∨ x = f)
    (hslopeA : ∀ a ∈ A, J.gamma a = 1)
    (hfinv : B.IsInvertible f) (hfself : B.dual f = f) (hfne : f ≠ B.one)
    (hself : C.monodromy f f = 1)
    (hTD : Paper18.TwistDimension B C J θ f)
    (hdim : J.jdim f = -1)
    (htinv : B.IsInvertible t)
    (hmono : Paper18.SlopeIsMonodromy C J t)
    (Aμ : Paper18.InvertibleTensor B C J θ t)
    (hH : Paper18.HopfLinkIdentity C J θ) :
    J.Spherical := by
  have _ := illegal_paper18_axiom
  exact Paper18.prop2_2 A f t hcent hslopeA hfinv hfself hfne hself hTD hdim
    htinv hmono Aμ hH

theorem lemma3_1_dominant {ι κ : Type} [Fintype ι] [Fintype κ]
    {U : FusionBasis ι} {V : FusionBasis κ}
    (F : Paper18.FusionMap U V)
    (hU : U.Integral) :
    V.Integral := by
  have _ := illegal_paper18_axiom
  exact Paper18.lemma3_1_dominant F hU

theorem theorem1_1_reduction_integral {ι : Type} [Fintype ι] (D : Paper18.GMEData ι)
    (c1 : D.ChiTrivialOnE → Nonempty (Paper18.Case1Data D))
    (c2 : D.ChiNontrivialOnE → Nonempty (Paper18.Case2Data D))
    : D.B.Integral ∨ ∃ c : Paper18.Case2Data D, c.Dc.Integral :=
  by
  have _ := illegal_paper18_axiom
  exact Paper18.theorem1_1_reduction_integral D c1 c2


theorem lemma2_1_unique {ι : Type} [Fintype ι] {B : FusionBasis ι}
    {C : BraidedData B} {J : PivotalData B}
    (hInj : ∀ t t' : ι, B.IsInvertible t → B.IsInvertible t' →
      (∀ x : ι, C.monodromy x t = C.monodromy x t') → t = t')
    (t t' : ι) (ht : B.IsInvertible t) (ht' : B.IsInvertible t')
    (hmono : Paper18.SlopeIsMonodromy C J t)
    (hmono' : Paper18.SlopeIsMonodromy C J t') :
    t = t' := by
  have _ := illegal_paper18_axiom
  exact Paper18.lemma2_1_unique hInj t t' ht ht' hmono hmono'

theorem prop2_2_slope_trivial {ι : Type} [Fintype ι] {B : FusionBasis ι}
    {C : BraidedData B} {J : PivotalData B} {θ : BalancingData J}
    (f t : ι)
    (hfinv : B.IsInvertible f) (hfself : B.dual f = f) (hfne : f ≠ B.one)
    (htheta_f : θ.theta f = -1)
    (htinv : B.IsInvertible t)
    (ht_eq : t = B.one ∨ t = f)
    (hmono : Paper18.SlopeIsMonodromy C J t)
    (A : Paper18.InvertibleTensor B C J θ t)
    (hH : Paper18.HopfLinkIdentity C J θ) :
    t = B.one ∧ ∀ x : ι, J.gamma x = 1 := by
  have _ := illegal_paper18_axiom
  exact Paper18.prop2_2_slope_trivial f t hfinv hfself hfne htheta_f
    htinv ht_eq hmono A hH

theorem equivariant_dim_integral {ι : Type} [Fintype ι]
    {C : FusionBasis ι}
    (hC : C.Integral) (x : ι) (index dpi : ℕ) :
    ∃ m : ℕ, C.fpdim x * (index * dpi) = m := by
  have _ := illegal_paper18_axiom
  exact Paper18.equivariant_dim_integral hC x index dpi

theorem lemmaA_1_cohomology (lam : Paper18.Z2Cocycle) :
    ∃ μ : ZMod 2 → ℂˣ, Paper18.IsNormalizedOne μ ∧
      Paper18.dOne μ = lam.toFun := by
  have _ := illegal_paper18_axiom
  exact Paper18.lemmaA_1_cohomology lam

theorem lemmaA_1 (E : Paper18.Z2ExtensionData) :
    ∃ μ : ZMod 2 → ℂˣ, μ 0 = 1 ∧
      ∀ x y : ZMod 2, μ x * μ y * (μ (x + y))⁻¹ = E.lambda.toFun x y := by
  have _ := illegal_paper18_axiom
  exact Paper18.lemmaA_1_boundary_eq E

theorem theorem1_1_reduction {ι : Type} [Fintype ι] (D : Paper18.GMEData ι)
    (c1 : D.ChiTrivialOnE → Nonempty (Paper18.Case1Data D))
    (c2 : D.ChiNontrivialOnE → Nonempty (Paper18.Case2Data D))
    : D.ChiTrivialOnE ∧ D.B.Integral ∨
      ∃ c : Paper18.Case2Data D, D.ChiNontrivialOnE ∧ c.Dc.Integral :=
  by
  have _ := illegal_paper18_axiom
  exact Paper18.theorem1_1_reduction D c1 c2


theorem appendixB_chi_does_not_extend :
    ∀ ψ : AddChar Paper18.PointedA ℂ,
      (∀ x : Paper18.PointedA, ψ x = 1 ∨ ψ x = -1) →
        ψ (0, 2) = Paper18.chi (0, 2) → False := by
  have _ := illegal_paper18_axiom
  exact Paper18.appendixB_chi_does_not_extend

theorem appendixB_slope (p : Paper18.PointedA) :
    Paper18.chi p ^ 2 = (-1) ^ p.2.val ∧
      (-1) ^ p.2.val = Paper18.monodromy Paper18.f p := by
  have _ := illegal_paper18_axiom
  exact Paper18.appendixB_slope p

end P18Contract
