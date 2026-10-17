import Paper28.BassSerreHullCoordinates
import Paper28.BassSerreRawTransfer
import Paper28.FiniteCoordinateAreaInput
import Paper28.TreeCurrentJacobian

/-! The concrete joint area estimate on the actual finite Bass--Serre
hull. Exact native branch coordinates identify every actual shadow with
the finite-tree map in Lemma 2.3. Only the generic individual AK area
formula is external; the joint inequality is derived here. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open MeasureTheory Set
open scoped Classical
attribute [local instance] Classical.propDecidable
variable {G : Type} [Group G] [DecidableEq G] [Countable G] {A B : Subgroup G}
  (T : BassSerreObject A B)
  (MA : SphericalQuotientMetricInput A) (MB : SphericalQuotientMetricInput B)
  (J : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere G) inferInstance)
  (IA : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient A) MA.metric)
  (IB : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient B) MB.metric)
  (F : CanonicalGlobalCurrentCalculusInput) (Area : FiniteCoordinateCurrentAreaInput J)

include Area in
theorem bassSerre_hull_joint_area (Fischer : FischerInput) (E : Finset G) (n : ℕ) (hn : 4 ≤ n)
    (C : J.Current n) (hC : J.support C ⊆ regularCoordinateSphere E) :
    (∑ v : BassSerreHullVertex T E, Sum.elim
      (fun a : G ⧸ A => IA.mass ((bassSerreShadowPushA T MA J IA F a).push n C))
      (fun b : G ⧸ B => IB.mass ((bassSerreShadowPushB T MB J IB F b).push n C)) v.val) ≤ J.mass C := by
  let Q := bassSerreFiniteTree T E
  have hQ := bassSerreFiniteTree_isTree T E
  let s := bassSerreHullEdgeCoordinates T E
  have hEs : E ⊆ Finset.univ.image s := by
    intro g hg
    obtain ⟨e,he⟩ := bassSerreHullEdgeCoordinates_cover T E g hg
    exact Finset.mem_image.mpr ⟨e,Finset.mem_univ _,he⟩
  obtain ⟨R⟩ := Area.representation s n C (fun x hx => coordinateSupportSubspace_mono E _ hEs (hC hx))
  letI := R.finiteMass
  have hIntegrable : ∀ v : BassSerreHullVertex T E,
      Integrable (currentJacobian R.calculus (vertexShadowOnEdges Q hQ v) R.current) (R.calculus.massMeasure R.current) :=
    fun v => R.jacobian_integrable (treeBranchEdge Q hQ v)
  have hEach : ∀ v : BassSerreHullVertex T E, Sum.elim
      (fun a : G ⧸ A => IA.mass ((bassSerreShadowPushA T MA J IA F a).push n C))
      (fun b : G ⧸ B => IB.mass ((bassSerreShadowPushB T MB J IB F b).push n C)) v.val ≤
      ∫ x, currentJacobian R.calculus (vertexShadowOnEdges Q hQ v) R.current x ∂R.calculus.massMeasure R.current := by
    rintro ⟨v,hv⟩
    cases v with
    | inl a =>
      have h := R.individual_area MA IA F (bassSerreBranchA T a) (treeBranchEdge Q hQ ⟨.inl a,hv⟩)
        (bassSerreHullIncidentCoordinatesA T E a hv) (bassSerreHullBranchEdgeA T E a hv)
      exact h
    | inr b =>
      have h := R.individual_area MB IB F (bassSerreBranchB T b) (treeBranchEdge Q hQ ⟨.inr b,hv⟩)
        (bassSerreHullIncidentCoordinatesB T E b hv) (bassSerreHullBranchEdgeB T E b hv)
      exact h
  have hJac := lemma_2_3 Q R.calculus Fischer hQ n hn R.current
  calc
    _ ≤ ∑ v : BassSerreHullVertex T E,
        ∫ x, currentJacobian R.calculus (vertexShadowOnEdges Q hQ v) R.current x ∂R.calculus.massMeasure R.current :=
      Finset.sum_le_sum (fun v _ => hEach v)
    _ = ∫ x, ∑ v : BassSerreHullVertex T E,
        currentJacobian R.calculus (vertexShadowOnEdges Q hQ v) R.current x ∂R.calculus.massMeasure R.current :=
      (integral_finset_sum Finset.univ (fun v _ => hIntegrable v)).symm
    _ ≤ ∫ _x, (1 : ℝ) ∂R.calculus.massMeasure R.current :=
      integral_mono_ae (integrable_finset_sum Finset.univ (fun v _ => hIntegrable v)) (integrable_const 1) hJac
    _ = J.mass C := R.mass_integral_one

end Paper28
