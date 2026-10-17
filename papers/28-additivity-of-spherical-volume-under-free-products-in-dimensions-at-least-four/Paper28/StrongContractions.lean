import Paper28.RetractionContractions
import Mathlib.Topology.MetricSpace.Isometry

/-! The exact strong-contraction predicate of Riedweg--Schaeppi Definition
1.1, with their time orientation (0 constant, 1 inclusion). Neighborhood
retractions imply it with the required diameter factor proved explicitly. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set Metric

abbrev StrongContractionInterval := Icc (0 : ℝ) 1

def AdmitsStrongLipschitzContraction {X : Type*} [MetricSpace X] (S : Set X) (γ : ℝ) : Prop :=
  ∃ a : X, ∃ φ : StrongContractionInterval×S → X,
    (∀ y : S, φ (⟨0,by norm_num⟩,y) = a) ∧
    (∀ y : S, φ (⟨1,by norm_num⟩,y) = y.val) ∧
    ∀ p q, dist (φ p) (φ q) ≤ γ*diam S*dist p.1 q.1+γ*dist p.2 q.2

def AdmitsLocallyStrongLipschitzContractions (X : Type*) [MetricSpace X] : Prop :=
  ∀ x : X, ∃ r γ : ℝ, 0 < r ∧ 0 < γ ∧ ∀ S : Set X, S ⊆ ball x r →
    AdmitsStrongLipschitzContraction S γ

set_option maxHeartbeats 600000 in
theorem locally_strong_contractions_of_neighborhood_retraction
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : Set H) (r : H → H) (hFix : ∀ x ∈ K, r x = x)
    (hNear : ∀ x ∈ K, ∃ ρ : ℝ, 0 < ρ ∧ ∃ L : NNReal,
      LipschitzOnWith L r (ball x ρ) ∧ MapsTo r (ball x ρ) K) :
    AdmitsLocallyStrongLipschitzContractions K := by
  intro x
  obtain ⟨ρ,hρ,L,hLip,hMaps⟩ := hNear x.val x.property
  let γ := (L : ℝ)+1
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hLγ : (L : ℝ) ≤ γ := by dsimp [γ]; linarith
  refine ⟨ρ,γ,hρ,hγ,?_⟩
  intro S hS
  by_cases hSE : S.Nonempty
  · obtain ⟨a,ha⟩ := hSE
    let E : Set H := Subtype.val '' S
    have hEball : E ⊆ ball x.val ρ := by
      rintro u ⟨y,hy,rfl⟩
      exact hS hy
    have hEB : Bornology.IsBounded E := isBounded_ball.subset hEball
    have haE : a.val ∈ E := mem_image_of_mem _ ha
    have haB : a.val ∈ ball x.val ρ := hS ha
    have hSeg : ∀ t : StrongContractionInterval, ∀ y : S,
        (1-(1-t.val)) • y.val.val+(1-t.val) • a.val ∈ ball x.val ρ := by
      intro t y
      exact contraction_segment_mem_ball x.val a.val y.val.val ρ (1-t.val) haB (hS y.property)
        (by linarith [t.property.2]) (by linarith [t.property.1])
    let φ : StrongContractionInterval×S → K := fun p =>
      ⟨retractionContraction r a.val (1-p.1.val) p.2.val.val,hMaps (hSeg p.1 p.2)⟩
    refine ⟨a,φ,?_,?_,?_⟩
    · intro y
      apply Subtype.ext
      change r ((1-(1-0)) • y.val.val+(1-0) • a.val) = a.val
      simpa only [sub_zero,sub_self,zero_smul,one_smul,zero_add] using hFix a.val a.property
    · intro y
      apply Subtype.ext
      change r ((1-(1-1)) • y.val.val+(1-1) • a.val) = y.val.val
      simpa only [sub_self,sub_zero,zero_smul,one_smul,add_zero] using hFix y.val.val y.val.property
    · intro p q
      have hSpace := retractionContraction_spatial r (ball x.val ρ) L hLip a.val p.2.val.val q.2.val.val
        (1-p.1.val) (by linarith [p.1.property.2]) (by linarith [p.1.property.1])
        (hSeg p.1 p.2) (hSeg p.1 q.2)
      have hTime := retractionContraction_time_diameter r (ball x.val ρ) E L hLip hEB
        a.val q.2.val.val haE (mem_image_of_mem _ q.2.property)
        (1-p.1.val) (1-q.1.val) (hSeg p.1 q.2) (hSeg q.1 q.2)
      have hDiam : diam E = diam S := isometry_subtype_coe.diam_image S
      have hAbs : |(1-p.1.val)-(1-q.1.val)| = dist p.1 q.1 := by
        change |(1-p.1.val)-(1-q.1.val)| = |p.1.val-q.1.val|
        have he : (1-p.1.val)-(1-q.1.val) = -(p.1.val-q.1.val) := by ring
        rw [he,abs_neg]
      rw [hDiam,hAbs] at hTime
      have hTriangle := dist_triangle (φ p)
        (φ (p.1,q.2)) (φ q)
      change dist (φ p) (φ q) ≤ _
      have hSpace' : dist (φ p) (φ (p.1,q.2)) ≤ (L : ℝ)*dist p.2 q.2 := hSpace
      have hTime' : dist (φ (p.1,q.2)) (φ q) ≤ (L : ℝ)*diam S*dist p.1 q.1 := hTime
      calc
        _ ≤ (L : ℝ)*dist p.2 q.2+(L : ℝ)*diam S*dist p.1 q.1 := hTriangle.trans (add_le_add hSpace' hTime')
        _ ≤ γ*diam S*dist p.1 q.1+γ*dist p.2 q.2 := by
          have h1 := mul_le_mul_of_nonneg_right hLγ (dist_nonneg (x := p.2) (y := q.2))
          have h2 := mul_le_mul_of_nonneg_right hLγ (mul_nonneg (diam_nonneg (s := S)) (dist_nonneg (x := p.1) (y := q.1)))
          nlinarith
  · have hEmpty : S = ∅ := not_nonempty_iff_eq_empty.mp hSE
    refine ⟨x,(fun _ => x),?_,?_,?_⟩
    · intro y
      exact False.elim (by simpa only [hEmpty,mem_empty_iff_false] using y.property)
    · intro y
      exact False.elim (by simpa only [hEmpty,mem_empty_iff_false] using y.property)
    · intro p q
      exact False.elim (by simpa only [hEmpty,mem_empty_iff_false] using p.2.property)

end Paper28
