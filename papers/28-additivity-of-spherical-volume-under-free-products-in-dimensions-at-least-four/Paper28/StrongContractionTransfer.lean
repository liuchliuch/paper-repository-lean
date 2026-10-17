import Paper28.StrongContractions

/-! Native transfer of the exact locally strong contraction property under
a bi-Lipschitz homeomorphism, including its diameter-dependent time bound. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set Metric
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem locally_strong_contractions_biLipschitz
    (f : X ≃ₜ Y) (L M : NNReal) (hL : 0 < (L : ℝ)) (hM : 0 < (M : ℝ))
    (hf : LipschitzWith L f) (hg : LipschitzWith M f.symm)
    (hX : AdmitsLocallyStrongLipschitzContractions X) : AdmitsLocallyStrongLipschitzContractions Y := by
  intro y
  obtain ⟨r,γ,hr,hγ,hContract⟩ := hX (f.symm y)
  let rY := r/(2*(M : ℝ))
  let γY := (L : ℝ)*γ*(M : ℝ)
  have hrY : 0 < rY := by dsimp [rY]; positivity
  have hγY : 0 < γY := by dsimp [γY]; positivity
  refine ⟨rY,γY,hrY,hγY,?_⟩
  intro S hS
  let E := f.symm '' S
  have hE : E ⊆ ball (f.symm y) r := by
    rintro x ⟨z,hz,rfl⟩
    have hd := hg.dist_le_mul z y
    have hz' : dist z y < rY := hS hz
    have hh : (M : ℝ)*dist z y < (M : ℝ)*rY := mul_lt_mul_of_pos_left hz' hM
    have heq : (M : ℝ)*rY = r/2 := by dsimp [rY]; field_simp
    rw [heq] at hh
    exact hd.trans_lt (hh.trans (by linarith))
  obtain ⟨a,φ,h0,h1,hDist⟩ := hContract E hE
  let e : S → E := fun z => ⟨f.symm z.val,mem_image_of_mem _ z.property⟩
  let ψ : StrongContractionInterval×S → Y := fun p => f (φ (p.1,e p.2))
  refine ⟨f a,ψ,?_,?_,?_⟩
  · intro z
    exact congrArg f (h0 (e z))
  · intro z
    exact (congrArg f (h1 (e z))).trans (f.apply_symm_apply z.val)
  · intro p q
    have hSB : Bornology.IsBounded S := isBounded_ball.subset hS
    have hDiam : diam E ≤ (M : ℝ)*diam S := hg.diam_image_le S hSB
    have hPre : dist (e p.2) (e q.2) ≤ (M : ℝ)*dist p.2 q.2 := hg.dist_le_mul _ _
    have hd := (hf.dist_le_mul (φ (p.1,e p.2)) (φ (q.1,e q.2))).trans
      (mul_le_mul_of_nonneg_left (hDist (p.1,e p.2) (q.1,e q.2)) L.coe_nonneg)
    change dist (ψ p) (ψ q) ≤ _
    calc
      _ ≤ (L : ℝ)*(γ*diam E*dist p.1 q.1+γ*dist (e p.2) (e q.2)) := hd
      _ ≤ (L : ℝ)*(γ*((M : ℝ)*diam S)*dist p.1 q.1+γ*((M : ℝ)*dist p.2 q.2)) := by
        gcongr
      _ = γY*diam S*dist p.1 q.1+γY*dist p.2 q.2 := by dsimp [γY]; ring

end Paper28
