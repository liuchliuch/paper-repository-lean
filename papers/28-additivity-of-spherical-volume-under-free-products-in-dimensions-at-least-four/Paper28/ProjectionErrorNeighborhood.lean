import Paper28.TranslatedProjections

/-! Extending the active projection error from the compact quotient set to
an open invariant neighborhood. Bad closed pieces have closed quotient
images by the already proved chart properness; no near-isometry is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Metric
variable {G J : Type*} [Group G] [DecidableEq G] [Fintype J]

@[simp] theorem regularQuotientMap_smul (γ : G) (u : RegularSphere G) :
    regularQuotientMap (γ • u) = regularQuotientMap u :=
  Quotient.sound (show MulAction.orbitRel G (RegularSphere G) (γ • u) u from ⟨γ,rfl⟩)

def badProjectionChart (c : RegularSphere G) (F : Finset G) (δ : ℝ) : Set (RegularSphere G) :=
  {u | u ∈ closedBall c (1/8 : ℝ) ∧ 2*δ ≤ ‖l2CoordinateProjection F u.val-u.val‖}

theorem badProjectionChart_isClosed (c : RegularSphere G) (F : Finset G) (δ : ℝ) :
    IsClosed (badProjectionChart c F δ) := by
  have he : Continuous (fun u : RegularSphere G => ‖l2CoordinateProjection F u.val-u.val‖) :=
    ((l2CoordinateProjectionCLM F).continuous.comp continuous_subtype_val |>.sub continuous_subtype_val).norm
  exact isClosed_closedBall.inter (isClosed_le continuous_const he)

/-- A fixed collection of compact-chart projections has uniformly small
active error on an actual open quotient neighborhood of K. -/
theorem exists_projection_error_neighborhood (c : J → RegularSphere G)
    [∀ j, Fintype (regularStabilizer (c j).val)] (b : ∀ j, ContDiffBump (c j).val)
    (hR : ∀ j, (b j).rOut ≤ (1/8 : ℝ)) (F : J → Finset G)
    (K : Set (RegularOrbitQuotient G)) (δ : ℝ) (hδ : 0 < δ)
    (hApprox : ∀ j, ∀ u : RegularSphere G, regularQuotientMap u ∈ K → dist u (c j) ≤ (1/8 : ℝ) →
      ‖l2CoordinateProjection (F j) u.val-u.val‖ < δ) :
    ∃ U : Set (RegularOrbitQuotient G), IsOpen U ∧ K ⊆ U ∧
      ∀ u : RegularSphere G, regularQuotientMap u ∈ U → ∀ i : J×G,
        translatedCutoff (fun j => (c j).val) b i u.val ≠ 0 →
          ‖translatedProjection F i u.val-u.val‖ < 2*δ := by
  let B := fun j => regularQuotientMap '' badProjectionChart (c j) (F j) δ
  have hB : ∀ j, IsClosed (B j) := fun j =>
    regular_quotient_closed_image (c j) (1/8) (by norm_num) _
      (badProjectionChart_isClosed (c j) (F j) δ) (fun _ h => h.1)
  let U := (⋃ j, B j)ᶜ
  refine ⟨U,(isClosed_iUnion_of_finite hB).isOpen_compl,?_,?_⟩
  · intro q hq hbad
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hbad
    obtain ⟨u,hu,huq⟩ := hj
    have he := hApprox j u (huq ▸ hq) hu.1
    linarith [hu.2]
  · intro u hu i hβ
    let v : RegularSphere G := i.2⁻¹ • u
    have hvq : regularQuotientMap v = regularQuotientMap u := regularQuotientMap_smul _ _
    have hclose : dist v (c i.1) < (1/8 : ℝ) := by
      have hc := translatedCutoff_support (fun j => (c j).val) b i u.val hβ
      change dist (leftRegular i.2⁻¹ u.val) (c i.1).val < (1/8 : ℝ)
      rw [leftRegular_inv_dist]
      exact hc.trans_le (hR i.1)
    by_contra hError
    have hE : 2*δ ≤ ‖l2CoordinateProjection (F i.1) v.val-v.val‖ := by
      rw [translatedProjection_error] at hError
      exact not_lt.mp hError
    apply hu
    apply Set.mem_iUnion.mpr
    refine ⟨i.1,v,⟨hclose.le,hE⟩,hvq⟩

end Paper28
