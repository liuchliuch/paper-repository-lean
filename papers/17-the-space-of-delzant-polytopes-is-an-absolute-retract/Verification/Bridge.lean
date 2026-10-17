import Verification.Model
import Paper17.ChainCombination
import Paper17.CloseRefinement
import Paper17.AbsoluteRetract

/-! Equivalence of canonical carrier statements and finite geometric presentations. -/
noncomputable section
open scoped Pointwise BigOperators
namespace P17Contract

/-- Choose a finite geometric presentation of an actual Delzant carrier. -/
def toProduction {n : ℕ} (P : DelzantSpace n) : Paper17.DelzantPolytope n :=
  ⟨Classical.choose P.property.some.presentation,
    (Classical.choose_spec P.property.some.presentation).1⟩

@[simp] theorem toProduction_carrier {n : ℕ} (P : DelzantSpace n) :
    (toProduction P).carrier = P.carrier :=
  (Classical.choose_spec P.property.some.presentation).2

/-- Forget redundant vertices and retain the actual canonical convex-body carrier. -/
def ofProduction {n : ℕ} (P : Paper17.DelzantPolytope n) : DelzantSpace n :=
  ⟨{ carrier := P.carrier
     convex' := P.val.convex
     isCompact' := P.val.isCompact
     interior_nonempty' := P.property.1 }, ⟨⟨P.val, P.property, rfl⟩⟩⟩

@[simp] theorem ofProduction_carrier {n : ℕ} (P : Paper17.DelzantPolytope n) :
    (ofProduction P).carrier = P.carrier := rfl

@[simp] theorem production_normalCone {n : ℕ} (P : Paper17.Polytope n) (v : V n) :
    (Paper17.normalConeAt P v : Set (V n)) = normalCone P.carrier v := rfl

/-- Canonical cone refinement implies refinement of the finite normal-fan presentation. -/
theorem toProduction_le {n : ℕ} {P Q : DelzantSpace n} (h : DelzantPolytope.le P Q) :
    Paper17.DelzantPolytope.le (toProduction P) (toProduction Q) := by
  classical
  intro K hK
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hK
  have hvQ : v ∈ Q.carrier := by
    rw [← toProduction_carrier Q]
    exact subset_convexHull ℝ _ hv
  obtain ⟨w, hw, hsub⟩ := h v hvQ
  have hwP : w ∈ (toProduction P).val.carrier := by
    change w ∈ (toProduction P).carrier
    rw [toProduction_carrier P]
    exact hw
  obtain ⟨p, hp, hpcone⟩ := Paper17.exists_vertex_normalCone_superset (toProduction P).val hwP
  refine ⟨Paper17.normalConeAt (toProduction P).val p,
    Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
  rw [production_normalCone, show (toProduction Q).val.carrier = Q.carrier from toProduction_carrier Q]
  rw [production_normalCone,
    show (toProduction P).val.carrier = P.carrier from toProduction_carrier P] at hpcone
  exact hsub.trans hpcone

/-- Finite normal-fan refinement implies refinement of all canonical normal cones. -/
theorem ofProduction_le {n : ℕ} {P Q : Paper17.DelzantPolytope n}
    (h : Paper17.DelzantPolytope.le P Q) :
    DelzantPolytope.le (ofProduction P) (ofProduction Q) := by
  classical
  intro v hv
  obtain ⟨q, hq, hqcone⟩ := Paper17.exists_vertex_normalCone_superset Q.val hv
  obtain ⟨K, hK, hsub⟩ := h (Paper17.normalConeAt Q.val q)
    (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hK
  refine ⟨p, subset_convexHull ℝ _ hp, ?_⟩
  exact hqcone.trans hsub

/-- Refinement in finite presentations, for arbitrary canonical carriers. -/
theorem canonical_le_of_refines {n : ℕ} (P Q : DelzantSpace n)
    (h : Paper17.DelzantPolytope.le (toProduction P) (toProduction Q)) :
    DelzantPolytope.le P Q := by
  have hh := ofProduction_le h
  change ∀ v ∈ (toProduction Q).carrier, ∃ w ∈ (toProduction P).carrier,
    normalCone (toProduction Q).carrier v ⊆ normalCone (toProduction P).carrier w at hh
  simpa only [toProduction_carrier] using hh

@[simp] theorem ofProduction_toProduction {n : ℕ} (P : DelzantSpace n) :
    ofProduction (toProduction P) = P := by
  apply Subtype.ext
  exact PosBody.ext (toProduction_carrier P)

/-- Canonical carriers embedded isometrically in the actual support-function space. -/
def toSupport {n : ℕ} (P : DelzantSpace n) : Paper17.SupportSpace n :=
  Paper17.delzantSupport (toProduction P)

theorem isometry_toSupport {n : ℕ} : Isometry (@toSupport n) := by
  apply isometry_iff_dist_eq.mpr
  intro P Q
  rw [toSupport, toSupport, Paper17.dist_delzantSupport, toProduction_carrier, toProduction_carrier]
  rfl

@[simp] theorem toSupport_ofProduction {n : ℕ} (P : Paper17.DelzantPolytope n) :
    toSupport (ofProduction P) = Paper17.delzantSupport P := by
  ext u
  change Paper17.supportFunction (toProduction (ofProduction P)).carrier u.val =
    Paper17.supportFunction P.carrier u.val
  rw [toProduction_carrier, ofProduction_carrier]

/-- Transfer the production extensor assertion to the canonical carrier space.
No new extension hypothesis is assumed here. -/
theorem carrier_absoluteExtensor (n : ℕ) : IsAbsoluteExtensor (DelzantSpace n) := by
  intro X _ A hA f hf
  let e : DelzantSpace n ≃ₜ Set.range (@toSupport n) := isometry_toSupport.isEmbedding.toHomeomorph
  obtain ⟨F, hFc, hFY, hFeq⟩ := Paper17.theorem_1_2 n X A hA
    (toSupport ∘ f) (isometry_toSupport.continuous.comp hf)
    (fun a => ⟨toProduction (f a), rfl⟩)
  have hFrange : ∀ x, F x ∈ Set.range (@toSupport n) := by
    intro x
    obtain ⟨P, hP⟩ := hFY x
    exact ⟨ofProduction P, (toSupport_ofProduction P).trans hP⟩
  refine ⟨fun x => e.symm ⟨F x, hFrange x⟩,
    e.symm.continuous.comp (hFc.subtype_mk _), ?_⟩
  intro a
  apply e.injective
  simp only [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  change F a = (e (f a)).val
  rw [hFeq a]
  exact (isometry_toSupport.isEmbedding.toHomeomorph_apply_coe (f a)).symm

end P17Contract
