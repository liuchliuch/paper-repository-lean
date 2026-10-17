import Paper18.Category.RepresentationZ2Action

/-! # Actual homogeneous coordinates of complex C₂ representations -/
noncomputable section
open Classical CategoryTheory
open scoped BigOperators
namespace Paper18.Category.RepresentationZ2

abbrev EigenIndex (V : FDRep ℂ H) :=
  Fin (Module.finrank ℂ (plusSpace V)) ⊕ Fin (Module.finrank ℂ (minusSpace V))

def eigenCoordinates (V : FDRep ℂ H) : V ≃ₗ[ℂ] (EigenIndex V → ℂ) :=
  (eigenspaceEquiv V).symm.trans
    (((Module.finBasis ℂ (plusSpace V)).equivFun.prodCongr
      (Module.finBasis ℂ (minusSpace V)).equivFun).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ ℂ ℂ).symm)

def eigenSign (V : FDRep ℂ H) : EigenIndex V → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

lemma eigenCoordinates_generator (V : FDRep ℂ H) (v : V) (i : EigenIndex V) :
    eigenCoordinates V (V.ρ generator v) i = eigenSign V i * eigenCoordinates V v i := by
  have h : (eigenspaceEquiv V).symm (V.ρ generator v) =
      (((eigenspaceEquiv V).symm v).1, -((eigenspaceEquiv V).symm v).2) := by
    apply (eigenspaceEquiv V).injective
    simpa only [LinearEquiv.apply_symm_apply] using
      eigenspaceEquiv_generator V ((eigenspaceEquiv V).symm v)
  cases i with
  | inl a => simp [eigenCoordinates, eigenSign, h]
  | inr a => simp [eigenCoordinates, eigenSign, h]

def eigenVector (V : FDRep ℂ H) (i : EigenIndex V) : V :=
  (eigenCoordinates V).symm (Pi.single i 1)

@[simp] lemma eigenCoordinates_eigenVector (V : FDRep ℂ H) (i : EigenIndex V) :
    eigenCoordinates V (eigenVector V i) = Pi.single i 1 :=
  (eigenCoordinates V).apply_symm_apply _

lemma eigenVector_generator (V : FDRep ℂ H) (i : EigenIndex V) :
    V.ρ generator (eigenVector V i) = eigenSign V i • eigenVector V i := by
  apply (eigenCoordinates V).injective
  funext j
  rw [eigenCoordinates_generator, map_smul, eigenCoordinates_eigenVector]
  by_cases hji : j = i
  · subst j; simp
  · simp [hji]

/-- A genuine homogeneous basis resolution, derived from the eigenspaces. -/
lemma eigenVector_resolution (V : FDRep ℂ H) (v : V) :
    ∑ i : EigenIndex V, eigenCoordinates V v i • eigenVector V i = v := by
  apply (eigenCoordinates V).injective
  funext j
  simp only [map_sum, map_smul, eigenCoordinates_eigenVector, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  simp [Pi.single_apply]

end Paper18.Category.RepresentationZ2
