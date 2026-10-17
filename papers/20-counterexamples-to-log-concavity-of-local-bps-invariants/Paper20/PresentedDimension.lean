import Paper20.PresentedNormalSpan

namespace Paper20.PresentedHecke
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Finite generation is proved from the actual factorial normal words
for the honest Hecke presentation over every commutative coefficient ring. -/
instance presentedFinite (R : Type*) [CommRing R] (n : ℕ) (z : R) :
    Module.Finite R (Presented R n z) := by
  classical
  constructor
  refine ⟨Finset.univ.image (normalWord R z n),?_⟩
  simpa only [Finset.coe_image,Finset.coe_univ,Set.image_univ] using normalSpan_eq_top R z n

/-- The rank of the honest Hecke presentation over a field is at most n!,
with the bound witnessed by the explicit actual normal-word family. -/
theorem presented_finrank_le (F : Type*) [Field F] (n : ℕ) (z : F) :
    Module.finrank F (Presented F n z)≤n.factorial := by
  have h := finrank_le_of_span_eq_top (normalSpan_eq_top F z n)
  exact h.trans_eq (code_card n)

end
end Paper20.PresentedHecke
