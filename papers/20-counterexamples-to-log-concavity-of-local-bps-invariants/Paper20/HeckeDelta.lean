import Paper20.HeckeMatrices

namespace Paper20.HeckeOperators
open Paper20.HeckeWalkExpansion
noncomputable section
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

/-- A genuine ascent sends a basis delta function to the moved delta
function without a stay term. -/
theorem operator_delta_ascent {S R : Type*} [CommRing R]
    (move : S → S) (desc : S → Prop) (hinv : Function.Involutive move)
    (z : R) (p : S) (hp : ¬desc p) :
    operator move desc z (delta p)=delta (move p) := by
  funext s
  have he : move s=p ↔ s=move p := by
    constructor
    · intro h; have hi := congrArg move h; simpa only [hinv s] using hi
    · intro h; rw [h,hinv p]
  by_cases hsp : s=p
  · subst s
    simp only [operator,delta,hp,↓reduceIte,add_zero]
    by_cases hm : move p=p
    · simp [hm]
    · simp [hm,Ne.symm hm]
  · by_cases hd : desc s <;> simp [operator,delta,he,hsp,hd]

end
end Paper20.HeckeOperators
