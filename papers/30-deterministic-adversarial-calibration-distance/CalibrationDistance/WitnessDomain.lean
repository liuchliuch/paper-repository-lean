import CalibrationDistance.WitnessConstants

/-! The native source domain for the witness is the closed unit interval.
Extension outside that interval is only a proof device; the theorem below
quantifies over every Lipschitz function on the interval itself. -/

open scoped BigOperators NNReal

namespace CalibrationDistance
noncomputable section

abbrev UnitInterval := Set.Icc (0 : ℝ) 1

def intervalExtension (f : UnitInterval → ℝ) (x : ℝ) : ℝ :=
  if hx : x ∈ Set.Icc (0 : ℝ) 1 then f ⟨x,hx⟩ else 0

@[simp] theorem intervalExtension_on (f : UnitInterval → ℝ) (x : UnitInterval) :
    intervalExtension f x = f x := by simp [intervalExtension, x.property]

def intervalLip (f : UnitInterval → ℝ) : ℝ := leastLip (intervalExtension f)
def intervalSupNorm (f : UnitInterval → ℝ) : ℝ := sSup (Set.range (fun x => |f x|))

theorem intervalSupNorm_eq (f : UnitInterval → ℝ) :
    intervalSupNorm f = unitSupNorm (intervalExtension f) := by
  unfold intervalSupNorm unitSupNorm
  congr 1
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.property, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x,hx⟩, by simp [intervalExtension, hx]⟩

theorem intervalExtension_lipschitzOn {C : ℝ≥0} {f : UnitInterval → ℝ}
    (hf : LipschitzWith C f) :
    LipschitzOnWith C (intervalExtension f) (Set.Icc (0 : ℝ) 1) := by
  intro x hx y hy
  simpa only [intervalExtension, dif_pos hx, dif_pos hy, Subtype.edist_eq] using
    hf (⟨x,hx⟩ : UnitInterval) ⟨y,hy⟩

/-- Lemma 4.1 on the literal source domain, with its genuine best constants. -/
theorem witness_comparison_interval {α : Type*} [Fintype α] {p y : α → ℝ}
    (hp : Valid p) (hy : Valid y) (f : UnitInterval → ℝ) {C : ℝ≥0}
    (hf : LipschitzWith C f) :
    |∑ t, f ⟨p t,hp t⟩ * (y t-p t)| ≤
      (intervalLip f + intervalSupNorm f) * calDist p y := by
  have hh := witness_comparison_least_of_lipschitzOnWith hp hy (intervalExtension f)
    (intervalExtension_lipschitzOn hf)
  rw [← intervalSupNorm_eq f] at hh
  simpa only [intervalExtension, dif_pos (hp _), intervalLip] using hh

end
end CalibrationDistance
