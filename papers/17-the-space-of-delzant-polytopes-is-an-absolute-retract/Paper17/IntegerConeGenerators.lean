import Paper17.RationalConeSection

/-! Clearing positive denominators preserves actual positive spans. -/
noncomputable section
open scoped BigOperators
namespace Paper17

/-- A rational vector has an actual positive integer multiple with integer
coordinates. Zero vectors and dimension zero are included. -/
theorem IsRatPoint.exists_pos_integer_multiple {n : ℕ} {x : V n} (hx : IsRatPoint x) :
    ∃ D : ℕ, 0 < D ∧ ∃ v : Fin n → ℤ, (D : ℝ) • x = realRays (fun _ : Unit => v) () := by
  classical
  choose q hq using hx
  let D : ℕ := ∏ j, (q j).den
  have hD : 0 < D := Finset.prod_pos (fun j _ => (q j).den_pos)
  have hdiv : ∀ j, (q j).den ∣ D := fun j => Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  let v : Fin n → ℤ := fun j => (D / (q j).den : ℕ) * (q j).num
  refine ⟨D, hD, v, ?_⟩
  ext j
  change (D : ℝ) * x j = (v j : ℝ)
  rw [hq j, Rat.cast_def]
  have heq : (D : ℝ) = (D / (q j).den : ℕ) * ((q j).den : ℝ) := by
    exact_mod_cast (Nat.div_mul_cancel (hdiv j)).symm
  rw [heq]
  dsimp only [v]
  simp only [Int.cast_mul, Int.cast_natCast]
  field_simp
  <;> ring

/-- A finite rational positive span is an actual finite integer positive span;
each generator is independently rescaled by a positive denominator. -/
theorem finite_rational_span_integer_generators {n : ℕ} (s : Finset (V n))
    (hs : ∀ x ∈ s, IsRatPoint x) :
    ∃ m : ℕ, ∃ rays : Fin m → Fin n → ℤ,
      raySpan (fun x : s => x.val) Finset.univ =
        {x | ∃ c : Fin m → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • realRays rays i} := by
  classical
  have hex : ∀ x : s, ∃ D : ℕ, 0 < D ∧ ∃ v : Fin n → ℤ,
      (D : ℝ) • x.val = realRays (fun _ : Unit => v) () :=
    fun x => (hs x.val x.property).exists_pos_integer_multiple
  choose D hD v hv using hex
  let e : Fin s.card ≃ s := (Finset.equivFin s).symm
  let rays : Fin s.card → Fin n → ℤ := fun i => v (e i)
  have hscale : ∀ i, (D (e i) : ℝ) • (e i).val = realRays rays i := fun i => hv (e i)
  have hpos : ∀ i, (0 : ℝ) < D (e i) := fun i => Nat.cast_pos.mpr (hD (e i))
  refine ⟨s.card, rays, ?_⟩
  let eu : s ≃ ↑(Finset.univ : Finset s) :=
    { toFun := fun x => ⟨x, Finset.mem_univ _⟩
      invFun := fun x => x.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  ext x
  rw [raySpan_iff_enumerated (fun x : s => x.val) Finset.univ
    (e.trans eu)]
  change (∃ c : Fin s.card → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • (e i).val) ↔ _
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun i => c i / D (e i), fun i => div_nonneg (hc i) (hpos i).le, ?_⟩
    apply Finset.sum_congr rfl
    intro i _
    rw [← hscale, smul_smul, div_mul_cancel₀ _ (hpos i).ne']
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun i => c i * D (e i), fun i => mul_nonneg (hc i) (hpos i).le, ?_⟩
    apply Finset.sum_congr rfl
    intro i _
    rw [← hscale, smul_smul]

/-- Finite homogeneous rational inequalities with trivial common kernel
therefore have actual integer generators. -/
theorem rationalCone_integer_generators {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (a : ι → Fin n → ℚ)
    (hk : ∀ x : V n, (∀ i, dot (ratVector (a i)) x = 0) → x = 0) :
    ∃ m : ℕ, ∃ rays : Fin m → Fin n → ℤ,
      rationalInequalityCone a = {x | ∃ c : Fin m → ℝ,
        (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • realRays rays i} := by
  obtain ⟨s, hs, heq⟩ := rationalCone_finite_rational_generators a hk
  obtain ⟨m, rays, hr⟩ := finite_rational_span_integer_generators s hs
  exact ⟨m, rays, heq.trans hr⟩

end Paper17
