import Paper28.CoordinateSplitting
import Paper28.ShadowDifferentialEquiv

/-! The two complementary edge-coordinate partitions in `(x,z,y)` form.
The original tree partitions are identified with these by the native cut
coordinate equivalences. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open WithLp
open scoped InnerProductSpace
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def splitLeft : α ⊕ (Unit ⊕ β) → α ⊕ Unit :=
  Sum.elim Sum.inl (fun _ => .inr ())

def splitRight : α ⊕ (Unit ⊕ β) → β ⊕ Unit :=
  Sum.elim (fun _ => .inr ()) (Sum.elim (fun _ => .inr ()) Sum.inl)

theorem splitLeft_sum_strict (r : α ⊕ (Unit ⊕ β) → ℝ) (a : α) :
    (∑ i ∈ Finset.univ.filter (fun i => splitLeft i = .inl a), r i) = r (.inl a) := by
  classical
  simp [Finset.sum_filter, Fintype.sum_sum_type, splitLeft]

theorem splitLeft_sum_terminal (r : α ⊕ (Unit ⊕ β) → ℝ) :
    (∑ i ∈ Finset.univ.filter (fun i => splitLeft i = .inr ()), r i) =
      r (.inr (.inl ())) + ∑ b, r (.inr (.inr b)) := by
  classical
  simp [Finset.sum_filter, Fintype.sum_sum_type, splitLeft]

theorem splitLeft_shadow_strict (u : EuclideanSpace ℝ (α ⊕ (Unit ⊕ β))) (a : α) :
    finiteShadow splitLeft u (.inl a) = |u (.inl a)| := by
  change Real.sqrt _ = _
  rw [splitLeft_sum_strict, Real.sqrt_sq_eq_abs]

theorem splitLeft_shadow_terminal (u : EuclideanSpace ℝ (α ⊕ (Unit ⊕ β))) :
    finiteShadow splitLeft u (.inr ()) = ‖(coordinateTriple (Equiv.refl _) u).snd‖ := by
  change Real.sqrt _ = _
  rw [splitLeft_sum_terminal]
  rw [← Real.sqrt_sq (norm_nonneg ((coordinateTriple (Equiv.refl _) u).snd))]
  congr 1
  change u (.inr (.inl ())) ^ 2 + (∑ b, u (.inr (.inr b)) ^ 2) =
    ‖toLp 2 (u (.inr (.inl ())), toLp 2 (fun b => u (.inr (.inr b))))‖ ^ 2
  simp only [prod_norm_sq_eq_of_L2, toLp_fst, toLp_snd, EuclideanSpace.norm_sq_eq,
    Real.norm_eq_abs, sq_abs]
  rfl

theorem splitLeft_differential_strict
    (u h : EuclideanSpace ℝ (α ⊕ (Unit ⊕ β))) (a : α) :
    shadowDifferential splitLeft u h (.inl a) = u (.inl a) * h (.inl a) / |u (.inl a)| := by
  rw [shadowDifferential_apply, splitLeft_shadow_strict, splitLeft_sum_strict]

/-- The terminal component of the canonical cut differential is exactly the
terminal component of the actual norm-folding Frechet differential. -/
theorem splitLeft_differential_terminal
    (u h : EuclideanSpace ℝ (α ⊕ (Unit ⊕ β))) :
    shadowDifferential splitLeft u h (.inr ()) =
      (normFoldDerivative (coordinateTriple (Equiv.refl _) u)
        (coordinateTriple (Equiv.refl _) h)).snd := by
  rw [shadowDifferential_apply, splitLeft_sum_terminal, splitLeft_shadow_terminal,
    normFoldDerivative_apply]
  change (_ + _) / _ = _ / _
  congr 1
  rw [prod_inner_apply]
  simp only [coordinateTriple_snd_fst, coordinateTriple_snd_snd, ofLp_fst, ofLp_snd,
    RCLike.inner_apply, conj_trivial, PiLp.inner_apply, Equiv.refl_apply]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro b _
    ring

/-- The actual cut differential and the norm-folding differential have the
same Gram form on each compatible coordinate stratum. -/
theorem splitLeft_differential_inner
    (u h k : EuclideanSpace ℝ (α ⊕ (Unit ⊕ β)))
    (hh : ∀ a, u (.inl a) = 0 → h (.inl a) = 0)
    (hk : ∀ a, u (.inl a) = 0 → k (.inl a) = 0) :
    ⟪shadowDifferential splitLeft u h, shadowDifferential splitLeft u k⟫_ℝ =
      ⟪normFoldDerivative (coordinateTriple (Equiv.refl _) u) (coordinateTriple (Equiv.refl _) h),
        normFoldDerivative (coordinateTriple (Equiv.refl _) u) (coordinateTriple (Equiv.refl _) k)⟫_ℝ := by
  rw [prod_inner_apply]
  change ⟪shadowDifferential splitLeft u h, shadowDifferential splitLeft u k⟫_ℝ =
    ⟪(coordinateTriple (Equiv.refl _) h).fst, (coordinateTriple (Equiv.refl _) k).fst⟫_ℝ +
      ⟪(normFoldDerivative (coordinateTriple (Equiv.refl _) u) (coordinateTriple (Equiv.refl _) h)).snd,
        (normFoldDerivative (coordinateTriple (Equiv.refl _) u) (coordinateTriple (Equiv.refl _) k)).snd⟫_ℝ
  rw [← splitLeft_differential_terminal u h, ← splitLeft_differential_terminal u k]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fintype.sum_sum_type,
    Fintype.sum_unique, coordinateTriple_fst, Equiv.refl_apply]
  congr 1
  simp_rw [splitLeft_differential_strict]
  exact Finset.sum_congr rfl (fun a _ => signed_coordinate_inner
    (u (.inl a)) (k (.inl a)) (h (.inl a)) (hk a) (hh a))

end Paper28
