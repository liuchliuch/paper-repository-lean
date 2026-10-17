import Paper27.Geometry.LineCocycles
import Paper27.Geometry.NormalJets
import Paper27.Geometry.CyclicTransitions

/-!
# Retraction normal charts, their jets, and transition compatibility

The charts below are actual open partial homeomorphisms, and the two maps take
values in the actual compact complex curve. The exact overlap formula (3) is
proved with chart inverse identities. The polynomial coefficient calculation
then derives the nth-power relation for the normal cocycle, from raw first
Taylor jets rather than from a supplied bundle isomorphism.

The source space may be the surface itself or an open neighbourhood subtype.
Holomorphicity and existence of the normal charts and Taylor jets are separate
geometric inputs. No action on the whole neighbourhood is assumed: the final
lemma proves that the local rotations commute with coordinate transitions.
-/

noncomputable section

open scoped Manifold
open Polynomial Finset

namespace Paper27.Geometry.RetractionAtlas

section NormalCharts

variable {S : Type*} [TopologicalSpace S]

/-- An actual source chart in which the two maps to the curve have the normal
forms `r=x` and `s=x+y^n`, in the same actual base coordinate. -/
structure NormalFormChart (D : Curve) (r s : S → D) (n : ℕ) (i : D) where
  coordinates : OpenPartialHomeomorph S (ℂ × ℂ)
  r_source : ∀ q ∈ coordinates.source, r q ∈ D.chartDomain i
  s_source : ∀ q ∈ coordinates.source, s q ∈ D.chartDomain i
  r_normal : ∀ q ∈ coordinates.source, (chartAt ℂ i) (r q) = (coordinates q).1
  s_normal : ∀ q ∈ coordinates.source, (chartAt ℂ i) (s q) =
    (coordinates q).1 + (coordinates q).2 ^ n

/-- The actual coordinate change on a point of the first chart's source. -/
theorem chartChange_at_point (D : Curve) (i j p : D) (hp : p ∈ D.chartDomain i) :
    D.chartChange i j ((chartAt ℂ i) p) = (chartAt ℂ j) p := by
  exact congrArg (chartAt ℂ j) ((chartAt ℂ i).left_inv hp)

/-- Formula (3), deduced from the two actual map identities and the chart
inverse equation. Both appearances of `φ` are the same actual base transition. -/
theorem overlap_formula_three (D : Curve) (r s : S → D) (n : ℕ) (i j : D)
    (ci : NormalFormChart D r s n i) (cj : NormalFormChart D r s n j)
    (q : S) (hi : q ∈ ci.coordinates.source) (hj : q ∈ cj.coordinates.source) :
    (cj.coordinates q).1 = D.chartChange i j ((ci.coordinates q).1) ∧
    (cj.coordinates q).2 ^ n =
      D.chartChange i j ((ci.coordinates q).1 + (ci.coordinates q).2 ^ n) -
        D.chartChange i j ((ci.coordinates q).1) := by
  have hr : D.chartChange i j ((ci.coordinates q).1) = (cj.coordinates q).1 := by
    rw [← ci.r_normal q hi, chartChange_at_point D i j (r q) (ci.r_source q hi)]
    exact cj.r_normal q hj
  have hs : D.chartChange i j ((ci.coordinates q).1 + (ci.coordinates q).2 ^ n) =
      (cj.coordinates q).1 + (cj.coordinates q).2 ^ n := by
    rw [← ci.s_normal q hi, chartChange_at_point D i j (s q) (ci.s_source q hi)]
    exact cj.s_normal q hj
  refine ⟨hr.symm, ?_⟩
  rw [hs, hr]
  ring

/-- A rotation in a normal chart preserves the two actual maps, provided both
points remain in the chart. This precedes, and does not assume, action gluing. -/
theorem normal_rotation_preserves_maps (D : Curve) (r s : S → D) (n : ℕ) (i : D)
    (c : NormalFormChart D r s n i) (q q' : S)
    (hq : q ∈ c.coordinates.source) (hq' : q' ∈ c.coordinates.source)
    (ζ : ℂ) (hζ : ζ ^ n = 1)
    (hrotation : c.coordinates q' = ((c.coordinates q).1, ζ * (c.coordinates q).2)) :
    r q' = r q ∧ s q' = s q := by
  have hr : (chartAt ℂ i) (r q') = (chartAt ℂ i) (r q) := by
    rw [c.r_normal q' hq', c.r_normal q hq, hrotation]
  have hs : (chartAt ℂ i) (s q') = (chartAt ℂ i) (s q) := by
    rw [c.s_normal q' hq', c.s_normal q hq, hrotation]
    simp only [mul_pow, hζ, one_mul]
  constructor
  · calc
      r q' = (chartAt ℂ i).symm ((chartAt ℂ i) (r q')) :=
        ((chartAt ℂ i).left_inv (c.r_source q' hq')).symm
      _ = (chartAt ℂ i).symm ((chartAt ℂ i) (r q)) := congrArg _ hr
      _ = r q := (chartAt ℂ i).left_inv (c.r_source q hq)
  · calc
      s q' = (chartAt ℂ i).symm ((chartAt ℂ i) (s q')) :=
        ((chartAt ℂ i).left_inv (c.s_source q' hq')).symm
      _ = (chartAt ℂ i).symm ((chartAt ℂ i) (s q)) := congrArg _ hs
      _ = s q := (chartAt ℂ i).left_inv (c.s_source q hq)

end NormalCharts

section NormalJetBridge

/-- The first Taylor coefficient of `φ(x+t^n)-φ(x)`, written as a polynomial
jet in `t`, is precisely the linear coefficient of the jet in `t^n`. -/
theorem raw_base_change_first_coefficient {n : ℕ} (hn : 0 < n) (F : ℂ[X]) :
    (F.comp (X ^ n) - C (F.coeff 0)).coeff n = F.coeff 1 := by
  have hindex : ∀ m : ℕ, n = n * m ↔ m = 1 := by
    intro m
    constructor
    · intro hm
      have hm' : n * 1 = n * m := by simpa using hm
      exact (Nat.eq_of_mul_eq_mul_left hn hm').symm
    · rintro rfl
      simp
  rw [coeff_sub, comp_eq_sum_left, coeff_sum, Polynomial.sum_def]
  simp only [coeff_C_mul, ← pow_mul, coeff_X_pow, hindex, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Polynomial.mem_support_iff, coeff_C,
    if_neg (Nat.ne_of_gt hn), sub_zero]
  by_cases hc : F.coeff 1 = 0 <;> simp [hc]

/-- A normal-coordinate Taylor jet with the stated first coefficient forces
the normal linear transition to be the nth root of that coefficient. -/
theorem normal_power_from_first_jet {n : ℕ} (hn : 0 < n)
    (Y H : ℂ[X]) (lam p : ℂ)
    (hY : Y = NormalJets.normalChange n lam H) (hcoefficient : (Y ^ n).coeff n = p) :
    lam ^ n = p := by
  rw [hY, NormalJets.normalChange_power_leading hn] at hcoefficient
  exact hcoefficient

/-- The root relation from raw Taylor compatibility with formula (3), rather
than from an assumed equality of normal and tangent transition powers. -/
theorem normal_power_from_raw_taylor_jet {n : ℕ} (hn : 0 < n)
    (Y H F : ℂ[X]) (lam p : ℂ)
    (hY : Y = NormalJets.normalChange n lam H) (hF : F.coeff 1 = p)
    (hcompatibility : (Y ^ n).coeff n =
      (F.comp (X ^ n) - C (F.coeff 0)).coeff n) : lam ^ n = p := by
  apply normal_power_from_first_jet hn Y H lam p hY
  exact hcompatibility.trans ((raw_base_change_first_coefficient hn F).trans hF)

/-- The normal tensor identity and negative degree are derived from the raw
normal/base Taylor jets at every actual chart overlap. The cocycle `N` is the
actual normal-coordinate cocycle; its nth-power identity is proved here. -/
theorem normal_tensor_degree_from_raw_jets (theory : LineBundleDegreeTheory)
    (D : Curve) (N : HolomorphicLineCocycle D) (T : TangentLineCocycle D)
    (n : ℕ) (hn : 2 ≤ n) (hg : D.Hyperbolic)
    (Y H F : D → D → D → ℂ[X])
    (hY : ∀ i j p, p ∈ D.chartDomain i → p ∈ D.chartDomain j →
      Y i j p = NormalJets.normalChange n (N.transition i j p) (H i j p))
    (hF : ∀ i j p, p ∈ D.chartDomain i → p ∈ D.chartDomain j →
      (F i j p).coeff 1 = D.chartJacobian i j p)
    (hcompatibility : ∀ i j p, p ∈ D.chartDomain i → p ∈ D.chartDomain j →
      (Y i j p ^ n).coeff n =
        ((F i j p).comp (X ^ n) - C ((F i j p).coeff 0)).coeff n) :
    (N.tensorPower n).SameTransitions T.bundle ∧
      (n : ℤ) * theory.degree D N = 2 - 2 * (D.genus : ℤ) ∧
      theory.degree D N < 0 := by
  apply normal_tensor_degree theory D N T n hn hg
  intro i j p hi hj
  exact normal_power_from_raw_taylor_jet (by omega) (Y i j p) (H i j p) (F i j p)
    (N.transition i j p) (D.chartJacobian i j p) (hY i j p hi hj)
    (hF i j p hi hj) (hcompatibility i j p hi hj)

end NormalJetBridge

section CyclicCompatibility

variable {U : Type*}

/-- The nth power of the normal transition unit is invariant because its raw
factor depends only on `x` and `y^n`. -/
theorem normal_unit_power_invariant (n : ℕ) (ζ : ℂ) (hζ : ζ ^ n = 1)
    (τ : U → U) (x y h : U → ℂ) (F : ℂ → ℂ → ℂ)
    (hx : ∀ u, x (τ u) = x u) (hy : ∀ u, y (τ u) = ζ * y u)
    (hfactor : ∀ u, h u ^ n = F (x u) (y u ^ n)) : ∀ u, h (τ u) ^ n = h u ^ n := by
  intro u
  rw [hfactor, hfactor, hx, hy, mul_pow, hζ, one_mul]

/-- Local coordinate transitions commute with the cyclic rotations. The input
is only the raw unit factorization, continuity, and a point of the fixed curve;
there is no already-glued action among the assumptions. -/
theorem rotation_overlap_compatibility [TopologicalSpace U] [PreconnectedSpace U]
    (n : ℕ) (hn : 0 < n) (ζ : ℂ) (hζ : ζ ^ n = 1)
    (τ : U → U) (hτ : Continuous τ) (x y x' y' h : U → ℂ)
    (φ : ℂ → ℂ) (F : ℂ → ℂ → ℂ)
    (hh : Continuous h) (hne : ∀ u, h u ≠ 0)
    (hx : ∀ u, x (τ u) = x u) (hy : ∀ u, y (τ u) = ζ * y u)
    (hx' : ∀ u, x' u = φ (x u)) (hy' : ∀ u, y' u = y u * h u)
    (hfactor : ∀ u, h u ^ n = F (x u) (y u ^ n))
    (u₀ : U) (hfixed : τ u₀ = u₀) :
    ∀ u, (x' (τ u), y' (τ u)) = (x' u, ζ * y' u) := by
  have hpow := normal_unit_power_invariant n ζ hζ τ x y h F hx hy hfactor
  have hnormal := CyclicTransitions.normal_transition_commutes n hn τ hτ y h hh hne
    hpow u₀ hfixed ζ hy
  intro u
  apply Prod.ext
  · rw [hx', hx', hx]
  · rw [hy', hy', hnormal]

end CyclicCompatibility

end Paper27.Geometry.RetractionAtlas
