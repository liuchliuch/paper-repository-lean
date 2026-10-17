import Paper28.HilbertPartitionFold
import Paper28.SphericalQuotientMetricInput
import Paper28.ProjectionErrorNeighborhood

/-! Actual group-homomorphism norm foldings in Song §3.4.1 (23), on the
native lp sphere and orbit quotient. Quotient equivariance and metric
contraction are derived from the native Hilbert partition map. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {H K : Type} [Group H] [Group K] [DecidableEq H] [DecidableEq K]

def groupHomSphereFold (θ : H →* K) (u : RegularSphere H) : RegularSphere K :=
  ⟨hilbertPartitionFold θ u.val,(hilbertPartitionFold_norm _ _).trans u.property⟩

theorem groupHomSphereFold_lipschitz (θ : H →* K) : LipschitzWith 1 (groupHomSphereFold θ) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simpa only [Subtype.dist_eq,dist_eq_norm,NNReal.coe_one,one_mul] using hilbertPartitionFold_dist θ u.val v.val

theorem groupHomSphereFold_equivariant (θ : H →* K) (a : H) (u : RegularSphere H) :
    groupHomSphereFold θ (a • u) = θ a • groupHomSphereFold θ u := by
  apply Subtype.ext
  ext b
  change hilbertPartitionFold θ (leftRegular a u.val) b = leftRegular (θ a) (hilbertPartitionFold θ u.val) b
  rw [leftRegular_apply]
  have he := hilbertPartitionFold_reindex θ θ (Equiv.mulLeft a) (Equiv.mulLeft (θ a))
    (fun x => θ.map_mul a x) u.val (leftRegular a u.val) (fun x => by simp [leftRegular_apply]) ((θ a)⁻¹*b)
  change hilbertPartitionFold θ (leftRegular a u.val) (θ a*((θ a)⁻¹*b)) = _ at he
  simpa only [mul_inv_cancel_left] using he

def groupHomQuotientFold (θ : H →* K) : RegularOrbitQuotient H → RegularOrbitQuotient K :=
  Quotient.lift (fun u => regularQuotientMap (groupHomSphereFold θ u)) (by
    intro u v h
    have ho : u ∈ MulAction.orbit H v := h
    obtain ⟨a,rfl⟩ := MulAction.mem_orbit_iff.mp ho
    change regularQuotientMap (groupHomSphereFold θ (a • v)) = regularQuotientMap (groupHomSphereFold θ v)
    rw [groupHomSphereFold_equivariant]
    exact regularQuotientMap_smul _ _)

theorem groupHomQuotientFold_eval (θ : H →* K) (u : RegularSphere H) :
    groupHomQuotientFold θ (regularQuotientMap u) = regularQuotientMap (groupHomSphereFold θ u) := rfl

theorem groupHomQuotientFold_lipschitz [Countable H] [Countable K]
    (MH : SphericalQuotientMetricInput H) (MK : SphericalQuotientMetricInput K) (θ : H →* K) :
    letI := MH.metric; letI := MK.metric
    LipschitzWith 1 (groupHomQuotientFold θ) := by
  letI := MH.metric
  letI := MK.metric
  apply LipschitzWith.of_dist_le_mul
  intro q p
  obtain ⟨u,rfl⟩ := Quotient.mk_surjective q
  obtain ⟨v,rfl⟩ := Quotient.mk_surjective p
  simp only [NNReal.coe_one,one_mul]
  change dist (regularQuotientMap (groupHomSphereFold θ u)) (regularQuotientMap (groupHomSphereFold θ v)) ≤
    dist (regularQuotientMap u) (regularQuotientMap v)
  rw [spherical_quotient_distance MH]
  apply le_csInf (Set.range_nonempty _)
  rintro a ⟨γ,rfl⟩
  have h := spherical_quotient_dist_le_angle MK (groupHomSphereFold θ u) (groupHomSphereFold θ v) (θ γ)
  have he : leftRegular (θ γ) (groupHomSphereFold θ v).val = (groupHomSphereFold θ (γ • v)).val :=
    (congrArg Subtype.val (groupHomSphereFold_equivariant θ γ v)).symm
  rw [he] at h
  exact h.trans (hilbertPartitionFold_angular θ u.val (leftRegular γ v.val))

/-- Standard regrouping of square-summable orthogonal coordinate sums.
This elementary Fubini/orthogonal-direct-sum corollary is kept explicit;
it is independent of any group, tree, current, transfer or volume bound. -/
structure HilbertGroupingInput : Prop where
  composition : ∀ {ι κ ν : Type} (π : ι → κ) (ρ : κ → ν) (u : CoordinateHilbert ι),
    hilbertPartitionFold ρ (hilbertPartitionFold π u) = hilbertPartitionFold (ρ ∘ π) u
  constant : ∀ {ι κ : Type} [DecidableEq κ] (c : κ) (u : CoordinateHilbert ι),
    hilbertPartitionFold (fun _ : ι => c) u = lp.single 2 c ‖u‖

theorem hilbertPartitionFold_left_mul (c : K) (u : CoordinateHilbert K) :
    hilbertPartitionFold (fun a : K => c*a) u = leftRegular c (hilbertPartitionFold id u) := by
  ext a
  rw [leftRegular_apply]
  have he := hilbertPartitionFold_reindex id (fun a : K => c*a) (Equiv.refl K) (Equiv.mulLeft c)
    (fun _ => rfl) u u (fun _ => rfl) (c⁻¹*a)
  change hilbertPartitionFold (fun a : K => c*a) u (c*(c⁻¹*a)) = _ at he
  simpa only [mul_inv_cancel_left] using he

end Paper28
