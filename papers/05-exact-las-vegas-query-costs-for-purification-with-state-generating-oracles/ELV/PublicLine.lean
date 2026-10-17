import ELV.LinePurifierFull
import ELV.HilbertSeparable

/-! The fixed public/private orthogonal decomposition of the line walk,
with actual scalar public space and private catalysts in its complement. -/
noncomputable section
namespace ELV.Line
open ELV.Stabilize ELV.Query
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def singletonIsometry (s : E) (hs : ‖s‖ = 1) : ℂ →ₗᵢ[ℂ] knownLine s where
  toLinearMap :=
    { toFun := fun a => ⟨a • s,Submodule.smul_mem _ a (Submodule.mem_span_singleton_self s)⟩
      map_add' := by intro a b; apply Subtype.ext; exact add_smul a b s
      map_smul' := by intro a b; apply Subtype.ext; exact mul_smul a b s }
  norm_map' a := by
    change ‖a • s‖ = ‖a‖
    simp [norm_smul,hs]

def singletonUnitary (s : E) (hs : ‖s‖ = 1) : ℂ ≃ₗᵢ[ℂ] knownLine s :=
  LinearIsometryEquiv.ofSurjective (singletonIsometry s hs) (by
    intro x
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp x.property
    refine ⟨a,?_⟩
    apply Subtype.ext
    exact ha)

@[simp] lemma singletonUnitary_coe (s : E) (hs : ‖s‖ = 1) (a : ℂ) :
    (singletonUnitary s hs a : E) = a • s := rfl

abbrev Private (s : E) := (knownLine (origin s))ᗮ

lemma origin_norm (s : E) (hs : ‖s‖ = 1) : ‖origin s‖ = 1 := by simpa [origin] using hs

/-- A fixed unitary identification of the physical line with public plus private. -/
def publicMerge (s : E) (hs : ‖s‖ = 1) : HilbertPair ℂ (Private s) ≃ₗᵢ[ℂ] LineSpace E :=
  (pairCongr (singletonUnitary (origin s) (origin_norm s hs)) (LinearIsometryEquiv.refl ℂ _)).trans
    (orthogonalSplit (knownLine (origin s))).symm

@[simp] lemma publicMerge_apply (s : E) (hs : ‖s‖ = 1) (a : ℂ) (w : Private s) :
    publicMerge s hs (WithLp.toLp 2 (a,w)) = a • origin s + (w : LineSpace E) := rfl

/-- The fixed circuit on the exact public/private direct sum required by (2.4). -/
def publicCircuit (s : E) (hs : ‖s‖ = 1) :
    Circuit (HilbertPair ℂ (Private s)) (Channel E) (Channel E) :=
  Query.transport (publicMerge s hs).symm (phaseCircuit (knownLine s))

/-- Returned line catalysts become actual private vectors with identical norms
and identical executed query costs, on a decomposition fixed before the oracle. -/
theorem public_realization (s : E) (hs : ‖s‖ = 1) (R : E ≃ₗᵢ[ℂ] E)
    (ζ : ℂ) (v : LineSpace E) (hv : inner ℂ (origin s) v = 0)
    (hrun : Query.run (lpCongr R) (phaseCircuit (knownLine s)) (origin s+v) = ζ • origin s+v) :
    ∃ w : Private s,
      Query.run (lpCongr R) (publicCircuit s hs) (WithLp.toLp 2 ((1 : ℂ),w)) =
        WithLp.toLp 2 (ζ,w) ∧
      Query.cost (lpCongr R) (publicCircuit s hs) (WithLp.toLp 2 ((1 : ℂ),w)) =
        Query.cost (lpCongr R) (phaseCircuit (knownLine s)) (origin s+v) ∧
      ‖w‖ ^ 2 = ‖v‖ ^ 2 := by
  let w : Private s := ⟨v,Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hv⟩
  have hm : publicMerge s hs (WithLp.toLp 2 ((1 : ℂ),w)) = origin s+v := by
    rw [publicMerge_apply,one_smul]
  have ho : publicMerge s hs (WithLp.toLp 2 (ζ,w)) = ζ • origin s+v := publicMerge_apply _ _ _ _
  refine ⟨w,?_,?_,rfl⟩
  · have hh := run_transport (publicMerge s hs).symm (phaseCircuit (knownLine s))
      (lpCongr R) (origin s+v)
    rw [← hm,LinearIsometryEquiv.symm_apply_apply] at hh
    rw [hm,hrun,← ho,LinearIsometryEquiv.symm_apply_apply] at hh
    exact hh
  · have hh := cost_transport (publicMerge s hs).symm (phaseCircuit (knownLine s))
      (lpCongr R) (origin s+v)
    rw [← hm,LinearIsometryEquiv.symm_apply_apply] at hh
    simpa only [hm] using hh

instance private_separable [TopologicalSpace.SeparableSpace E] (s : E) :
    TopologicalSpace.SeparableSpace (Private s) := by
  letI : TopologicalSpace.SeparableSpace (LineSpace E) := Query.lp_separable
  exact (Private s).subtypeₗᵢ.isometry.isEmbedding.separableSpace

/-- Lemma 3.1 in the explicit public/private direct-sum query model. -/
theorem line_purifier_public (s : E) (hs : ‖s‖ = 1) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) (hne : p ≠ 1/2) (t : E) (ht : ‖t‖ = 1) (hst : inner ℂ s t = 0)
    (R : E ≃ₗᵢ[ℂ] E)
    (hRs : R s = (matrixMean p : ℂ) • s + (matrixOff p : ℂ) • t)
    (hRt : R t = (matrixOff p : ℂ) • s - (matrixMean p : ℂ) • t) :
    ∃ w : Private s,
      Query.run (lpCongr R) (publicCircuit s hs) (WithLp.toLp 2 ((1 : ℂ),w)) =
        WithLp.toLp 2 (phaseSign p,w) ∧
      Query.cost (lpCongr R) (publicCircuit s hs) (WithLp.toLp 2 ((1 : ℂ),w)) = 1/|1-2*p| ∧
      ‖w‖ ^ 2 = min p (1-p)/|1-2*p| := by
  obtain ⟨v,hv,hrun,hcost,hnorm⟩ := line_purifier s hs p hp0 hp1 hne t ht hst R hRs hRt
  obtain ⟨w,hw,hc,hn⟩ := public_realization s hs R (phaseSign p) v hv hrun
  exact ⟨w,hw,hc.trans hcost,hn.trans hnorm⟩

/-- Endpoint public transduction with actual zero private catalyst and cost one. -/
theorem line_purifier_public_endpoint (s : E) (hs : ‖s‖ = 1)
    (R : E ≃ₗᵢ[ℂ] E) (ζ : ℂ) (hζ : ζ^2 = 1) (hRs : R s = ζ • s) :
    Query.run (lpCongr R) (publicCircuit s hs) (WithLp.toLp 2 ((1 : ℂ),(0 : Private s))) =
      WithLp.toLp 2 (ζ,(0 : Private s)) ∧
    Query.cost (lpCongr R) (publicCircuit s hs) (WithLp.toLp 2 ((1 : ℂ),(0 : Private s))) = 1 := by
  have he := line_purifier_endpoint s hs R ζ hζ hRs
  have hm : publicMerge s hs (WithLp.toLp 2 ((1 : ℂ),(0 : Private s))) = origin s := by
    simp [publicMerge_apply]
  have ho : publicMerge s hs (WithLp.toLp 2 (ζ,(0 : Private s))) = ζ • origin s := by
    simp [publicMerge_apply]
  constructor
  · have hh := run_transport (publicMerge s hs).symm (phaseCircuit (knownLine s)) (lpCongr R) (origin s)
    rw [← hm,LinearIsometryEquiv.symm_apply_apply,hm,he.1,← ho,
      LinearIsometryEquiv.symm_apply_apply] at hh
    exact hh
  · have hh := cost_transport (publicMerge s hs).symm (phaseCircuit (knownLine s)) (lpCongr R) (origin s)
    rw [← hm,LinearIsometryEquiv.symm_apply_apply,hm,he.2] at hh
    exact hh

end ELV.Line
