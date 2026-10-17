import Paper28.CurrentClassVolume
import Paper28.GroupHomSphereFolding
import Paper28.GlobalCurrentPushforwardInput

/-! Precisely disclosed existing group-homology/Song comparison framework.
Group homology is a standard external object; current homology and the
mass infimum are the native homology of the actual current boundaries.
Naturality refers to the actual norm-folding maps (23). No free product,
transfer, approximation, factor recovery or additivity is an input field.
-/
set_option autoImplicit false
noncomputable section
namespace Paper28
open CategoryTheory

structure IntegralGroupHomologyInput where
  group : ∀ (G : Type) [Group G] [DecidableEq G] [Countable G], ℕ → AddCommGrpCat
  map : ∀ {G K : Type} [Group G] [Group K] [DecidableEq G] [DecidableEq K] [Countable G] [Countable K],
    (G →* K) → ∀ n, group G n →+ group K n
  map_identity : ∀ (G : Type) [Group G] [DecidableEq G] [Countable G] (n : ℕ),
    map (MonoidHom.id G) n = AddMonoidHom.id (group G n)
  map_composition : ∀ {G K N : Type} [Group G] [Group K] [Group N]
    [DecidableEq G] [DecidableEq K] [DecidableEq N] [Countable G] [Countable K] [Countable N]
    (f : G →* K) (g : K →* N) (n : ℕ), map (g.comp f) n = (map g n).comp (map f n)

def globalCurrentCyclesPush {X Y : Type} {metricX : MetricSpace X} {metricY : MetricSpace Y}
    {I : CompactIntegralCurrentAlgebraInput.{0,0} X metricX}
    {J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY} {f : X → Y}
    (P : GlobalCurrentPushforwardInput metricX metricY I J f) (k : ℕ) :
    PositiveCurrentCycles I k →+ PositiveCurrentCycles J k where
  toFun C := ⟨P.push (k+1) C.val,by
    change J.boundary k (P.push (k+1) C.val) = 0
    rw [P.boundary_comm,C.property,map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' C D := Subtype.ext (map_add _ _ _)

def groupHomCurrentPush (F : CanonicalGlobalCurrentCalculusInput)
    {G K : Type} [Group G] [Group K] [DecidableEq G] [DecidableEq K] [Countable G] [Countable K]
    (MG : SphericalQuotientMetricInput G) (MK : SphericalQuotientMetricInput K)
    (I : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient G) MG.metric)
    (J : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient K) MK.metric) (θ : G →* K) :
    GlobalCurrentPushforwardInput MG.metric MK.metric I J (groupHomQuotientFold θ) := by
  letI := MG.metric
  letI := MK.metric
  exact F.map I J _ ⟨1,groupHomQuotientFold_lipschitz MG MK θ⟩

structure SongCurrentComparisonInput (H : IntegralGroupHomologyInput)
    {G : Type} [Group G] [DecidableEq G] [Countable G] (M : SphericalQuotientMetricInput G)
    (I : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient G) M.metric) where
  toCurrent : ∀ k, H.group G (k+1) →+ PositiveCurrentHomology I k
  realizable : ∀ k h, ∃ C : PositiveCurrentCycles I k, positiveCurrentClass I k C = toCurrent k h

structure SongSphericalHomologyInput (H : IntegralGroupHomologyInput) (F : CanonicalGlobalCurrentCalculusInput) where
  comparison : ∀ {G : Type} [Group G] [DecidableEq G] [Countable G] (M : SphericalQuotientMetricInput G)
    (I : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient G) M.metric), SongCurrentComparisonInput H M I
  naturality : ∀ {G K : Type} [Group G] [Group K] [DecidableEq G] [DecidableEq K] [Countable G] [Countable K]
    (MG : SphericalQuotientMetricInput G) (MK : SphericalQuotientMetricInput K)
    (I : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient G) MG.metric)
    (J : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient K) MK.metric)
    (θ : G →* K) (k : ℕ) (h : H.group G (k+1)) (C : PositiveCurrentCycles I k),
    positiveCurrentClass I k C = (comparison MG I).toCurrent k h →
      positiveCurrentClass J k (globalCurrentCyclesPush (groupHomCurrentPush F MG MK I J θ) k C) =
        (comparison MK J).toCurrent k (H.map θ (k+1) h)

def groupSphericalVolume (H : IntegralGroupHomologyInput) (F : CanonicalGlobalCurrentCalculusInput)
    (Song : SongSphericalHomologyInput H F)
    {G : Type} [Group G] [DecidableEq G] [Countable G] (M : SphericalQuotientMetricInput G)
    (I : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient G) M.metric)
    (k : ℕ) (h : H.group G (k+1)) : ℝ :=
  sphericalClassVolume I k ((Song.comparison M I).toCurrent k h)

end Paper28
