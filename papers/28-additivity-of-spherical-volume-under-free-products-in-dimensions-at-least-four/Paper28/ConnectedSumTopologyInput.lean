import Paper28.PaperFoundations
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-! Standard connected-sum topology, explicitly external to this paper's
own argument. Underlying closed connected manifolds and their fundamental
groups are native topological/charted-space objects. Topological orientations,
the canonical classifying image of the oriented fundamental class, and the
oriented connected-sum construction are standard supplied objects.
Van Kampen and the pinch fundamental-class identity are the only theorem
conclusions used below (Hatcher 1.20, 3.26 and §3.3; connected-sum/excision
corollary). No spherical volume or additivity is an input field.
-/
set_option autoImplicit false
noncomputable section
namespace Paper28

structure ClosedConnectedManifold (n : ℕ) where
  carrier : Type
  topology : TopologicalSpace carrier
  t2 : @T2Space carrier topology
  secondCountable : @SecondCountableTopology carrier topology
  compact : @CompactSpace carrier topology
  connected : @ConnectedSpace carrier topology
  charts : @ChartedSpace (EuclideanSpace ℝ (Fin n)) inferInstance carrier topology
  point : carrier

attribute [instance] ClosedConnectedManifold.topology ClosedConnectedManifold.t2
  ClosedConnectedManifold.secondCountable ClosedConnectedManifold.compact ClosedConnectedManifold.connected
  ClosedConnectedManifold.charts

/-- The standard orientation/fundamental-class/connected-sum object API.
Orientation denotes a topological orientation (coherent integral local
homology generators); fundamentalImage is the canonical image under a
classifying map in the stated actual fundamental-group model. These
standard objects are supplied, not rebuilt or claimed as native witnesses.
-/
structure ManifoldTopologyObjectsInput (H : IntegralGroupHomologyInput) where
  Orientation : ∀ {n : ℕ}, ClosedConnectedManifold n → Type
  fundamentalImage : ∀ {n : ℕ} (M : ClosedConnectedManifold n), Orientation M →
    ∀ {Γ : Type} [Group Γ] [DecidableEq Γ] [Countable Γ],
      (Γ ≃* FundamentalGroup M.carrier M.point) → H.group Γ n
  connectedSum : ∀ {n : ℕ} (M N : ClosedConnectedManifold n), Orientation M → Orientation N →
    Σ W : ClosedConnectedManifold n, Orientation W

variable {H : IntegralGroupHomologyInput} (Objects : ManifoldTopologyObjectsInput H)
  {n : ℕ} (M N : ClosedConnectedManifold n) (oM : Objects.Orientation M) (oN : Objects.Orientation N)

structure ConnectedSumFundamentalData where
  group : Type
  groupStructure : Group group
  decidable : DecidableEq group
  countable : Countable group
  leftFactor : Subgroup group
  rightFactor : Subgroup group
  leftFundamentalGroup : leftFactor ≃* FundamentalGroup M.carrier M.point
  rightFundamentalGroup : rightFactor ≃* FundamentalGroup N.carrier N.point
  sumFundamentalGroup : group ≃* FundamentalGroup (Objects.connectedSum M N oM oN).1.carrier
    (Objects.connectedSum M N oM oN).1.point
  freeProduct : IsFreeProductOfSubgroups leftFactor rightFactor
  pinch_class : Objects.fundamentalImage (Objects.connectedSum M N oM oN).1
      (Objects.connectedSum M N oM oN).2 sumFundamentalGroup =
    H.map leftFactor.subtype n (Objects.fundamentalImage M oM leftFundamentalGroup)+
      H.map rightFactor.subtype n (Objects.fundamentalImage N oN rightFundamentalGroup)

attribute [instance] ConnectedSumFundamentalData.groupStructure ConnectedSumFundamentalData.decidable
  ConnectedSumFundamentalData.countable

/-- The standard van Kampen and oriented pinch-map/excision corollary.
The n>=3 hypothesis is retained explicitly. There is no mass or volume
assertion. All groups are identified with actual native fundamental groups.
-/
structure ConnectedSumTopologyInput (H : IntegralGroupHomologyInput) (Objects : ManifoldTopologyObjectsInput H) : Prop where
  facts : ∀ {n : ℕ}, 3 ≤ n → ∀ (M N : ClosedConnectedManifold n)
    (oM : Objects.Orientation M) (oN : Objects.Orientation N),
      Nonempty (ConnectedSumFundamentalData Objects M N oM oN)

def standardConnectedSumModel (Topology : ConnectedSumTopologyInput H Objects)
    (hn : 3 ≤ n) : ConnectedSumFundamentalData Objects M N oM oN :=
  Classical.choice (Topology.facts hn M N oM oN)

end Paper28
