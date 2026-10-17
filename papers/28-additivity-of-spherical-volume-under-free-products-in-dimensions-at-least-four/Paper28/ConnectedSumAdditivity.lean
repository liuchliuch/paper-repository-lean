import Paper28.FreeProductAdditivity
import Paper28.ConnectedSumTopologyInput

/-! Original Corollary 1.2. The volume is the actual current mass infimum
of the classifying image of the oriented fundamental class. Standard
van Kampen/pinch topology supplies only the free-product identification
and fundamental-class identity; Theorem 1.1 supplies additivity.
Dimension is written k+4, covering every n>=4.
-/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable (Std : PaperStandardInputs) (Objects : ManifoldTopologyObjectsInput Std.groupHomology)

def manifoldSphericalVolume (k : ℕ) (M : ClosedConnectedManifold (k+4)) (oM : Objects.Orientation M)
    {Γ : Type} [Group Γ] [DecidableEq Γ] [Countable Γ]
    (D : SphericalQuotientCurrentData Std.currentCalculus Γ)
    (model : Γ ≃* FundamentalGroup M.carrier M.point) : ℝ :=
  groupSphericalVolume Std.groupHomology Std.currentCalculus Std.song D.M D.algebra (k+3)
    (Objects.fundamentalImage M oM model)

theorem connected_sum_additivity_from_facts (k : ℕ) (M N : ClosedConnectedManifold (k+4))
    (oM : Objects.Orientation M) (oN : Objects.Orientation N)
    (CS : ConnectedSumFundamentalData Objects M N oM oN)
    (DG : SphericalQuotientCurrentData Std.currentCalculus CS.group)
    (DA : SphericalQuotientCurrentData Std.currentCalculus CS.leftFactor)
    (DB : SphericalQuotientCurrentData Std.currentCalculus CS.rightFactor) :
    manifoldSphericalVolume Std Objects k (Objects.connectedSum M N oM oN).1 (Objects.connectedSum M N oM oN).2
      DG CS.sumFundamentalGroup =
      manifoldSphericalVolume Std Objects k M oM DA CS.leftFundamentalGroup+
        manifoldSphericalVolume Std Objects k N oN DB CS.rightFundamentalGroup := by
  unfold manifoldSphericalVolume
  rw [CS.pinch_class]
  exact theorem_1_1 Std DG DA DB CS.freeProduct k
    (Objects.fundamentalImage M oM CS.leftFundamentalGroup) (Objects.fundamentalImage N oN CS.rightFundamentalGroup)

theorem corollary_1_2 (Topology : ConnectedSumTopologyInput Std.groupHomology Objects)
    (k : ℕ) (M N : ClosedConnectedManifold (k+4)) (oM : Objects.Orientation M) (oN : Objects.Orientation N) :
    let CS := standardConnectedSumModel Objects M N oM oN Topology (by omega : 3 ≤ k+4)
    ∀ (DG : SphericalQuotientCurrentData Std.currentCalculus CS.group)
      (DA : SphericalQuotientCurrentData Std.currentCalculus CS.leftFactor)
      (DB : SphericalQuotientCurrentData Std.currentCalculus CS.rightFactor),
    manifoldSphericalVolume Std Objects k (Objects.connectedSum M N oM oN).1 (Objects.connectedSum M N oM oN).2
      DG CS.sumFundamentalGroup =
      manifoldSphericalVolume Std Objects k M oM DA CS.leftFundamentalGroup+
        manifoldSphericalVolume Std Objects k N oN DB CS.rightFundamentalGroup := by
  dsimp only
  intro DG DA DB
  exact connected_sum_additivity_from_facts Std Objects k M N oM oN
    (standardConnectedSumModel Objects M N oM oN Topology (by omega : 3 ≤ k+4)) DG DA DB

end Paper28
