import Paper15.PositionTable
set_option maxHeartbeats 0
set_option maxRecDepth 100000
position_table%
namespace Paper15.OrbitCheck
noncomputable def positionsChecked : Bool :=
  (List.range 1296).all (fun g => checkPositionMap g (positionMaps.get g))
theorem positionMaps_checked : positionsChecked=true := by decide +kernel
end Paper15.OrbitCheck
