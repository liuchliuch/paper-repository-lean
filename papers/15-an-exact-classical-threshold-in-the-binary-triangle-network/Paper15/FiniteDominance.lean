import Paper15.FiniteResponse
import Paper15.TernaryLaw

noncomputable section
namespace Paper15
open Finset BigOperators

def AggregateMoments.vec (m : AggregateMoments) (u : Fin 3) : ℝ :=
  if u=0 then m.M1 else if u=1 then m.M2 else m.M3

lemma detMoments_vec (T : DetTriangle) (qx qy qz : Simplex2) (u : Fin 3) :
    (detMoments' T qx qy qz).vec u =
    ∑ i, qx i * ∑ j, qy j * ∑ k, qz k * momentAt (T.A j k) (T.B k i) (T.C i j) u := by
  fin_cases u <;>
    simp [AggregateMoments.vec,momentAt,detMoments',detMoments]
  all_goals simp_rw [Finset.mul_sum,← mul_assoc]
  all_goals try simp_rw [← mul_div_assoc]
  all_goals try simp_rw [mul_add]
  all_goals try simp_rw [Finset.sum_add_distrib]
  all_goals try simp_rw [← Finset.sum_div]
  all_goals simp only [Finset.sum_add_distrib,← mul_assoc]

namespace FiniteResponse
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- The finite deterministic reduction used in Lemma 4, with all source
sizes arbitrary. The two constrained moments are exactly preserved. -/
theorem exists_ternary_dominating (F : FiniteResponse α β γ) (hF : F.Deterministic)
    (qx : Law α) (qy : Law β) (qz : Law γ) :
    ∃ (T : DetTriangle) (sx sy sz : Simplex2),
      (detMoments' T sx sy sz).M1 = F.moments qx qy qz 0 ∧
      (detMoments' T sx sy sz).M3 = F.moments qx qy qz 2 ∧
      F.moments qx qy qz 1 ≤ (detMoments' T sx sy sz).M2 := by
  classical
  let fx := fun u x => qy.avg (fun y => qz.avg (fun z => momentAt (F.A y z) (F.B z x) (F.C x y) u))
  obtain ⟨rx,hsx,hx0,hx2,hx1⟩ := qx.exists_sparse (fx 0) (fx 2) (fx 1)
  let fy := fun u y => rx.avg (fun x => qz.avg (fun z => momentAt (F.A y z) (F.B z x) (F.C x y) u))
  obtain ⟨ry,hsy,hy0,hy2,hy1⟩ := qy.exists_sparse (fy 0) (fy 2) (fy 1)
  let fz := fun u z => rx.avg (fun x => ry.avg (fun y => momentAt (F.A y z) (F.B z x) (F.C x y) u))
  obtain ⟨rz,hsz,hz0,hz2,hz1⟩ := qz.exists_sparse (fz 0) (fz 2) (fz 1)
  have hm_y (r : Law β) (u : Fin 3) : r.avg (fy u) = F.moments rx r qz u := by
    exact Law.avg_comm r rx _
  have hm_z (r : Law γ) (u : Fin 3) : r.avg (fz u) = F.moments rx ry r u := by
    dsimp [fz,moments]
    rw [Law.avg_comm r rx]
    congr 1; funext x
    exact Law.avg_comm r ry _
  have h0 : F.moments rx ry rz 0 = F.moments qx qy qz 0 :=
    (hm_z rz 0).symm.trans (hz0.trans ((hm_z qz 0).trans
      ((hm_y ry 0).symm.trans (hy0.trans ((hm_y qy 0).trans hx0)))))
  have h2 : F.moments rx ry rz 2 = F.moments qx qy qz 2 :=
    (hm_z rz 2).symm.trans (hz2.trans ((hm_z qz 2).trans
      ((hm_y ry 2).symm.trans (hy2.trans ((hm_y qy 2).trans hx2)))))
  have h1 : F.moments qx qy qz 1 ≤ F.moments rx ry rz 1 := by
    calc
      _ ≤ F.moments rx qy qz 1 := hx1
      _ = qy.avg (fy 1) := (hm_y qy 1).symm
      _ ≤ ry.avg (fy 1) := hy1
      _ = qz.avg (fz 1) := (hm_y ry 1).trans (hm_z qz 1).symm
      _ ≤ rz.avg (fz 1) := hz1
      _ = _ := hm_z rz 1
  obtain ⟨sx,px,hpx⟩ := rx.exists_ternary hsx
  obtain ⟨sy,py,hpy⟩ := ry.exists_ternary hsy
  obtain ⟨sz,pz,hpz⟩ := rz.exists_ternary hsz
  let T : DetTriangle :=
    ⟨⟨fun j k => F.A (py j) (pz k),fun j k => hF.1 _ _⟩,
      ⟨fun k i => F.B (pz k) (px i),fun k i => hF.2.1 _ _⟩,
      ⟨fun i j => F.C (px i) (py j),fun i j => hF.2.2 _ _⟩⟩
  have hm (u : Fin 3) : (detMoments' T sx sy sz).vec u = F.moments rx ry rz u := by
    rw [detMoments_vec]
    change (∑ i, sx i * ∑ j, sy j * ∑ k, sz k *
      momentAt (F.A (py j) (pz k)) (F.B (pz k) (px i)) (F.C (px i) (py j)) u) = _
    have hinner (i : Fin 3) : (∑ j, sy j * ∑ k, sz k *
        momentAt (F.A (py j) (pz k)) (F.B (pz k) (px i)) (F.C (px i) (py j)) u) =
        ry.avg (fun y => rz.avg (fun z => momentAt (F.A y z) (F.B z (px i)) (F.C (px i) y) u)) := by
      rw [← hpy (fun y => rz.avg (fun z => momentAt (F.A y z) (F.B z (px i)) (F.C (px i) y) u))]
      apply sum_congr rfl
      intro j _
      congr 1
      exact hpz (fun z => momentAt (F.A (py j) z) (F.B z (px i)) (F.C (px i) (py j)) u)
    simp_rw [hinner]
    exact hpx (fun x => ry.avg (fun y => rz.avg (fun z => momentAt (F.A y z) (F.B z x) (F.C x y) u)))

  refine ⟨T,sx,sy,sz,?_,?_,?_⟩
  · exact (hm 0).trans h0
  · exact (hm 2).trans h2
  · exact h1.trans (hm 1).ge

end FiniteResponse
end Paper15
