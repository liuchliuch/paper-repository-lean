import Paper15.SymmetryTransport
import Mathlib.Tactic.FinCases

noncomputable section
namespace Paper15
@[ext] theorem RespTable.ext {a b : RespTable} (h : ∀i j, a i j = b i j) : a=b := by
  cases a; cases b; congr; funext i j; exact h i j
@[ext] theorem DetTriangle.ext {a b : DetTriangle}
    (hA : a.A=b.A) (hB : a.B=b.B) (hC : a.C=b.C) : a=b := by cases a; cases b; congr

def Symmetry.values (g : Symmetry) (i : Fin 3) : Equiv.Perm (Fin 3) :=
  if i=0 then g.σX else if i=1 then g.σY else g.σZ

def Symmetry.comp (g f : Symmetry) : Symmetry where
  σX := (g.values (f.srcPerm 0)).trans f.σX
  σY := (g.values (f.srcPerm 1)).trans f.σY
  σZ := (g.values (f.srcPerm 2)).trans f.σZ
  srcPerm := f.srcPerm.trans g.srcPerm
  flip := xor g.flip f.flip

lemma perm_cases (p : Equiv.Perm (Fin 3)) :
    (p 0=0 ∧ p 1=1 ∧ p 2=2) ∨ (p 0=0 ∧ p 1=2 ∧ p 2=1) ∨
    (p 0=1 ∧ p 1=0 ∧ p 2=2) ∨ (p 0=1 ∧ p 1=2 ∧ p 2=0) ∨
    (p 0=2 ∧ p 1=0 ∧ p 2=1) ∨ (p 0=2 ∧ p 1=1 ∧ p 2=0) := by
  have h01 : p 0 ≠ p 1 := p.injective.ne (by decide)
  have h02 : p 0 ≠ p 2 := p.injective.ne (by decide)
  have h12 : p 1 ≠ p 2 := p.injective.ne (by decide)
  generalize h0 : p 0 = a at *
  generalize h1 : p 1 = b at *
  generalize h2 : p 2 = c at *
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

set_option maxHeartbeats 0 in
lemma Symmetry.apply_comp (g f : Symmetry) (T : DetTriangle) :
    (g.comp f).apply T = g.apply (f.apply T) := by
  rcases g with ⟨gx,gy,gz,gp,gf⟩
  rcases f with ⟨fx,fy,fz,fp,ff⟩
  rcases perm_cases gp with h|h|h|h|h|h <;>
    rcases h with ⟨h0,h1,h2⟩ <;>
    rcases perm_cases fp with k|k|k|k|k|k <;>
    rcases k with ⟨k0,k1,k2⟩ <;>
    cases gf <;> cases ff <;>
    apply DetTriangle.ext <;> apply RespTable.ext <;> intro i j <;>
    simp [Symmetry.comp,Symmetry.values,Symmetry.apply,applyPerm,valueReindex,
      swapXY,swapYZ,swapXZ,cycleXYZ,cycleXZY,flipAll,RespTable.flip,RespTable.swap,
      h0,h1,h2,k0,k1,k2]

def Symmetry.inv (g : Symmetry) : Symmetry where
  σX := (g.values (g.srcPerm.symm 0)).symm
  σY := (g.values (g.srcPerm.symm 1)).symm
  σZ := (g.values (g.srcPerm.symm 2)).symm
  srcPerm := g.srcPerm.symm
  flip := g.flip

set_option maxHeartbeats 0 in
lemma Symmetry.apply_inv (g : Symmetry) (T : DetTriangle) :
    g.inv.apply (g.apply T) = T := by
  rcases g with ⟨gx,gy,gz,gp,gf⟩
  rcases perm_cases gp with h|h|h|h|h|h <;>
    rcases h with ⟨h0,h1,h2⟩ <;>
    have hi0 := gp.symm_apply_apply 0 <;>
    have hi1 := gp.symm_apply_apply 1 <;>
    have hi2 := gp.symm_apply_apply 2 <;>
    rw [h0] at hi0 <;> rw [h1] at hi1 <;> rw [h2] at hi2 <;>
    cases gf <;> apply DetTriangle.ext <;> apply RespTable.ext <;> intro i j <;>
    simp [Symmetry.inv,Symmetry.values,Symmetry.apply,applyPerm,valueReindex,
      swapXY,swapYZ,swapXZ,cycleXYZ,cycleXZY,flipAll,RespTable.flip,RespTable.swap,
      h0,h1,h2,hi0,hi1,hi2]

lemma gapHolds_symmetry_iff (g : Symmetry) (T : DetTriangle) :
    GapHolds (g.apply T) ↔ GapHolds T := by
  refine ⟨fun h => ?_,fun h => h |> fun h => gapHolds_symmetry h g⟩
  simpa only [g.apply_inv] using gapHolds_symmetry h g.inv

lemma inExceptionalOrbit_symmetry (g : Symmetry) {T : DetTriangle}
    (h : inExceptionalOrbit T) : inExceptionalOrbit (g.apply T) := by
  obtain ⟨f,rfl⟩ := h
  exact ⟨g.comp f,g.apply_comp f _⟩

lemma inExceptionalOrbit_symmetry_iff (g : Symmetry) (T : DetTriangle) :
    inExceptionalOrbit (g.apply T) ↔ inExceptionalOrbit T := by
  refine ⟨fun h => ?_,inExceptionalOrbit_symmetry g⟩
  simpa only [g.apply_inv] using inExceptionalOrbit_symmetry g.inv h

end Paper15
