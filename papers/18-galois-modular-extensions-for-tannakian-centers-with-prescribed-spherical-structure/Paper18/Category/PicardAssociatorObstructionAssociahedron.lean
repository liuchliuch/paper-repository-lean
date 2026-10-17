import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-! # Cancellation on the five-input associahedron

The diagram consists of actual objects and isomorphisms. No pentagon law is
part of its data. The six pentagonal faces may have scalar defects; the three
interchange squares force the alternating product of these defects to be one.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category
universe v u
namespace Paper18.Category.PicardAssociatorObstruction

/-- The fourteen bracketings and twenty-one directed associator moves for
five inputs. The names are edges, not scalar or coherence certificates. -/
structure AssociahedronDiagram (E : Type u) [Category.{v} E] where
  obj : Fin 14 → E
  a : obj 0 ≅ obj 1
  b : obj 0 ≅ obj 2
  c : obj 0 ≅ obj 5
  d : obj 1 ≅ obj 3
  e : obj 1 ≅ obj 6
  f : obj 2 ≅ obj 4
  g : obj 2 ≅ obj 7
  h : obj 3 ≅ obj 4
  i : obj 3 ≅ obj 9
  j : obj 4 ≅ obj 10
  k : obj 5 ≅ obj 6
  l : obj 5 ≅ obj 8
  m : obj 6 ≅ obj 11
  n : obj 7 ≅ obj 8
  o : obj 7 ≅ obj 12
  p : obj 8 ≅ obj 13
  q : obj 9 ≅ obj 10
  r : obj 9 ≅ obj 11
  s : obj 10 ≅ obj 12
  t : obj 11 ≅ obj 13
  z : obj 12 ≅ obj 13

namespace AssociahedronDiagram
variable {E : Type u} [Category.{v} E] [Preadditive E] [Linear ℂ E]
  (D : AssociahedronDiagram E)

def faceLeft : Fin 6 → Σ X Y : E, X ≅ Y
  | 0 => ⟨D.obj 9, D.obj 13, D.q ≪≫ D.s ≪≫ D.z⟩
  | 1 => ⟨D.obj 0, D.obj 8, D.b ≪≫ D.g ≪≫ D.n⟩
  | 2 => ⟨D.obj 1, D.obj 11, D.d ≪≫ D.i ≪≫ D.r⟩
  | 3 => ⟨D.obj 2, D.obj 12, D.f ≪≫ D.j ≪≫ D.s⟩
  | 4 => ⟨D.obj 5, D.obj 13, D.k ≪≫ D.m ≪≫ D.t⟩
  | 5 => ⟨D.obj 0, D.obj 4, D.a ≪≫ D.d ≪≫ D.h⟩

/-- The six actual pentagon boundaries, with no requirement that they
commute. The order agrees with the inhomogeneous four-cocycle equation. -/
theorem scalar_faces_cocycle (w : Fin 6 → ℂˣ)
    (h0 : 𝟙 (D.obj 0) ≠ 0)
    (sq₁ : D.a.hom ≫ D.e.hom = D.c.hom ≫ D.k.hom)
    (sq₂ : D.h.hom ≫ D.j.hom = D.i.hom ≫ D.q.hom)
    (sq₃ : D.n.hom ≫ D.p.hom = D.o.hom ≫ D.z.hom)
    (f₀ : D.q.hom ≫ D.s.hom ≫ D.z.hom =
      (w 0 : ℂ) • (D.r.hom ≫ D.t.hom))
    (f₁ : D.b.hom ≫ D.g.hom ≫ D.n.hom =
      (w 1 : ℂ) • (D.c.hom ≫ D.l.hom))
    (f₂ : D.d.hom ≫ D.i.hom ≫ D.r.hom =
      (w 2 : ℂ) • (D.e.hom ≫ D.m.hom))
    (f₃ : D.f.hom ≫ D.j.hom ≫ D.s.hom =
      (w 3 : ℂ) • (D.g.hom ≫ D.o.hom))
    (f₄ : D.k.hom ≫ D.m.hom ≫ D.t.hom =
      (w 4 : ℂ) • (D.l.hom ≫ D.p.hom))
    (f₅ : D.a.hom ≫ D.d.hom ≫ D.h.hom =
      (w 5 : ℂ) • (D.b.hom ≫ D.f.hom)) :
    w 0 * w 2 * w 4 = w 1 * w 3 * w 5 := by
  have route₁ :
      D.a.hom ≫ D.d.hom ≫ D.h.hom ≫ D.j.hom ≫ D.s.hom ≫ D.z.hom =
        ((w 5 : ℂ) * (w 3 : ℂ) * (w 1 : ℂ)) •
          (D.c.hom ≫ D.l.hom ≫ D.p.hom) := by
    calc
      _ = ((D.a.hom ≫ D.d.hom ≫ D.h.hom) ≫ D.j.hom ≫ D.s.hom ≫ D.z.hom) := by
        simp only [assoc]
      _ = (w 5 : ℂ) • (D.b.hom ≫ (D.f.hom ≫ D.j.hom ≫ D.s.hom) ≫ D.z.hom) := by
        rw [f₅]
        simp only [Linear.smul_comp, assoc]
      _ = ((w 5 : ℂ) * (w 3 : ℂ)) • (D.b.hom ≫ D.g.hom ≫ D.o.hom ≫ D.z.hom) := by
        rw [f₃]
        simp only [Linear.comp_smul, Linear.smul_comp, smul_smul, assoc]
      _ = ((w 5 : ℂ) * (w 3 : ℂ)) • ((D.b.hom ≫ D.g.hom ≫ D.n.hom) ≫ D.p.hom) := by
        rw [← sq₃]
        simp only [assoc]
      _ = _ := by
        rw [f₁]
        simp only [Linear.smul_comp, smul_smul, assoc]
  have route₂ :
      D.a.hom ≫ D.d.hom ≫ D.h.hom ≫ D.j.hom ≫ D.s.hom ≫ D.z.hom =
        ((w 0 : ℂ) * (w 2 : ℂ) * (w 4 : ℂ)) •
          (D.c.hom ≫ D.l.hom ≫ D.p.hom) := by
    calc
      _ = D.a.hom ≫ D.d.hom ≫ (D.h.hom ≫ D.j.hom) ≫ D.s.hom ≫ D.z.hom := by
        simp only [assoc]
      _ = D.a.hom ≫ D.d.hom ≫ D.i.hom ≫ (D.q.hom ≫ D.s.hom ≫ D.z.hom) := by
        rw [sq₂]
        simp only [assoc]
      _ = (w 0 : ℂ) • (D.a.hom ≫ (D.d.hom ≫ D.i.hom ≫ D.r.hom) ≫ D.t.hom) := by
        rw [f₀]
        simp only [Linear.comp_smul, assoc]
      _ = ((w 0 : ℂ) * (w 2 : ℂ)) • ((D.a.hom ≫ D.e.hom) ≫ D.m.hom ≫ D.t.hom) := by
        rw [f₂]
        simp only [Linear.comp_smul, Linear.smul_comp, smul_smul, assoc]
      _ = ((w 0 : ℂ) * (w 2 : ℂ)) • (D.c.hom ≫ (D.k.hom ≫ D.m.hom ≫ D.t.hom)) := by
        rw [sq₁]
        simp only [assoc]
      _ = _ := by
        rw [f₄]
        simp only [Linear.comp_smul, smul_smul]
  have hc := route₂.symm.trans route₁
  have hi := congrArg (fun f => f ≫ (D.c ≪≫ D.l ≪≫ D.p).inv) hc
  have hs : ((w 0 : ℂ) * (w 2 : ℂ) * (w 4 : ℂ)) • 𝟙 (D.obj 0) =
      ((w 5 : ℂ) * (w 3 : ℂ) * (w 1 : ℂ)) • 𝟙 (D.obj 0) := by
    simpa only [Linear.smul_comp, Iso.trans_inv, assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id, comp_id] using hi
  apply Units.ext
  change (w 0 : ℂ) * (w 2 : ℂ) * (w 4 : ℂ) = (w 1 : ℂ) * (w 3 : ℂ) * (w 5 : ℂ)
  have he := (smul_left_injective ℂ h0) hs
  exact he.trans (by ring)

end AssociahedronDiagram
end Paper18.Category.PicardAssociatorObstruction
