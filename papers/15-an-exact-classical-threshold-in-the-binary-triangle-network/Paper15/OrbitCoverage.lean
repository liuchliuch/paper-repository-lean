import Paper15.ResponseDistance

noncomputable section
namespace Paper15
open Finset BigOperators

/-- Induction on the Boolean cube of all 27 response entries. -/
theorem responseCube_induction (P : DetTriangle → Prop)
    (hzero : P (DetTriangle.ofBits (fun _ => false)))
    (hstep : ∀T p,P T → P (flipAt T p)) (T : DetTriangle) : P T := by
  classical
  have haux (s : Finset (Fin 27)) : P (DetTriangle.ofBits (fun p => decide (p∈s))) := by
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | @insert p s hp ih =>
      convert hstep (DetTriangle.ofBits (fun q => decide (q∈s))) p ih using 1
      unfold flipAt
      rw [DetTriangle.bits_ofBits]
      congr 1
      funext q
      by_cases hq : q=p
      · subst q; simp [hp]
      · simp [Function.update_of_ne hq,hq]
  let s := univ.filter (fun p => T.bits p)
  have he : (fun p => decide (p∈s))=T.bits := by
    funext p
    simp [s]
  simpa only [he,DetTriangle.ofBits_bits] using haux s

/-- A supplied list of representatives covers every table if it contains
the zero word and its symmetry orbits are closed under every single-entry
flip. This needs 27 transitions per representative, rather than a trusted
scan of all 2^27 tables. -/
theorem orbit_coverage_from_neighbours (reps : Finset Nat) (hzero : 0∈reps)
    (hneighbours : ∀r∈reps,∀p : Fin 27,∃s∈reps,∃g : Symmetry,
      g.apply (DetTriangle.ofPattern s)=flipAt (DetTriangle.ofPattern r) p) :
    ∀T : DetTriangle,∃r∈reps,∃g : Symmetry,g.apply (DetTriangle.ofPattern r)=T := by
  let P := fun T => ∃r∈reps,∃g : Symmetry,g.apply (DetTriangle.ofPattern r)=T
  apply responseCube_induction P
  · refine ⟨0,hzero,Symmetry.one,?_⟩
    rw [Symmetry.apply_one,DetTriangle.ofPattern_eq_ofBits]
    simp
  · intro T p hT
    obtain ⟨r,hr,g,hg⟩ := hT
    let V := g.inv.apply (flipAt T p)
    have hd : responseDist (DetTriangle.ofPattern r) V=1 := by
      have he := responseDist_symmetry (DetTriangle.ofPattern r) V g
      rw [hg,show g.apply V=flipAt T p from g.apply_inv_right _] at he
      rw [← he]
      exact (responseDist_one_iff T _).mpr ⟨p,rfl⟩
    obtain ⟨q,hq⟩ := (responseDist_one_iff _ _).mp hd
    obtain ⟨s,hs,f,hf⟩ := hneighbours r hr q
    refine ⟨s,hs,g.comp f,?_⟩
    rw [Symmetry.apply_comp,hf,← hq]
    exact g.apply_inv_right _

end Paper15
