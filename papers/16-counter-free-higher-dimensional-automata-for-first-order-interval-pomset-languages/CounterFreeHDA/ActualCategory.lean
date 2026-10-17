import CounterFreeHDA.IdentityComposition

/-! The actual bounded interval-pomset category, with genuine gluing on
isomorphism classes. All category laws are derived from actual event/order
isomorphisms, rather than stipulated for raw data. -/
namespace CounterFreeHDA.Cubical.BoundedArrow
universe u
variable {Lab : Type u} {k : ℕ} {U V W : Cube Lab k}

/-- Actual subsumption is compatible with actual interface gluing. -/
theorem subsumption_comp (A A' : BoundedArrow U V) (B B' : BoundedArrow V W)
    (ha : A.pom ⊑ₛ A'.pom) (hb : B.pom ⊑ₛ B'.pom) : (A.comp B).pom ⊑ₛ (A'.comp B').pom := by
  let R := Refinement.witness ha
  let T := Refinement.witness hb
  let l := Arrow.leftInclusion A'.toArrow B'.toArrow
  let r := Arrow.rightInclusion A'.toArrow B'.toArrow
  let p := (Refinement.map (k := k) R).comp l
  let q := (Refinement.map (k := k) T).comp r
  have hs : p.app A.toArrow.targetCell = q.app B.toArrow.sourceCell := by
    change l.app (Refinement.transport R A.toArrow.targetCell) = r.app (Refinement.transport T B.toArrow.sourceCell)
    rw [Refinement.transport_target,Refinement.transport_source]
    exact Arrow.inclusion_seam A'.toArrow B'.toArrow
  let m := A.toArrow.glueMap B.toArrow p q hs
  apply Arrow.subsumption_of_map _ _ m
  · apply (A.toArrow.glueMap_source B.toArrow p q hs).trans
    change l.app (Refinement.transport R A.toArrow.sourceCell) = _
    rw [Refinement.transport_source]
    exact Arrow.leftInclusion_source A'.toArrow B'.toArrow
  · apply (A.toArrow.glueMap_target B.toArrow p q hs).trans
    change r.app (Refinement.transport T B.toArrow.targetCell) = _
    rw [Refinement.transport_target]
    exact Arrow.rightInclusion_target A'.toArrow B'.toArrow

end CounterFreeHDA.Cubical.BoundedArrow

namespace CounterFreeHDA.Cubical.PomsetCategory
universe u v
variable {Lab : Type u} {k : ℕ}

def isoSetoid (U V : Cube Lab k) : Setoid (BoundedArrow U V) where
  r A B := Nonempty (PomsetIso A.pom.val B.pom.val)
  iseqv := ⟨fun A => ⟨PomsetIso.refl _⟩,fun h => h.elim (fun φ => ⟨φ.symm⟩),
    fun h h' => h.elim (fun φ => h'.elim (fun ψ => ⟨φ.trans ψ⟩))⟩

abbrev Hom (U V : Cube Lab k) := Quotient (isoSetoid U V)

def mk {U V : Cube Lab k} (A : BoundedArrow U V) : Hom U V := Quotient.mk _ A

noncomputable def comp {U V W : Cube Lab k} (A : Hom U V) (B : Hom V W) : Hom U W :=
  Quotient.liftOn₂ A B (fun A B => mk (A.comp B)) (by
    rintro A B A' B' ⟨φ⟩ ⟨ψ⟩
    exact Quotient.sound ⟨PomsetIso.glueIso φ ψ
      (GlueMatch.ofType (A.target.trans B.source.symm)) (GlueMatch.ofType (A'.target.trans B'.source.symm))⟩)

/-- The paper's actual source category iiPoms≤k. -/
noncomputable def category (Lab : Type u) (k : ℕ) : Recognition.Cat (Cube Lab k) where
  Hom := Hom
  id U := mk (BoundedArrow.ident U)
  comp := comp
  id_comp A := by
    induction A using Quotient.inductionOn with
    | _ A => exact Quotient.sound ⟨A.identityLeftIso⟩
  comp_id A := by
    induction A using Quotient.inductionOn with
    | _ A => exact Quotient.sound ⟨A.identityRightIso⟩
  assoc A B C := by
    induction A using Quotient.inductionOn with
    | _ A =>
      induction B using Quotient.inductionOn with
      | _ B =>
        induction C using Quotient.inductionOn with
        | _ C => exact Quotient.sound ⟨BoundedArrow.assocIso A B C⟩

def subsumption {U V : Cube Lab k} (A B : Hom U V) : Prop :=
  Quotient.liftOn₂ A B (fun A B => A.pom ⊑ₛ B.pom) (by
    rintro A B A' B' ⟨φ⟩ ⟨ψ⟩
    apply propext
    exact ⟨fun h => subsumption_trans φ.symm.subsumption (subsumption_trans h ψ.subsumption),
      fun h => subsumption_trans φ.subsumption (subsumption_trans h ψ.symm.subsumption)⟩)

theorem sub_context {U V S T : Cube Lab k} {A B : Hom U V} (h : subsumption A B)
    (a : Hom S U) (b : Hom V T) : subsumption (comp (comp a A) b) (comp (comp a B) b) := by
  induction A using Quotient.inductionOn with
  | _ A =>
    induction B using Quotient.inductionOn with
    | _ B =>
      induction a using Quotient.inductionOn with
      | _ a =>
        induction b using Quotient.inductionOn with
        | _ b =>
          exact BoundedArrow.subsumption_comp _ _ b b
            (BoundedArrow.subsumption_comp a a A B (subsumption_refl a.pom) h) (subsumption_refl b.pom)

variable {L : Set (IntervalPom Lab)} {h : ℕ} (G : FinitePomsetRecognizer.{u,v} (k := k) L h)

noncomputable def map {U V : Cube Lab k} (A : Hom U V) : G.D.Hom U V :=
  Quotient.liftOn A (fun A => G.map A) (by
    rintro A B ⟨φ⟩
    exact G.map_iso A B φ)

/-- The original actual recognizer descends to a genuine category functor. -/
noncomputable def functor : Recognition.Functor (category Lab k) (Recognition.ofFinite G.D) where
  obj := id
  map := map G
  map_id := G.map_id
  map_comp A B := by
    induction A using Quotient.inductionOn with
    | _ A =>
      induction B using Quotient.inductionOn with
      | _ B => exact G.map_comp A B

end CounterFreeHDA.Cubical.PomsetCategory
