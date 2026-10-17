import Paper19.FiniteCoding

namespace Paper19
namespace FiniteCoding
open scoped symmDiff

theorem nodes_nodup (F : Finset Node) : (nodes F).Nodup :=
  (Denumerable.raise'_sorted _ _).nodup.map (Denumerable.eqv Node).symm.injective

theorem mem_primrec : PrimrecRel (fun σ : Node => fun F : Finset Node => σ ∈ F) :=
  (list_mem_primrec.comp Primrec.fst (nodes_primrec.comp Primrec.snd)).primrecRel.of_eq
    (fun σ F => mem_nodes F σ)

theorem singleton_computable : Computable (fun σ : Node => ({σ} : Finset Node)) :=
  (list_toFinset_computable.comp
    (Primrec.list_cons.comp Primrec.id (Primrec.const [])).to_comp).of_eq (by simp)

theorem symmDiff_computable : Computable (fun p : Finset Node × Finset Node => p.1 ∆ p.2) := by
  have hf := mem_primrec.not.listFilter
  have hl := Primrec.list_append.comp (hf.comp (nodes_primrec.comp Primrec.fst) Primrec.snd)
    (hf.comp (nodes_primrec.comp Primrec.snd) Primrec.fst)
  apply (list_toFinset_computable.comp hl.to_comp).of_eq
  rintro ⟨F,G⟩
  ext σ
  simp [Finset.mem_symmDiff, or_comm, and_comm]

theorem take_primrec : Primrec (fun p : Node × ℕ => p.1.take p.2) :=
  Effective.takeNode_primrec.of_eq Effective.takeNode_eq

def fibre (p : ℕ × (Finset Node × Node)) : List Node :=
  (nodes p.2.1).filter (fun τ => τ.take p.1 = p.2.2)

theorem takeRel_primrec : PrimrecRel (fun τ : Node => fun p : ℕ × Node => τ.take p.1 = p.2) :=
  (Primrec.eq.comp (take_primrec.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
    (Primrec.snd.comp Primrec.snd)).primrecRel

theorem fibre_primrec : Primrec fibre :=
  takeRel_primrec.listFilter.comp (nodes_primrec.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))

theorem fibre_card (n : ℕ) (F : Finset Node) (σ : Node) :
    (fibre (n,F,σ)).length = (F.filter (fun τ => τ.take n = σ)).card := by
  have he : (fibre (n,F,σ)).toFinset = F.filter (fun τ => τ.take n = σ) := by
    ext τ; simp [fibre]
  have hc := List.toFinset_card_of_nodup ((nodes_nodup F).filter (fun τ => decide (τ.take n = σ)))
  change (fibre (n,F,σ)).toFinset.card = (fibre (n,F,σ)).length at hc
  exact hc.symm.trans (congrArg Finset.card he)

def parents (p : ℕ × Finset Node) : List Node :=
  ((nodes p.2).filter (fun τ => τ.length = p.1 + 1)).map (fun τ => τ.take p.1)

theorem parents_primrec : Primrec parents := by
  have hr : PrimrecRel (fun τ : Node => fun n : ℕ => τ.length = n + 1) :=
    (Primrec.eq.comp (Primrec.list_length.comp Primrec.fst) (Primrec.succ.comp Primrec.snd)).primrecRel
  exact Primrec.list_map (hr.listFilter.comp (nodes_primrec.comp Primrec.snd) Primrec.fst)
    (Primrec.to₂ (take_primrec.comp (Primrec.snd.pair (Primrec.fst.comp Primrec.fst))))

theorem mem_parents (n : ℕ) (F : Finset Node) (σ : Node) :
    σ ∈ parents (n,F) ↔ ∃ τ ∈ F, τ.length = n + 1 ∧ τ.take n = σ := by
  simp [parents, and_assoc]

def projectList (p : ℕ × Finset Node) : List Node :=
  (parents p).filter (fun σ => Odd (fibre (p.1,p.2,σ)).length)

theorem projectList_primrec : Primrec projectList := by
  have hc := Primrec.list_length.comp (fibre_primrec.comp
    ((Primrec.fst.comp Primrec.snd).pair ((Primrec.snd.comp Primrec.snd).pair Primrec.fst)))
  have ho : PrimrecRel (fun σ : Node => fun p : ℕ × Finset Node => Odd (fibre (p.1,p.2,σ)).length) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp hc (Primrec.const 2)) (Primrec.const 1)).primrecRel.of_eq
      (fun _ _ => Nat.odd_iff.symm)
  exact ho.listFilter.comp parents_primrec Primrec.id

theorem projectList_correct (T : Tree) (n : ℕ) (F : Finset Node) :
    (projectList (n,F)).toFinset = proj T n F := by
  ext σ
  simp only [List.mem_toFinset, projectList, List.mem_filter, mem_parents, fibre_card, mem_proj_iff, decide_eq_true_eq]

theorem proj_computable (T : Tree) : Computable (fun p : ℕ × Finset Node => proj T p.1 p.2) :=
  (list_toFinset_computable.comp projectList_primrec.to_comp).of_eq (fun p => projectList_correct T p.1 p.2)

def childPick (p : ℕ × (Finset Node × Node)) : Node := (fibre p).getD 0 []

theorem childPick_primrec : Primrec childPick :=
  (Primrec.list_getD []).comp fibre_primrec (Primrec.const 0)

def symmDiffCodes (p : ℕ × ℕ) : ℕ :=
  @Encodable.encode (Finset Node) (Primcodable.toEncodable)
    (Denumerable.ofNat (Finset Node) p.1 ∆ Denumerable.ofNat (Finset Node) p.2)

set_option maxHeartbeats 500000 in
theorem symmDiffCodes_computable : Computable symmDiffCodes := by
  have hf : Computable (fun p : ℕ × ℕ => Denumerable.ofNat (Finset Node) p.1) :=
    (Primrec.ofNat (Finset Node)).to_comp.comp Computable.fst
  have hg : Computable (fun p : ℕ × ℕ => Denumerable.ofNat (Finset Node) p.2) :=
    (Primrec.ofNat (Finset Node)).to_comp.comp Computable.snd
  have hd : Computable (fun p : ℕ × ℕ =>
      Denumerable.ofNat (Finset Node) p.1 ∆ Denumerable.ofNat (Finset Node) p.2) :=
    Computable.comp (f := fun p : Finset Node × Finset Node => p.1 ∆ p.2)
      (g := fun p : ℕ × ℕ => (Denumerable.ofNat (Finset Node) p.1, Denumerable.ofNat (Finset Node) p.2))
      symmDiff_computable (Computable.pair hf hg)
  have he : Computable (fun F : Finset Node => @Encodable.encode (Finset Node) (Primcodable.toEncodable) F) :=
    Primrec.encode.to_comp
  exact Computable.comp (f := fun F : Finset Node => @Encodable.encode (Finset Node) (Primcodable.toEncodable) F)
    (g := fun p : ℕ × ℕ => Denumerable.ofNat (Finset Node) p.1 ∆ Denumerable.ofNat (Finset Node) p.2) he hd

end FiniteCoding
end Paper19
