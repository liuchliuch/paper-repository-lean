import CounterFreeHDA.UnaryLanguageCore

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare

def ClosedWord := Word Completion.emptyCube Completion.emptyCube

/-- A block is the ordinary closed letter, or two concurrently started
unary events terminated at both possible positions. -/
inductive SingleBlock : ClosedWord → Prop where
  | mk {U : UCube} (f g : Cubical.Face Completion.emptyCube U)
      (hl : f.Lower) (hu : g.Upper) (hd : U.dim = 1) :
      SingleBlock (.cons (.start f hl hd) (.cons (.stop g hu hd) (.nil _)))

inductive ConcurrentBlock : ClosedWord → Prop where
  | mk {U V W : UCube} (f : Cubical.Face Completion.emptyCube U) (g : Cubical.Face U V)
      (h : Cubical.Face W V) (l : Cubical.Face Completion.emptyCube W)
      (hf : f.Lower) (hg : g.Lower) (hh : h.Upper) (hl : l.Upper)
      (hU : U.dim = 1) (hV : V.dim = U.dim+1) (hW : V.dim = W.dim+1) (h0 : W.dim = 1) :
      ConcurrentBlock (.cons (.start f hf hU) (.cons (.start g hg hV)
        (.cons (.stop h hh hW) (.cons (.stop l hl h0) (.nil _)))))

inductive PairStar : ClosedWord → Prop where
  | nil : PairStar (.nil _)
  | cons {c p : ClosedWord} : ConcurrentBlock c → PairStar p → PairStar (c.append p)

/-- The ST expression C* union C*aP+ before taking the actual label image. -/
inductive ExpressionWord : ClosedWord → Prop where
  | star {p} : PairStar p → ExpressionWord p
  | tail {c a p : ClosedWord} : PairStar c → SingleBlock a → 0 < p.length → ExpressionWord (c.append (a.append p))

private theorem kind_single {p : ClosedWord} (hp : SingleBlock p) (r : Fin 4) :
    wordKind p r = ![1,2,2,3] r := by
  cases hp with
  | @mk U f g hl hu hd =>
    have h := hd
    rcases U with ⟨n,lab⟩
    have hn : n = 1 := Fin.ext h
    subst n
    fin_cases r <;> rfl

private theorem kind_pair {p : ClosedWord} (hp : ConcurrentBlock p) (r : Fin 4) :
    wordKind p r = ![0,2,2,3] r := by
  cases hp with
  | @mk U V W f g h l hf hg hh hl hU hV hW h0 =>
    have hu : U.1 = 1 := Fin.ext hU
    have hv : V.1 = 2 := Fin.ext (by change V.1.val = U.1.val+1 at hV; rw [hu] at hV; exact hV)
    have hw : W.1 = 1 := Fin.ext h0
    rcases U with ⟨u,lu⟩
    rcases V with ⟨v,lv⟩
    rcases W with ⟨w,lw⟩
    change u = 1 at hu
    subst u
    change v = 2 at hv
    subst v
    change w = 1 at hw
    subst w
    fin_cases r <;> rfl

theorem wordKind_append {U V W : UCube} (p : Word U V) (q : Word V W) (r : Kind U) :
    wordKind (p.append q) r = wordKind q (wordKind p r) := by
  induction p with
  | nil => rfl
  | cons s p ih => exact ih q _

theorem pairStar_kind {c : ClosedWord} (h : PairStar c) : wordKind c (0 : Fin 4) = 0 := by
  induction h with
  | nil => rfl
  | cons hc hp ih => rw [wordKind_append,kind_pair hc]; exact ih

theorem expression_accepts {p : ClosedWord} (h : ExpressionWord p) : acceptBit (wordKind p (0 : Fin 4)) = true := by
  cases h with
  | star hc => rw [pairStar_kind hc]; decide
  | tail hc ha hp =>
    rw [wordKind_append,pairStar_kind hc,wordKind_append,kind_single ha]
    exact (closed_word_B _).mpr hp

end CounterFreeHDA.Appendix.Residual
