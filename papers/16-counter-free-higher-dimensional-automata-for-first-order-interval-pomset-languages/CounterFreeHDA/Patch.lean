import CounterFreeHDA.Cubical

/-! Gluing actual cubical maps on a cover by two face-closed pieces. -/
namespace CounterFreeHDA.Cubical
universe u v w
variable {Lab : Type u} {k : ℕ}

structure Patch (X : Precubical.{u,v} Lab k) (Y : Precubical.{u,w} Lab k) where
  pred : ∀ {U}, X.Cell U → Prop
  closed : ∀ {U V} (f : Face U V) (x : X.Cell V), pred x → pred (X.face f x)
  app : ∀ {U} (x : X.Cell U), pred x → Y.Cell U
  natural : ∀ {U V} (f : Face U V) (x : X.Cell V) (h : pred x),
    app (X.face f x) (closed f x h) = Y.face f (app x h)

variable {X : Precubical.{u,v} Lab k} {Y : Precubical.{u,w} Lab k}

noncomputable def gluePatches (L R : Patch X Y)
    (cover : ∀ U (x : X.Cell U), L.pred x ∨ R.pred x)
    (agree : ∀ U (x : X.Cell U) (hl : L.pred x) (hr : R.pred x), L.app x hl = R.app x hr) :
    Map X Y := by
  classical
  exact {
    app := fun {U} x => if hl : L.pred x then L.app x hl else R.app x ((cover U x).resolve_left hl)
    natural := by
      intro U V f x
      by_cases hl : L.pred x
      · simp only [dif_pos hl,dif_pos (L.closed f x hl)]
        exact L.natural f x hl
      · have hr := (cover V x).resolve_left hl
        have hrf := R.closed f x hr
        by_cases hlf : L.pred (X.face f x)
        · simp only [dif_pos hlf,dif_neg hl]
          exact (agree _ _ hlf hrf).trans (R.natural f x hr)
        · simp only [dif_neg hlf,dif_neg hl]
          exact R.natural f x hr }

@[simp] theorem gluePatches_left (L R : Patch X Y)
    (cover : ∀ U (x : X.Cell U), L.pred x ∨ R.pred x)
    (agree : ∀ U (x : X.Cell U) (hl : L.pred x) (hr : R.pred x), L.app x hl = R.app x hr)
    {U} (x : X.Cell U) (hx : L.pred x) : (gluePatches L R cover agree).app x = L.app x hx := by
  classical
  change (if hl : L.pred x then L.app x hl else R.app x _) = _
  rw [dif_pos hx]

theorem gluePatches_right (L R : Patch X Y)
    (cover : ∀ U (x : X.Cell U), L.pred x ∨ R.pred x)
    (agree : ∀ U (x : X.Cell U) (hl : L.pred x) (hr : R.pred x), L.app x hl = R.app x hr)
    {U} (x : X.Cell U) (hx : R.pred x) : (gluePatches L R cover agree).app x = R.app x hx := by
  classical
  by_cases hl : L.pred x
  · rw [gluePatches_left L R cover agree x hl]
    exact agree U x hl hx
  · change (if h : L.pred x then L.app x h else R.app x _) = _
    rw [dif_neg hl]

end CounterFreeHDA.Cubical
