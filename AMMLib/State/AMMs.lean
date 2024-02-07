import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Sym.Sym2
import HelpersLib.NNReal
import HelpersLib.Prod
import HelpersLib.PReal.Basic
import HelpersLib.Finsupp2
import AMMLib.State.Tokens
import AMMLib.State.AtomicWall

/-
The intuition is for example to model a set of two AMMs {r₀:τ₀, r₁:τ₁} and {r₂:τ₂, r₃:τ₃} as `f` with
f τ₀ τ₁ = r₀
f τ₁ τ₀ = r₁
f τ₂ τ₃ = r₂
f τ₃ τ₂ = r₃

And zero for any other input.
-/

structure AMMs where
  res: T →₀ W₀
  distinct: ∀ (t: T), res t t = 0
  posres: ∀ (t0 t1: T), res t0 t1 ≠ 0 ↔ res t1 t0 ≠ 0

def AMMs.empty: AMMs :=
⟨
  0,
  by intro _; simp,
  by intro t0 t1; apply Iff.intro;
     . simp
     . simp
⟩

def AMMs.init (amms: AMMs) (t0 t1: T): Prop :=
  amms.res t0 t1 ≠ 0

theorem AMMs.empty_uninit (t0 t1: T):
  ¬ AMMs.empty.init t0 t1 := by
  simp [init, empty]

theorem AMMs.same_uninit (amms: AMMs)(t: T):
  ¬amms.init t t := by unfold init; simp [amms.distinct]

def AMMs.init.swap {amms: AMMs} {t0 t1: T} (h: amms.init t0 t1):
  amms.init t1 t0 := by
  unfold init at *
  exact (amms.posres t0 t1).mp h

def AMMs.init_swap_iff (amms: AMMs) (t0 t1: T):
 amms.init t0 t1 ↔ amms.init t1 t0 := by
  unfold init
  exact amms.posres t0 t1

def AMMs.init.dif {amms: AMMs} {t0 t1: T} (h: amms.init t0 t1):
  t0 ≠ t1 := by
  unfold init at h
  rcases (Decidable.em (t0=t1)) with eq|neq
  . rw [eq] at h
    have h' := amms.distinct t1
    contradiction
  . exact Ne.intro neq

theorem AMMs.init.samepair {amms: AMMs} {t0 t1: T} (h: amms.init t0 t1) {t0' t1': T} (same: samemint t0 t1 t0' t1'):
  amms.init t0' t1' := by
  rcases same with ⟨a,b⟩|⟨a,b⟩
  . simp [← a, ← b, h]
  . simp [← a, ← b, h.swap]

-- Set an AMM's reserves to an arbitrary pair of positive reals
noncomputable def AMMs.initialize
  (amms: AMMs) {t0 t1: T} (hdif: t0 ≠ t1) (r0 r1: ℝ>0): AMMs :=

  ⟨
    (amms.res.update t0 ((amms.res t0).update t1 r0)
    ).update t1 ((amms.res t1).update t0 r1),

    by
    intro t
    rcases Decidable.em (t=t0), Decidable.em (t=t1)
           with ⟨eq0|neq0, eq1|neq1⟩
    . rw [eq0] at eq1; contradiction
    . simp [eq0, hdif, amms.distinct t0]
    . simp [eq1, hdif, amms.distinct t1, hdif.symm]
    . simp [neq0, neq1, amms.distinct t],


    by
    intro t0' t1'
    rcases Decidable.em (t0'=t0), Decidable.em (t0'=t1),
          Decidable.em (t1'=t0), Decidable.em (t1'=t1)
          with ⟨a|a, b|b, c|c, d|d⟩
    <;>
    simp [a, b, c, d, hdif, r0.toNNReal_ne_zero, r1.toNNReal_ne_zero, amms.posres]
  ⟩

-- An AMM is initialized
@[simp] theorem AMMs.initialize_init_diffpair
  (amms: AMMs) {t0 t1: T} (hdif: t0 ≠ t1) (r0 r1: ℝ>0)
  (t0' t1': T) (h: diffmint t0 t1 t0' t1'):
  (amms.initialize hdif r0 r1).init t0' t1' ↔ amms.init t0' t1' := by

    -- t0'=t1' case is trivial, since a t ↔ t exchange
    -- may not exist
    rcases Decidable.em (t0'=t1') with triv|hdif'
    . simp [triv, same_uninit]
    . unfold init AMMs.initialize
      rcases h with ⟨a,b⟩|⟨a,b⟩
      -- Otherwise, by cases on the intersection between
      -- {t0,t1} and {t0',t1'}
      . rcases Decidable.em (t1=t1') with c|c
        . simp [a.symm, c, hdif, hdif']
        . rcases Decidable.em (t1=t0') with d|d
          . simp [b.symm, d]
          . simp [a.symm, b, c, (Ne.intro d).symm, hdif, hdif']
      . rcases Decidable.em (t0=t1') with c|c
        . simp [a.symm, c, hdif, hdif']
        . rcases Decidable.em (t0=t0') with d|d
          . simp [a.symm, b.symm, d]
          . simp [a.symm, b, c, (Ne.intro d).symm, hdif, hdif']

@[simp] theorem AMMs.initialize_init_not_diffpair
  (amms: AMMs) {t0 t1: T} (hdif: t0 ≠ t1) (r0 r1: ℝ>0)
  (t0' t1': T) (h: samemint t0 t1 t0' t1'):
  (amms.initialize hdif r0 r1).init t0' t1' := by

  unfold init
  rcases h with ⟨a,b⟩|⟨a,b⟩
  . simp [AMMs.initialize, ← a, ← b, hdif, r0.toNNReal_ne_zero]
  . simp [AMMs.initialize, ← a, ← b, hdif, r1.toNNReal_ne_zero]

@[simp] theorem AMMs.initialize_init_self
  (amms: AMMs) {t0 t1: T} (hdif: t0 ≠ t1) (r0 r1: ℝ>0):
  (amms.initialize hdif r0 r1).init t0 t1 :=
  initialize_init_not_diffpair amms hdif r0 r1 t0 t1 (self_samemint t0 t1)

def AMMs.r0 (amms: AMMs) (t0 t1: T)
  (h: amms.init t0 t1): ℝ>0 :=

  ⟨amms.res t0 t1, by
    unfold init at h
    exact NNReal.neq_zero_imp_gt h
  ⟩

def AMMs.r1 (amms: AMMs) (t0 t1: T)
  (h: amms.init t0 t1): ℝ>0 :=

  ⟨amms.res t1 t0, by
    unfold init at h
    exact NNReal.neq_zero_imp_gt ((amms.posres t0 t1).mp h)
  ⟩

theorem AMMs.r0_reorder
  (amms: AMMs) (t1 t0: T) (h: amms.init t1 t0):
  amms.r0 t1 t0 h = amms.r1 t0 t1 h.swap := by
  simp [r0, r1]

theorem AMMs.r1_reorder
  (amms: AMMs) (t1 t0: T) (h: amms.init t1 t0):
  amms.r1 t1 t0 h = amms.r0 t0 t1 h.swap := by
  simp [r0, r1]

noncomputable instance decidableInit (amms: AMMs) (t0 t1: T): Decidable (amms.init t0 t1)
  := by unfold AMMs.init
        infer_instance

noncomputable def AMMs.add_r0 (amms: AMMs) (t0 t1: T)
  (h: amms.init t0 t1) (x: ℝ>0): AMMs :=
  amms.initialize h.dif ((amms.r0 t0 t1 h) + x) (amms.r1 t0 t1 h)

noncomputable def AMMs.sub_r0 (amms: AMMs) (t0 t1: T)
  (h: amms.init t0 t1) (x: ℝ>0)
  (nodrain: x < amms.r0 t0 t1 h): AMMs :=
  amms.initialize h.dif ((amms.r0 t0 t1 h).sub x nodrain) (amms.r1 t0 t1 h)

noncomputable def AMMs.add_r1 (amms: AMMs) (t0 t1: T)
  (h: amms.init t0 t1) (x: ℝ>0): AMMs :=
  amms.initialize h.dif (amms.r0 t0 t1 h) ((amms.r1 t0 t1 h) + x)

noncomputable def AMMs.sub_r1 (amms: AMMs) (t0 t1: T)
  (h: amms.init t0 t1) (x: ℝ>0)
  (nodrain: x < amms.r1 t0 t1 h): AMMs :=
  amms.initialize h.dif
    (amms.r0 t0 t1 h) ((amms.r1 t0 t1 h).sub x nodrain)

@[simp] theorem AMMs.r0_of_initialize
  (amms: AMMs) {t0 t1: T} (hdif: t0 ≠ t1) (r0 r1: ℝ>0):
  (amms.initialize hdif r0 r1).r0 t0 t1 (by simp) = r0 := by
  simp [AMMs.r0, AMMs.initialize, hdif]

@[simp] theorem AMMs.r1_of_initialize
  (amms: AMMs) {t0 t1: T} (hdif: t0 ≠ t1) (r0 r1: ℝ>0):
  (amms.initialize hdif r0 r1).r1 t0 t1 (by simp) = r1 := by
  simp [AMMs.r1, AMMs.initialize, hdif]

@[simp] theorem AMMs.r0_of_initialize_diffpair
  (amms: AMMs) {t0 t1: T} (hdif: t0 ≠ t1) (r0 r1: ℝ>0)
  (t0' t1': T) (hinit: amms.init t0' t1') (difp: diffmint t0 t1 t0' t1'):
  (amms.initialize hdif r0 r1).r0 t0' t1' (by simp[difp, hinit]) = amms.r0 t0' t1' hinit := by
  rcases difp with ⟨a,b⟩|⟨a,b⟩
  . rcases Decidable.em (t1=t1') with c|c
    . simp [AMMs.r0, AMMs.initialize, a.symm, c, hinit.dif]
    . rcases Decidable.em (t0'=t1) with d|d
      . simp [AMMs.r0, AMMs.initialize, a.symm, b.symm, c, hinit.dif, d]
      . simp [AMMs.r0, AMMs.initialize, a.symm, c, hinit.dif, d]
  . rcases Decidable.em (t0=t1') with c|c
    . simp [AMMs.r0, AMMs.initialize, a.symm, c, hinit.dif]
    . rcases Decidable.em (t0'=t0) with d|d
      . simp [AMMs.r0, AMMs.initialize, b.symm, d, hdif]
      . simp [AMMs.r0, AMMs.initialize, a.symm, c, hinit.dif, d]

@[simp] theorem AMMs.r1_of_initialize_diffpair
  (amms: AMMs) {t0 t1: T} (hdif: t0 ≠ t1) (r0 r1: ℝ>0)
  (t0' t1': T) (hinit: amms.init t0' t1') (difp: diffmint t0 t1 t0' t1'):
  (amms.initialize hdif r0 r1).r1 t0' t1' (by simp[difp, hinit]) = amms.r1 t0' t1' hinit := by
  rw [r1_reorder _ t0' t1' (by simp[difp, hinit])]
  rw [r1_reorder amms t0' t1' hinit]
  simp [hinit.swap, hdif.symm, (diffmint.iff_swap_inner_right t0 t1 t0' t1').mp difp]

@[simp] theorem AMMs.init_of_add_r0
  (amms: AMMs) (t0 t1 t0' t1': T) (h: amms.init t0 t1) (x: ℝ>0):
  (amms.add_r0 t0 t1 h x).init t0' t1'
  ↔
  amms.init t0' t1'
  := by
  rcases Decidable.em (diffmint t0 t1 t0' t1') with a|a
  . simp [add_r0, a]
  . rw [not_diffmint_iff_samemint t0 t1 t0' t1' h.dif] at a
    simp [add_r0, a]; exact h.samepair a

@[simp] theorem AMMs.init_of_add_r1
  (amms: AMMs) (t0 t1 t0' t1': T) (h: amms.init t0 t1) (x: ℝ>0):
  (amms.add_r1 t0 t1 h x).init t0' t1'
  ↔
  amms.init t0' t1'
  := by
  rcases Decidable.em (diffmint t0 t1 t0' t1') with a|a
  . simp [add_r1, a]
  . rw [not_diffmint_iff_samemint t0 t1 t0' t1' h.dif] at a
    simp [add_r1, a]; exact h.samepair a

@[simp] theorem AMMs.init_of_sub_r0
  (amms: AMMs) (t0 t1 t0' t1': T) (h: amms.init t0 t1) (x: ℝ>0) (h': x < amms.r0 t0 t1 h):
  (amms.sub_r0 t0 t1 h x h').init t0' t1'
  ↔
  amms.init t0' t1'
  := by
  rcases Decidable.em (diffmint t0 t1 t0' t1') with a|a
  . simp [sub_r0, a]
  . rw [not_diffmint_iff_samemint t0 t1 t0' t1' h.dif] at a
    simp [sub_r0, a]; exact h.samepair a

@[simp] theorem AMMs.init_of_sub_r1
  (amms: AMMs) (t0 t1 t0' t1': T) (h: amms.init t0 t1) (x: ℝ>0) (h': x < amms.r1 t0 t1 h):
  (amms.sub_r1 t0 t1 h x h').init t0' t1'
  ↔
  amms.init t0' t1'
  := by
  rcases Decidable.em (diffmint t0 t1 t0' t1') with a|a
  . simp [sub_r1, a]
  . rw [not_diffmint_iff_samemint t0 t1 t0' t1' h.dif] at a
    simp [sub_r1, a]; exact h.samepair a

@[simp] theorem AMMs.r0_of_add_r0
  (amms: AMMs) (t0 t1: T) (x: ℝ>0)
  (h: amms.init t0 t1)
  :
  (amms.add_r0 t0 t1 h x).r0 t0 t1 (by simp [h])
  =
  x + amms.r0 t0 t1 h
  := by rw [add_comm]; simp [add_r0]

@[simp] theorem AMMs.r0_of_add_r0_diff
  (amms: AMMs) (t0 t1: T) (x: ℝ>0)
  (h: amms.init t0 t1)
  (t0' t1': T) (h': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1')
  :
  (amms.add_r0 t0 t1 h x).r0 t0' t1' (by simp [h'])
  =
  amms.r0 t0' t1' h'
  := by simp [add_r0, hdiff, h']

@[simp] theorem AMMs.r0_of_add_r1
  (amms: AMMs) (t0 t1: T) (h: amms.init t0 t1) (x: ℝ>0):
  (amms.add_r1 t0 t1 h x).r0 t0 t1 (by simp[h])
  =
  amms.r0 t0 t1 h
  := by simp [add_r1]

@[simp] theorem AMMs.r0_of_add_r1_diff
  (amms: AMMs) (t0 t1: T) (x: ℝ>0)
  (h: amms.init t0 t1)
  (t0' t1': T) (h': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1')
  :
  (amms.add_r1 t0 t1 h x).r0 t0' t1' (by simp [h'])
  =
  amms.r0 t0' t1' h'
  := by
  simp [add_r1, hdiff, h']

@[simp] theorem AMMs.r1_of_add_r1
  (amms: AMMs) (t0 t1: T) (h: amms.init t0 t1) (x: ℝ>0):
  (amms.add_r1 t0 t1 h x).r1 t0 t1 (by simp[h])
  =
  x + amms.r1 t0 t1 h
  := by rw [add_comm]; simp [add_r1]

@[simp] theorem AMMs.r1_of_add_r1_diff
  (amms: AMMs) (t0 t1: T) (x: ℝ>0)
  (h: amms.init t0 t1)
  (t0' t1': T) (h': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1')
  :
  (amms.add_r1 t0 t1 h x).r1 t0' t1' (by simp [h'])
  =
  amms.r1 t0' t1' h'
  := by simp [add_r1, hdiff, h']

@[simp] theorem AMMs.r1_of_add_r0
  (amms: AMMs) (t0 t1: T) (h: amms.init t0 t1) (x: ℝ>0):
  (amms.add_r0 t0 t1 h x).r1 t0 t1 (by simp[h])
  =
  amms.r1 t0 t1 h
  := by simp [add_r0]

@[simp] theorem AMMs.r1_of_add_r0_diff
  (amms: AMMs) (t0 t1: T) (x: ℝ>0)
  (h: amms.init t0 t1)
  (t0' t1': T) (h': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1')
  :
  (amms.add_r0 t0 t1 h x).r1 t0' t1' (by simp [h'])
  =
  amms.r1 t0' t1' h'
  := by simp [add_r0, hdiff, h']

@[simp] theorem AMMs.r0_of_sub_r0
  (amms: AMMs) (t0 t1: T) (h: amms.init t0 t1) (x: ℝ>0) (h': x < amms.r0 t0 t1 h):
  (amms.sub_r0 t0 t1 h x h').r0 t0 t1 (by simp[h])
  =
  (amms.r0 t0 t1 h).sub x h'
  := by simp [sub_r0]

@[simp] theorem AMMs.r0_of_sub_r1
  (amms: AMMs) (t0 t1: T) (h: amms.init t0 t1) (x: ℝ>0) (h': x < amms.r1 t0 t1 h):
  (amms.sub_r1 t0 t1 h x h').r0 t0 t1 (by simp[h])
  =
  amms.r0 t0 t1 h
  := by simp [sub_r1]

@[simp] theorem AMMs.r1_of_sub_r1
  (amms: AMMs) (t0 t1: T) (h: amms.init t0 t1) (x: ℝ>0) (h': x < amms.r1 t0 t1 h):
  (amms.sub_r1 t0 t1 h x h').r1 t0 t1 (by simp[h])
  =
  (amms.r1 t0 t1 h).sub x h'
  := by simp [sub_r1]

@[simp] theorem AMMs.r1_of_sub_r0
  (amms: AMMs) (t0 t1: T) (h: amms.init t0 t1) (x: ℝ>0) (h': x < amms.r0 t0 t1 h):
  (amms.sub_r0 t0 t1 h x h').r1 t0 t1 (by simp[h])
  =
  amms.r1 t0 t1 h
  := by simp [sub_r0]

@[simp] theorem AMMs.r0_of_sub_r0_diff
  (amms: AMMs) (t0 t1: T) (h: amms.init t0 t1) (x: ℝ>0) (h': x < amms.r0 t0 t1 h)
  (t0' t1': T) (h'': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1'):
  (amms.sub_r0 t0 t1 h x h').r0 t0' t1' (by simp[h''])
  =
  amms.r0 t0' t1' h''
  := by simp [sub_r0, hdiff, h'']

@[simp] theorem AMMs.r0_of_sub_r1_diff
  (amms: AMMs) (t0 t1: T) (h: amms.init t0 t1) (x: ℝ>0) (h': x < amms.r1 t0 t1 h)
  (t0' t1': T) (h'': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1'):
  (amms.sub_r1 t0 t1 h x h').r0 t0' t1' (by simp[h''])
  =
  amms.r0 t0' t1' h''
  := by simp [sub_r1, hdiff, h'']

@[simp] theorem AMMs.r1_of_sub_r1_diff
  (amms: AMMs) (t0 t1: T) (h: amms.init t0 t1) (x: ℝ>0) (h': x < amms.r1 t0 t1 h)
  (t0' t1': T) (h'': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1'):
  (amms.sub_r1 t0 t1 h x h').r1 t0' t1' (by simp[h''])
  =
  amms.r1 t0' t1' h''
  := by simp [sub_r1, hdiff, h'']

@[simp] theorem AMMs.r1_of_sub_r0_diff
  (amms: AMMs) (t0 t1: T) (h: amms.init t0 t1) (x: ℝ>0) (h': x < amms.r0 t0 t1 h)
  (t0' t1': T) (h'': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1'):
  (amms.sub_r0 t0 t1 h x h').r1 t0' t1' (by simp[h''])
  =
  amms.r1 t0' t1' h''
  := by simp [sub_r0, hdiff, h'']
