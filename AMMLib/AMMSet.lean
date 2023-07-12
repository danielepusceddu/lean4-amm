import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Sym.Sym2
import HelpersLib.NNReal
import HelpersLib.Prod
import HelpersLib.PReal.Basic
import HelpersLib.Finsupp2
import AMMLib.Tokens
import AMMLib.Wallets.AtomicWall

structure Sₐ where 
  f: T →₀ W₀
  h2: ∀ (t: T), f t t = 0
  h3: ∀ (t0 t1: T), f t0 t1 ≠ 0 ↔ f t1 t0 ≠ 0

def Sₐ.empty: Sₐ :=
⟨ 
  0,
  by intro _; simp,
  by intro t0 t1; apply Iff.intro;
     . simp
     . simp
⟩

def Sₐ.init (amms: Sₐ) (t0 t1: T): Prop :=
  amms.f t0 t1 ≠ 0

theorem Sₐ.empty_uninit (t0 t1: T):
  ¬ Sₐ.empty.init t0 t1 := by
  simp [init, empty]

theorem Sₐ.same_uninit (amms: Sₐ)(t: T):
  ¬amms.init t t := by unfold init; simp [amms.h2]

def Sₐ.init.swap {amms: Sₐ} {t0 t1: T} (h: amms.init t0 t1):
  amms.init t1 t0 := by
  unfold init at *
  exact (amms.h3 t0 t1).mp h

def Sₐ.init_swap_iff (amms: Sₐ) (t0 t1: T):
 amms.init t0 t1 ↔ amms.init t1 t0 := by
  unfold init
  exact amms.h3 t0 t1

def Sₐ.init.dif {amms: Sₐ} {t0 t1: T} (h: amms.init t0 t1):
  t0 ≠ t1 := by
  unfold init at h
  rcases (Decidable.em (t0=t1)) with eq|neq
  . rw [eq] at h
    have h' := amms.h2 t1
    contradiction
  . exact Ne.intro neq

theorem Sₐ.init.samepair {amms: Sₐ} {t0 t1: T} (h: amms.init t0 t1) {t0' t1': T} (same: samemint t0 t1 t0' t1'):
  amms.init t0' t1' := by 
  rcases same with ⟨a,b⟩|⟨a,b⟩
  . simp [← a, ← b, h]
  . simp [← a, ← b, h.swap]

noncomputable def Sₐ.initialize 
  (amms: Sₐ) {t0 t1: T} (hdif: t0 ≠ t1) (r0 r1: ℝ+): Sₐ :=
  
  ⟨
    (amms.f.update t0 ((amms.f t0).update t1 r0)).update t1 ((amms.f t1).update t0 r1),

    by intro t
       rcases Decidable.em (t=t0), Decidable.em (t=t1) with ⟨eq0|neq0, eq1|neq1⟩ 
       . rw [eq0] at eq1; contradiction
       . simp [eq0, hdif, amms.h2 t0]
       . simp [eq1, hdif, amms.h2 t1, hdif.symm]
       . simp [neq0, neq1, amms.h2 t],


    by intro t0' t1'
       rcases Decidable.em (t0'=t0), Decidable.em (t0'=t1), Decidable.em (t1'=t0), Decidable.em (t1'=t1) with ⟨a|a, b|b, c|c, d|d⟩ 
       <;>
       simp [a, b, c, d, hdif, r0.toNNReal_ne_zero, r1.toNNReal_ne_zero, amms.h3]
  ⟩

@[simp] theorem Sₐ.initialize_init_diffpair
  (amms: Sₐ) {t0 t1: T} (hdif: t0 ≠ t1) (r0 r1: ℝ+)
  (t0' t1': T) (h: diffmint t0 t1 t0' t1'):
  (amms.initialize hdif r0 r1).init t0' t1' ↔ amms.init t0' t1' := by 

    rcases Decidable.em (t0'=t1') with triv|hdif'
    . simp [triv, same_uninit]
    . unfold init Sₐ.initialize
      rcases h with ⟨a,b⟩|⟨a,b⟩
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

@[simp] theorem Sₐ.initialize_init_not_diffpair
  (amms: Sₐ) {t0 t1: T} (hdif: t0 ≠ t1) (r0 r1: ℝ+)
  (t0' t1': T) (h: samemint t0 t1 t0' t1'):
  (amms.initialize hdif r0 r1).init t0' t1' := by

  unfold init
  rcases h with ⟨a,b⟩|⟨a,b⟩
  . simp [Sₐ.initialize, ← a, ← b, hdif, r0.toNNReal_ne_zero]
  . simp [Sₐ.initialize, ← a, ← b, hdif, r1.toNNReal_ne_zero]

@[simp] theorem Sₐ.initialize_init_self
  (amms: Sₐ) {t0 t1: T} (hdif: t0 ≠ t1) (r0 r1: ℝ+):
  (amms.initialize hdif r0 r1).init t0 t1 := 
  initialize_init_not_diffpair amms hdif r0 r1 t0 t1 (self_samemint t0 t1)

def Sₐ.r0 (amms: Sₐ) (t0 t1: T) 
  (h: amms.init t0 t1): ℝ+ := 
  
  ⟨amms.f t0 t1, by 
    unfold init at h
    exact NNReal.neq_zero_imp_gt h
  ⟩

def Sₐ.r1 (amms: Sₐ) (t0 t1: T) 
  (h: amms.init t0 t1): ℝ+ := 
  
  ⟨amms.f t1 t0, by 
    unfold init at h
    exact NNReal.neq_zero_imp_gt ((amms.h3 t0 t1).mp h)
  ⟩

theorem Sₐ.r0_reorder
  (amms: Sₐ) (t1 t0: T) (h: amms.init t1 t0):
  amms.r0 t1 t0 h = amms.r1 t0 t1 h.swap := by
  simp [r0, r1]

theorem Sₐ.r1_reorder
  (amms: Sₐ) (t1 t0: T) (h: amms.init t1 t0):
  amms.r1 t1 t0 h = amms.r0 t0 t1 h.swap := by
  simp [r0, r1]

noncomputable instance decidableInit (amms: Sₐ) (t0 t1: T): Decidable (amms.init t0 t1) 
  := by unfold Sₐ.init
        infer_instance

noncomputable def Sₐ.add_r0 (amms: Sₐ) (t0 t1: T) (h: amms.init t0 t1) (x: PReal): Sₐ := 
  amms.initialize h.dif ((amms.r0 t0 t1 h) + x) (amms.r1 t0 t1 h)

noncomputable def Sₐ.sub_r0 (amms: Sₐ) (t0 t1: T) (h: amms.init t0 t1) (x: PReal) (nodrain: x < amms.r0 t0 t1 h): Sₐ := 
  amms.initialize h.dif ((amms.r0 t0 t1 h).sub x nodrain) (amms.r1 t0 t1 h)

noncomputable def Sₐ.add_r1 (amms: Sₐ) (t0 t1: T) (h: amms.init t0 t1) (x: PReal): Sₐ := 
  amms.initialize h.dif (amms.r0 t0 t1 h) ((amms.r1 t0 t1 h) + x)

noncomputable def Sₐ.sub_r1 (amms: Sₐ) (t0 t1: T) (h: amms.init t0 t1) (x: PReal) (nodrain: x < amms.r1 t0 t1 h): Sₐ := 
  amms.initialize h.dif (amms.r0 t0 t1 h) ((amms.r1 t0 t1 h).sub x nodrain)

@[simp] theorem Sₐ.r0_of_initialize
  (amms: Sₐ) {t0 t1: T} (hdif: t0 ≠ t1) (r0 r1: ℝ+):
  (amms.initialize hdif r0 r1).r0 t0 t1 (by simp) = r0 := by 
  simp [Sₐ.r0, Sₐ.initialize, hdif]

@[simp] theorem Sₐ.r1_of_initialize
  (amms: Sₐ) {t0 t1: T} (hdif: t0 ≠ t1) (r0 r1: ℝ+):
  (amms.initialize hdif r0 r1).r1 t0 t1 (by simp) = r1 := by 
  simp [Sₐ.r1, Sₐ.initialize, hdif]

@[simp] theorem Sₐ.r0_of_initialize_diffpair
  (amms: Sₐ) {t0 t1: T} (hdif: t0 ≠ t1) (r0 r1: ℝ+)
  (t0' t1': T) (hinit: amms.init t0' t1') (difp: diffmint t0 t1 t0' t1'):
  (amms.initialize hdif r0 r1).r0 t0' t1' (by simp[difp, hinit]) = amms.r0 t0' t1' hinit := by 
  rcases difp with ⟨a,b⟩|⟨a,b⟩
  . rcases Decidable.em (t1=t1') with c|c
    . simp [Sₐ.r0, Sₐ.initialize, a.symm, c, hinit.dif]
    . rcases Decidable.em (t0'=t1) with d|d
      . simp [Sₐ.r0, Sₐ.initialize, a.symm, b.symm, c, hinit.dif, d]
      . simp [Sₐ.r0, Sₐ.initialize, a.symm, c, hinit.dif, d]
  . rcases Decidable.em (t0=t1') with c|c
    . simp [Sₐ.r0, Sₐ.initialize, a.symm, c, hinit.dif]
    . rcases Decidable.em (t0'=t0) with d|d
      . simp [Sₐ.r0, Sₐ.initialize, b.symm, d, hdif]
      . simp [Sₐ.r0, Sₐ.initialize, a.symm, c, hinit.dif, d]

@[simp] theorem Sₐ.r1_of_initialize_diffpair
  (amms: Sₐ) {t0 t1: T} (hdif: t0 ≠ t1) (r0 r1: ℝ+)
  (t0' t1': T) (hinit: amms.init t0' t1') (difp: diffmint t0 t1 t0' t1'):
  (amms.initialize hdif r0 r1).r1 t0' t1' (by simp[difp, hinit]) = amms.r1 t0' t1' hinit := by 
  rw [r1_reorder _ t0' t1' (by simp[difp, hinit])]
  rw [r1_reorder amms t0' t1' hinit]
  simp [hinit.swap, hdif.symm, (diffmint.iff_swap_inner_right t0 t1 t0' t1').mp difp]

@[simp] theorem Sₐ.init_of_add_r0
  (amms: Sₐ) (t0 t1 t0' t1': T) (h: amms.init t0 t1) (x: PReal):
  (amms.add_r0 t0 t1 h x).init t0' t1'
  ↔
  amms.init t0' t1'
  := by 
  rcases Decidable.em (diffmint t0 t1 t0' t1') with a|a
  . simp [add_r0, a]
  . rw [not_diffmint_iff_samemint t0 t1 t0' t1' h.dif] at a
    simp [add_r0, a]; exact h.samepair a

@[simp] theorem Sₐ.init_of_add_r1
  (amms: Sₐ) (t0 t1 t0' t1': T) (h: amms.init t0 t1) (x: PReal):
  (amms.add_r1 t0 t1 h x).init t0' t1'
  ↔
  amms.init t0' t1'
  := by
  rcases Decidable.em (diffmint t0 t1 t0' t1') with a|a
  . simp [add_r1, a]
  . rw [not_diffmint_iff_samemint t0 t1 t0' t1' h.dif] at a
    simp [add_r1, a]; exact h.samepair a

@[simp] theorem Sₐ.init_of_sub_r0
  (amms: Sₐ) (t0 t1 t0' t1': T) (h: amms.init t0 t1) (x: PReal) (h': x < amms.r0 t0 t1 h):
  (amms.sub_r0 t0 t1 h x h').init t0' t1'
  ↔
  amms.init t0' t1'
  := by
  rcases Decidable.em (diffmint t0 t1 t0' t1') with a|a
  . simp [sub_r0, a]
  . rw [not_diffmint_iff_samemint t0 t1 t0' t1' h.dif] at a
    simp [sub_r0, a]; exact h.samepair a

@[simp] theorem Sₐ.init_of_sub_r1
  (amms: Sₐ) (t0 t1 t0' t1': T) (h: amms.init t0 t1) (x: PReal) (h': x < amms.r1 t0 t1 h):
  (amms.sub_r1 t0 t1 h x h').init t0' t1'
  ↔
  amms.init t0' t1'
  := by
  rcases Decidable.em (diffmint t0 t1 t0' t1') with a|a
  . simp [sub_r1, a]
  . rw [not_diffmint_iff_samemint t0 t1 t0' t1' h.dif] at a
    simp [sub_r1, a]; exact h.samepair a

@[simp] theorem Sₐ.r0_of_add_r0
  (amms: Sₐ) (t0 t1: T) (x: PReal)
  (h: amms.init t0 t1)
  :
  (amms.add_r0 t0 t1 h x).r0 t0 t1 (by simp [h])
  =
  x + amms.r0 t0 t1 h
  := by rw [add_comm]; simp [add_r0]

@[simp] theorem Sₐ.r0_of_add_r0_diff
  (amms: Sₐ) (t0 t1: T) (x: PReal)
  (h: amms.init t0 t1) 
  (t0' t1': T) (h': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1')
  :
  (amms.add_r0 t0 t1 h x).r0 t0' t1' (by simp [h'])
  =
  amms.r0 t0' t1' h'
  := by simp [add_r0, hdiff, h']

@[simp] theorem Sₐ.r0_of_add_r1
  (amms: Sₐ) (t0 t1: T) (h: amms.init t0 t1) (x: PReal):
  (amms.add_r1 t0 t1 h x).r0 t0 t1 (by simp[h])
  =
  amms.r0 t0 t1 h
  := by simp [add_r1]

@[simp] theorem Sₐ.r0_of_add_r1_diff
  (amms: Sₐ) (t0 t1: T) (x: PReal)
  (h: amms.init t0 t1) 
  (t0' t1': T) (h': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1')
  :
  (amms.add_r1 t0 t1 h x).r0 t0' t1' (by simp [h'])
  =
  amms.r0 t0' t1' h'
  := by 
  simp [add_r1, hdiff, h']

@[simp] theorem Sₐ.r1_of_add_r1
  (amms: Sₐ) (t0 t1: T) (h: amms.init t0 t1) (x: ℝ+):
  (amms.add_r1 t0 t1 h x).r1 t0 t1 (by simp[h])
  =
  x + amms.r1 t0 t1 h
  := by rw [add_comm]; simp [add_r1]

@[simp] theorem Sₐ.r1_of_add_r1_diff
  (amms: Sₐ) (t0 t1: T) (x: PReal)
  (h: amms.init t0 t1) 
  (t0' t1': T) (h': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1')
  :
  (amms.add_r1 t0 t1 h x).r1 t0' t1' (by simp [h'])
  =
  amms.r1 t0' t1' h'
  := by simp [add_r1, hdiff, h']

@[simp] theorem Sₐ.r1_of_add_r0
  (amms: Sₐ) (t0 t1: T) (h: amms.init t0 t1) (x: ℝ+):
  (amms.add_r0 t0 t1 h x).r1 t0 t1 (by simp[h])
  =
  amms.r1 t0 t1 h
  := by simp [add_r0]

@[simp] theorem Sₐ.r1_of_add_r0_diff
  (amms: Sₐ) (t0 t1: T) (x: PReal)
  (h: amms.init t0 t1) 
  (t0' t1': T) (h': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1')
  :
  (amms.add_r0 t0 t1 h x).r1 t0' t1' (by simp [h'])
  =
  amms.r1 t0' t1' h'
  := by simp [add_r0, hdiff, h']

@[simp] theorem Sₐ.r0_of_sub_r0
  (amms: Sₐ) (t0 t1: T) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r0 t0 t1 h):
  (amms.sub_r0 t0 t1 h x h').r0 t0 t1 (by simp[h])
  =
  (amms.r0 t0 t1 h).sub x h'
  := by simp [sub_r0]

@[simp] theorem Sₐ.r0_of_sub_r1
  (amms: Sₐ) (t0 t1: T) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r1 t0 t1 h):
  (amms.sub_r1 t0 t1 h x h').r0 t0 t1 (by simp[h])
  =
  amms.r0 t0 t1 h
  := by simp [sub_r1]

@[simp] theorem Sₐ.r1_of_sub_r1
  (amms: Sₐ) (t0 t1: T) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r1 t0 t1 h):
  (amms.sub_r1 t0 t1 h x h').r1 t0 t1 (by simp[h])
  =
  (amms.r1 t0 t1 h).sub x h'
  := by simp [sub_r1]

@[simp] theorem Sₐ.r1_of_sub_r0
  (amms: Sₐ) (t0 t1: T) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r0 t0 t1 h):
  (amms.sub_r0 t0 t1 h x h').r1 t0 t1 (by simp[h])
  =
  amms.r1 t0 t1 h
  := by simp [sub_r0]

@[simp] theorem Sₐ.r0_of_sub_r0_diff
  (amms: Sₐ) (t0 t1: T) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r0 t0 t1 h)
  (t0' t1': T) (h'': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1'):
  (amms.sub_r0 t0 t1 h x h').r0 t0' t1' (by simp[h''])
  =
  amms.r0 t0' t1' h''
  := by simp [sub_r0, hdiff, h'']

@[simp] theorem Sₐ.r0_of_sub_r1_diff
  (amms: Sₐ) (t0 t1: T) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r1 t0 t1 h)
  (t0' t1': T) (h'': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1'):
  (amms.sub_r1 t0 t1 h x h').r0 t0' t1' (by simp[h''])
  =
  amms.r0 t0' t1' h''
  := by simp [sub_r1, hdiff, h'']

@[simp] theorem Sₐ.r1_of_sub_r1_diff
  (amms: Sₐ) (t0 t1: T) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r1 t0 t1 h)
  (t0' t1': T) (h'': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1'):
  (amms.sub_r1 t0 t1 h x h').r1 t0' t1' (by simp[h''])
  =
  amms.r1 t0' t1' h''
  := by simp [sub_r1, hdiff, h'']

@[simp] theorem Sₐ.r1_of_sub_r0_diff
  (amms: Sₐ) (t0 t1: T) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r0 t0 t1 h)
  (t0' t1': T) (h'': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1'):
  (amms.sub_r0 t0 t1 h x h').r1 t0' t1' (by simp[h''])
  =
  amms.r1 t0' t1' h''
  := by simp [sub_r0, hdiff, h'']
