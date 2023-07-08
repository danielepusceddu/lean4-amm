import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Sym.Sym2
import HelpersLib.NNReal
import HelpersLib.Prod
import HelpersLib.PReal.Basic
import HelpersLib.Finsupp2
import AMMLib.Tokens
import AMMLib.Wallets.AtomicWall

structure 𝕊ₐ where 
  f: 𝕋 →₀ 𝕎₀
  h2: ∀ (t: 𝕋), f t t = 0
  h3: ∀ (t0 t1: 𝕋), f t0 t1 ≠ 0 ↔ f t1 t0 ≠ 0

def 𝕊ₐ.empty: 𝕊ₐ :=
⟨ 
  0,
  by intro _; simp,
  by intro t0 t1; apply Iff.intro;
     . simp
     . simp
⟩

def 𝕊ₐ.init (amms: 𝕊ₐ) (t0 t1: 𝕋): Prop :=
  amms.f t0 t1 ≠ 0

theorem 𝕊ₐ.empty_uninit (t0 t1: 𝕋):
  ¬ 𝕊ₐ.empty.init t0 t1 := by
  simp [init, empty]

theorem 𝕊ₐ.same_uninit (amms: 𝕊ₐ)(t: 𝕋):
  ¬amms.init t t := by unfold init; simp [amms.h2]

def 𝕊ₐ.init.swap {amms: 𝕊ₐ} {t0 t1: 𝕋} (h: amms.init t0 t1):
  amms.init t1 t0 := by
  unfold init at *
  exact (amms.h3 t0 t1).mp h

def 𝕊ₐ.init_swap_iff (amms: 𝕊ₐ) (t0 t1: 𝕋):
 amms.init t0 t1 ↔ amms.init t1 t0 := by
  unfold init
  exact amms.h3 t0 t1

def 𝕊ₐ.init.dif {amms: 𝕊ₐ} {t0 t1: 𝕋} (h: amms.init t0 t1):
  t0 ≠ t1 := by
  unfold init at h
  rcases (Decidable.em (t0=t1)) with eq|neq
  . rw [eq] at h
    have h' := amms.h2 t1
    contradiction
  . exact Ne.intro neq

theorem 𝕊ₐ.init.samepair {amms: 𝕊ₐ} {t0 t1: 𝕋} (h: amms.init t0 t1) {t0' t1': 𝕋} (same: samemint t0 t1 t0' t1'):
  amms.init t0' t1' := by 
  rcases same with ⟨a,b⟩|⟨a,b⟩
  . simp [← a, ← b, h]
  . simp [← a, ← b, h.swap]

noncomputable def 𝕊ₐ.initialize 
  (amms: 𝕊ₐ) {t0 t1: 𝕋} (hdif: t0 ≠ t1) (r0 r1: ℝ+): 𝕊ₐ :=
  
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

@[simp] theorem 𝕊ₐ.initialize_init_diffpair
  (amms: 𝕊ₐ) {t0 t1: 𝕋} (hdif: t0 ≠ t1) (r0 r1: ℝ+)
  (t0' t1': 𝕋) (h: diffmint t0 t1 t0' t1'):
  (amms.initialize hdif r0 r1).init t0' t1' ↔ amms.init t0' t1' := by 

    rcases Decidable.em (t0'=t1') with triv|hdif'
    . simp [triv, same_uninit]
    . unfold init 𝕊ₐ.initialize
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

@[simp] theorem 𝕊ₐ.initialize_init_not_diffpair
  (amms: 𝕊ₐ) {t0 t1: 𝕋} (hdif: t0 ≠ t1) (r0 r1: ℝ+)
  (t0' t1': 𝕋) (h: samemint t0 t1 t0' t1'):
  (amms.initialize hdif r0 r1).init t0' t1' := by

  unfold init
  rcases h with ⟨a,b⟩|⟨a,b⟩
  . simp [𝕊ₐ.initialize, ← a, ← b, hdif, r0.toNNReal_ne_zero]
  . simp [𝕊ₐ.initialize, ← a, ← b, hdif, r1.toNNReal_ne_zero]

@[simp] theorem 𝕊ₐ.initialize_init_self
  (amms: 𝕊ₐ) {t0 t1: 𝕋} (hdif: t0 ≠ t1) (r0 r1: ℝ+):
  (amms.initialize hdif r0 r1).init t0 t1 := 
  initialize_init_not_diffpair amms hdif r0 r1 t0 t1 (self_samemint t0 t1)

def 𝕊ₐ.r0 (amms: 𝕊ₐ) (t0 t1: 𝕋) 
  (h: amms.init t0 t1): ℝ+ := 
  
  ⟨amms.f t0 t1, by 
    unfold init at h
    exact NNReal.neq_zero_imp_gt h
  ⟩

def 𝕊ₐ.r1 (amms: 𝕊ₐ) (t0 t1: 𝕋) 
  (h: amms.init t0 t1): ℝ+ := 
  
  ⟨amms.f t1 t0, by 
    unfold init at h
    exact NNReal.neq_zero_imp_gt ((amms.h3 t0 t1).mp h)
  ⟩

theorem 𝕊ₐ.r0_reorder
  (amms: 𝕊ₐ) (t1 t0: 𝕋) (h: amms.init t1 t0):
  amms.r0 t1 t0 h = amms.r1 t0 t1 h.swap := by
  simp [r0, r1]

theorem 𝕊ₐ.r1_reorder
  (amms: 𝕊ₐ) (t1 t0: 𝕋) (h: amms.init t1 t0):
  amms.r1 t1 t0 h = amms.r0 t0 t1 h.swap := by
  simp [r0, r1]

noncomputable instance decidableInit (amms: 𝕊ₐ) (t0 t1: 𝕋): Decidable (amms.init t0 t1) 
  := by unfold 𝕊ₐ.init
        infer_instance

noncomputable def 𝕊ₐ.add_r0 (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: PReal): 𝕊ₐ := 
  amms.initialize h.dif ((amms.r0 t0 t1 h) + x) (amms.r1 t0 t1 h)

noncomputable def 𝕊ₐ.sub_r0 (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: PReal) (nodrain: x < amms.r0 t0 t1 h): 𝕊ₐ := 
  amms.initialize h.dif ((amms.r0 t0 t1 h).sub x nodrain) (amms.r1 t0 t1 h)

noncomputable def 𝕊ₐ.add_r1 (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: PReal): 𝕊ₐ := 
  amms.initialize h.dif (amms.r0 t0 t1 h) ((amms.r1 t0 t1 h) + x)

noncomputable def 𝕊ₐ.sub_r1 (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: PReal) (nodrain: x < amms.r1 t0 t1 h): 𝕊ₐ := 
  amms.initialize h.dif (amms.r0 t0 t1 h) ((amms.r1 t0 t1 h).sub x nodrain)

@[simp] theorem 𝕊ₐ.r0_of_initialize
  (amms: 𝕊ₐ) {t0 t1: 𝕋} (hdif: t0 ≠ t1) (r0 r1: ℝ+):
  (amms.initialize hdif r0 r1).r0 t0 t1 (by simp) = r0 := by 
  simp [𝕊ₐ.r0, 𝕊ₐ.initialize, hdif]

@[simp] theorem 𝕊ₐ.r1_of_initialize
  (amms: 𝕊ₐ) {t0 t1: 𝕋} (hdif: t0 ≠ t1) (r0 r1: ℝ+):
  (amms.initialize hdif r0 r1).r1 t0 t1 (by simp) = r1 := by 
  simp [𝕊ₐ.r1, 𝕊ₐ.initialize, hdif]

@[simp] theorem 𝕊ₐ.r0_of_initialize_diffpair
  (amms: 𝕊ₐ) {t0 t1: 𝕋} (hdif: t0 ≠ t1) (r0 r1: ℝ+)
  (t0' t1': 𝕋) (hinit: amms.init t0' t1') (difp: diffmint t0 t1 t0' t1'):
  (amms.initialize hdif r0 r1).r0 t0' t1' (by simp[difp, hinit]) = amms.r0 t0' t1' hinit := by 
  rcases difp with ⟨a,b⟩|⟨a,b⟩
  . rcases Decidable.em (t1=t1') with c|c
    . simp [𝕊ₐ.r0, 𝕊ₐ.initialize, a.symm, c, hinit.dif]
    . rcases Decidable.em (t0'=t1) with d|d
      . simp [𝕊ₐ.r0, 𝕊ₐ.initialize, a.symm, b.symm, c, hinit.dif, d]
      . simp [𝕊ₐ.r0, 𝕊ₐ.initialize, a.symm, c, hinit.dif, d]
  . rcases Decidable.em (t0=t1') with c|c
    . simp [𝕊ₐ.r0, 𝕊ₐ.initialize, a.symm, c, hinit.dif]
    . rcases Decidable.em (t0'=t0) with d|d
      . simp [𝕊ₐ.r0, 𝕊ₐ.initialize, b.symm, d, hdif]
      . simp [𝕊ₐ.r0, 𝕊ₐ.initialize, a.symm, c, hinit.dif, d]

@[simp] theorem 𝕊ₐ.r1_of_initialize_diffpair
  (amms: 𝕊ₐ) {t0 t1: 𝕋} (hdif: t0 ≠ t1) (r0 r1: ℝ+)
  (t0' t1': 𝕋) (hinit: amms.init t0' t1') (difp: diffmint t0 t1 t0' t1'):
  (amms.initialize hdif r0 r1).r1 t0' t1' (by simp[difp, hinit]) = amms.r1 t0' t1' hinit := by 
  rw [r1_reorder _ t0' t1' (by simp[difp, hinit])]
  rw [r1_reorder amms t0' t1' hinit]
  simp [hinit.swap, hdif.symm, (diffmint.iff_swap_inner_right t0 t1 t0' t1').mp difp]

@[simp] theorem 𝕊ₐ.init_of_add_r0
  (amms: 𝕊ₐ) (t0 t1 t0' t1': 𝕋) (h: amms.init t0 t1) (x: PReal):
  (amms.add_r0 t0 t1 h x).init t0' t1'
  ↔
  amms.init t0' t1'
  := by 
  rcases Decidable.em (diffmint t0 t1 t0' t1') with a|a
  . simp [add_r0, a]
  . rw [not_diffmint_iff_samemint t0 t1 t0' t1' h.dif] at a
    simp [add_r0, a]; exact h.samepair a

@[simp] theorem 𝕊ₐ.init_of_add_r1
  (amms: 𝕊ₐ) (t0 t1 t0' t1': 𝕋) (h: amms.init t0 t1) (x: PReal):
  (amms.add_r1 t0 t1 h x).init t0' t1'
  ↔
  amms.init t0' t1'
  := by
  rcases Decidable.em (diffmint t0 t1 t0' t1') with a|a
  . simp [add_r1, a]
  . rw [not_diffmint_iff_samemint t0 t1 t0' t1' h.dif] at a
    simp [add_r1, a]; exact h.samepair a

@[simp] theorem 𝕊ₐ.init_of_sub_r0
  (amms: 𝕊ₐ) (t0 t1 t0' t1': 𝕋) (h: amms.init t0 t1) (x: PReal) (h': x < amms.r0 t0 t1 h):
  (amms.sub_r0 t0 t1 h x h').init t0' t1'
  ↔
  amms.init t0' t1'
  := by
  rcases Decidable.em (diffmint t0 t1 t0' t1') with a|a
  . simp [sub_r0, a]
  . rw [not_diffmint_iff_samemint t0 t1 t0' t1' h.dif] at a
    simp [sub_r0, a]; exact h.samepair a

@[simp] theorem 𝕊ₐ.init_of_sub_r1
  (amms: 𝕊ₐ) (t0 t1 t0' t1': 𝕋) (h: amms.init t0 t1) (x: PReal) (h': x < amms.r1 t0 t1 h):
  (amms.sub_r1 t0 t1 h x h').init t0' t1'
  ↔
  amms.init t0' t1'
  := by
  rcases Decidable.em (diffmint t0 t1 t0' t1') with a|a
  . simp [sub_r1, a]
  . rw [not_diffmint_iff_samemint t0 t1 t0' t1' h.dif] at a
    simp [sub_r1, a]; exact h.samepair a

@[simp] theorem 𝕊ₐ.r0_of_add_r0
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (x: PReal)
  (h: amms.init t0 t1)
  :
  (amms.add_r0 t0 t1 h x).r0 t0 t1 (by simp [h])
  =
  x + amms.r0 t0 t1 h
  := by rw [add_comm]; simp [add_r0]

@[simp] theorem 𝕊ₐ.r0_of_add_r0_diff
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (x: PReal)
  (h: amms.init t0 t1) 
  (t0' t1': 𝕋) (h': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1')
  :
  (amms.add_r0 t0 t1 h x).r0 t0' t1' (by simp [h'])
  =
  amms.r0 t0' t1' h'
  := by simp [add_r0, hdiff, h']

@[simp] theorem 𝕊ₐ.r0_of_add_r1
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: PReal):
  (amms.add_r1 t0 t1 h x).r0 t0 t1 (by simp[h])
  =
  amms.r0 t0 t1 h
  := by simp [add_r1]

@[simp] theorem 𝕊ₐ.r0_of_add_r1_diff
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (x: PReal)
  (h: amms.init t0 t1) 
  (t0' t1': 𝕋) (h': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1')
  :
  (amms.add_r1 t0 t1 h x).r0 t0' t1' (by simp [h'])
  =
  amms.r0 t0' t1' h'
  := by 
  simp [add_r1, hdiff, h']

@[simp] theorem 𝕊ₐ.r1_of_add_r1
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: ℝ+):
  (amms.add_r1 t0 t1 h x).r1 t0 t1 (by simp[h])
  =
  x + amms.r1 t0 t1 h
  := by rw [add_comm]; simp [add_r1]

@[simp] theorem 𝕊ₐ.r1_of_add_r1_diff
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (x: PReal)
  (h: amms.init t0 t1) 
  (t0' t1': 𝕋) (h': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1')
  :
  (amms.add_r1 t0 t1 h x).r1 t0' t1' (by simp [h'])
  =
  amms.r1 t0' t1' h'
  := by simp [add_r1, hdiff, h']

@[simp] theorem 𝕊ₐ.r1_of_add_r0
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: ℝ+):
  (amms.add_r0 t0 t1 h x).r1 t0 t1 (by simp[h])
  =
  amms.r1 t0 t1 h
  := by simp [add_r0]

@[simp] theorem 𝕊ₐ.r1_of_add_r0_diff
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (x: PReal)
  (h: amms.init t0 t1) 
  (t0' t1': 𝕋) (h': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1')
  :
  (amms.add_r0 t0 t1 h x).r1 t0' t1' (by simp [h'])
  =
  amms.r1 t0' t1' h'
  := by simp [add_r0, hdiff, h']

@[simp] theorem 𝕊ₐ.r0_of_sub_r0
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r0 t0 t1 h):
  (amms.sub_r0 t0 t1 h x h').r0 t0 t1 (by simp[h])
  =
  (amms.r0 t0 t1 h).sub x h'
  := by simp [sub_r0]

@[simp] theorem 𝕊ₐ.r0_of_sub_r1
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r1 t0 t1 h):
  (amms.sub_r1 t0 t1 h x h').r0 t0 t1 (by simp[h])
  =
  amms.r0 t0 t1 h
  := by simp [sub_r1]

@[simp] theorem 𝕊ₐ.r1_of_sub_r1
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r1 t0 t1 h):
  (amms.sub_r1 t0 t1 h x h').r1 t0 t1 (by simp[h])
  =
  (amms.r1 t0 t1 h).sub x h'
  := by simp [sub_r1]

@[simp] theorem 𝕊ₐ.r1_of_sub_r0
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r0 t0 t1 h):
  (amms.sub_r0 t0 t1 h x h').r1 t0 t1 (by simp[h])
  =
  amms.r1 t0 t1 h
  := by simp [sub_r0]

@[simp] theorem 𝕊ₐ.r0_of_sub_r0_diff
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r0 t0 t1 h)
  (t0' t1': 𝕋) (h'': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1'):
  (amms.sub_r0 t0 t1 h x h').r0 t0' t1' (by simp[h''])
  =
  amms.r0 t0' t1' h''
  := by simp [sub_r0, hdiff, h'']

@[simp] theorem 𝕊ₐ.r0_of_sub_r1_diff
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r1 t0 t1 h)
  (t0' t1': 𝕋) (h'': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1'):
  (amms.sub_r1 t0 t1 h x h').r0 t0' t1' (by simp[h''])
  =
  amms.r0 t0' t1' h''
  := by simp [sub_r1, hdiff, h'']

@[simp] theorem 𝕊ₐ.r1_of_sub_r1_diff
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r1 t0 t1 h)
  (t0' t1': 𝕋) (h'': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1'):
  (amms.sub_r1 t0 t1 h x h').r1 t0' t1' (by simp[h''])
  =
  amms.r1 t0' t1' h''
  := by simp [sub_r1, hdiff, h'']

@[simp] theorem 𝕊ₐ.r1_of_sub_r0_diff
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r0 t0 t1 h)
  (t0' t1': 𝕋) (h'': amms.init t0' t1')
  (hdiff: diffmint t0 t1 t0' t1'):
  (amms.sub_r0 t0 t1 h x h').r1 t0' t1' (by simp[h''])
  =
  amms.r1 t0' t1' h''
  := by simp [sub_r0, hdiff, h'']
