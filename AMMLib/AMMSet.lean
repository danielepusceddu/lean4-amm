import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Sym.Sym2
import HelpersLib.NNReal
import HelpersLib.Prod
import HelpersLib.PReal
import HelpersLib.Finsupp2
import AMMLib.Tokens

structure 𝕊ₐ where 
  f: 𝕋₀ →₀ 𝕋₀ →₀ (NNReal × NNReal)
  h1: ∀ (t0 t1: 𝕋₀), f t0 t1 = (f t1 t0).swap
  h2: ∀ (t: 𝕋₀), f t t = (0,0)
  h3: ∀ (t0 t1: 𝕋₀), (f t0 t1).fst ≠ 0 ↔ (f t0 t1).snd ≠ 0

def 𝕊ₐ.empty: 𝕊ₐ :=
⟨ 
  0,
  by intro _ _; simp,
  by intro t; simp; exact Prod.zero_eq_mk,
  by intro t0 t1; apply Iff.intro;
     . simp
     . simp
⟩

def 𝕊ₐ.init (amms: 𝕊ₐ) (t0 t1: 𝕋₀): Prop :=
  amms.f t0 t1 ≠ 0

theorem 𝕊ₐ.empty_uninit (t0 t1: 𝕋₀):
  ¬ 𝕊ₐ.empty.init t0 t1 := by
  simp [init, empty]

def 𝕊ₐ.init.swap {amms: 𝕊ₐ} {t0 t1: 𝕋₀} (h: amms.init t0 t1):
  amms.init t1 t0 := by sorry

def 𝕊ₐ.init.dif {amms: 𝕊ₐ} {t0 t1: 𝕋₀} (h: amms.init t0 t1):
  t0 ≠ t1 := by sorry

lemma 𝕊ₐ.up_h1' (amms: 𝕊ₐ) 
(t0' t1': 𝕋₀) (x: NNReal × NNReal) (hdif: t0' ≠ t1')
(t0 t1: 𝕋₀)
: ((amms.f.up t0' t1' x).up t1' t0' x.swap) t0 t1 = (((amms.f.up t0' t1' x).up t1' t0' x.swap) t1 t0).swap := by

  apply @Decidable.byCases (t1'=t0)
  . intro t1pt0
    simp [t1pt0]
    apply @Decidable.byCases (t0'=t0)
    . intro t0pt0
      simp [t0pt0, t1pt0] at hdif
    . intro nt0pt0
      apply @Decidable.byCases (t0'=t1)
      . intro t0pt1
        simp [t1pt0, t0pt1] at hdif
        simp [t1pt0, t0pt1, hdif]
      . intro nt0pt1
        simp [(Ne.intro nt0pt1).symm, (Ne.intro nt0pt0).symm]
        exact amms.h1 t0 t1
  
  . intro nt1pt0
    simp [(Ne.intro nt1pt0).symm, hdif.symm]
    apply @Decidable.byCases (t0'=t0)
    . intro t0pt0
      apply @Decidable.byCases (t1'=t1)
      . intro t1pt1
        simp only [t0pt0, t1pt1]
        simp [Finsupp.up_self]
      . intro nt1pt1
        rw [Finsupp.up_diff2 amms.f t0' t1' x t0 t1 (Ne.intro nt1pt1).symm]
        rw [Finsupp.up_diff _ t1' t0' x.swap t1 (Ne.intro nt1pt1).symm]
        simp [← t0pt0, hdif]
        exact amms.h1 t0' t1
    . intro nt0pt0
      simp [(Ne.intro nt0pt0).symm, (Ne.intro nt1pt0).symm]
      exact amms.h1 t0 t1

lemma 𝕊ₐ.up_h2' (amms: 𝕊ₐ) 
(t0 t1: 𝕋₀) (x: NNReal × NNReal) (hdif: t0 ≠ t1)
(t: 𝕋₀): ((amms.f.up t0 t1 x).up t1 t0 x.swap) t t = (0,0) := by

  apply @Decidable.byCases (t=t1)
  . intro tt1
    apply @Decidable.byCases (t=t0)
    . intro tt0
      rw [tt0] at tt1; contradiction
    . intro ntt0
      simp [(Ne.intro ntt0)]
      exact amms.h2 t
  . intro ntt1
    simp [(Ne.intro ntt1)]
    exact amms.h2 t

lemma 𝕊ₐ.up_h3' (amms: 𝕊ₐ) 
(t0' t1': 𝕋₀) (x: NNReal × NNReal) (hdif: t0' ≠ t1')
(h3: x.fst ≠ 0 ↔ x.snd ≠ 0) (t0 t1: 𝕋₀)
: (((amms.f.up t0' t1' x).up t1' t0' x.swap) t0 t1).fst ≠ 0 ↔ (((amms.f.up t0' t1' x).up t1' t0' x.swap) t0 t1).snd ≠ 0 := by
  apply @Decidable.byCases (t1'=t0)
  . intro t1pt0
    simp [t1pt0]
    apply @Decidable.byCases (t0'=t0)
    . intro t0pt0
      simp [t0pt0, t1pt0] at hdif
    . intro nt0pt0
      apply @Decidable.byCases (t0'=t1)
      . intro t0pt1
        simp [t1pt0, t0pt1] at hdif
        simp [t1pt0, t0pt1, hdif]
        exact h3.symm
      . intro nt0pt1
        simp [(Ne.intro nt0pt1).symm, (Ne.intro nt0pt0).symm]
        exact amms.h3 t0 t1
  
  . intro nt1pt0
    simp [(Ne.intro nt1pt0).symm, hdif.symm]
    apply @Decidable.byCases (t0'=t0)
    . intro t0pt0
      apply @Decidable.byCases (t1'=t1)
      . intro t1pt1
        simp only [t0pt0, t1pt1]
        simp [Finsupp.up_self]
        exact h3
      . intro nt1pt1
        rw [Finsupp.up_diff2 amms.f t0' t1' x t0 t1 (Ne.intro nt1pt1).symm]
        exact amms.h3 t0 t1
    . intro nt0pt0
      simp [(Ne.intro nt0pt0).symm, (Ne.intro nt1pt0).symm]
      exact amms.h3 t0 t1

noncomputable def 𝕊ₐ.initialize 
  (amms: 𝕊ₐ) {t0 t1: 𝕋₀} (hdif: t0 ≠ t1)
  (h: ¬amms.init t0 t1) (r0 r1: ℝ+): 𝕊ₐ :=
  
  ⟨
    (amms.f.up t0 t1 (r0, r1)).up t1 t0 (r1, r0),
    up_h1' amms t0 t1 (r0,r1) hdif,
    up_h2' amms t0 t1 (r0,r1) hdif,
    up_h3' amms t0 t1 (r0,r1) hdif (by sorry)
  ⟩

def 𝕊ₐ.r0 (amms: 𝕊ₐ) (t0 t1: 𝕋₀) 
  (h: amms.init t0 t1): ℝ+ := ⟨(amms.f t0 t1).fst, (by sorry)⟩

def 𝕊ₐ.r1 (amms: 𝕊ₐ) (t0 t1: 𝕋₀) 
  (h: amms.init t0 t1): ℝ+ := ⟨(amms.f t0 t1).snd, (by sorry)⟩

theorem 𝕊ₐ.r0_reorder
  (amms: 𝕊ₐ) (t1 t0: 𝕋₀) (h: amms.init t1 t0):
  amms.r0 t1 t0 h = amms.r1 t0 t1 h.swap := by sorry

theorem 𝕊ₐ.r1_reorder
  (amms: 𝕊ₐ) (t1 t0: 𝕋₀) (h: amms.init t1 t0):
  amms.r1 t1 t0 h = amms.r0 t0 t1 h.swap := by sorry

instance decidableInit (amms: 𝕊ₐ) (t0 t1: 𝕋₀): Decidable (amms.init t0 t1) 
  := by sorry

noncomputable def 𝕊ₐ.add_r0 (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (h: amms.init t0 t1) (x: PReal): 𝕊ₐ := 
  ⟨
    (amms.f.up t0 t1 (x + amms.r0 t0 t1 h, amms.r1 t0 t1 h)).up t1 t0 (amms.r1 t0 t1 h, x + amms.r0 t0 t1 h),
    (by sorry),
    (by sorry),
    (by sorry)
  ⟩

noncomputable def 𝕊ₐ.sub_r0 (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (h: amms.init t0 t1) (x: PReal) (nodrain: x < amms.r0 t0 t1 h): 𝕊ₐ := 
  ⟨
    (amms.f.up t0 t1 (amms.r0 t0 t1 (by sorry) - x, amms.r1 t0 t1 (by sorry))).up t1 t0 (amms.r1 t0 t1 (by sorry), amms.r0 t0 t1 (by sorry) - x),
    (by sorry),
    (by sorry),
    (by sorry)
  ⟩

noncomputable def 𝕊ₐ.add_r1 (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (h: amms.init t0 t1) (x: PReal): 𝕊ₐ := amms.add_r0 t1 t0 h.swap x

noncomputable def 𝕊ₐ.sub_r1 (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (h: amms.init t0 t1) (x: PReal) (h': x < amms.r1 t0 t1 h): 𝕊ₐ := amms.sub_r0 t1 t0 h.swap x (by sorry)

@[simp] theorem 𝕊ₐ.init_of_add_r0
  (amms: 𝕊ₐ) (t0 t1 t0' t1': 𝕋₀) (h: amms.init t0 t1) (x: PReal):
  (amms.add_r0 t0 t1 h x).init t0' t1'
  ↔
  amms.init t0' t1'
  := by sorry

@[simp] theorem 𝕊ₐ.init_of_add_r1
  (amms: 𝕊ₐ) (t0 t1 t0' t1': 𝕋₀) (h: amms.init t0 t1) (x: PReal):
  (amms.add_r1 t0 t1 h x).init t0' t1'
  ↔
  amms.init t0' t1'
  := by sorry

@[simp] theorem 𝕊ₐ.init_of_sub_r0
  (amms: 𝕊ₐ) (t0 t1 t0' t1': 𝕋₀) (h: amms.init t0 t1) (x: PReal) (h': x < amms.r0 t0 t1 h):
  (amms.sub_r0 t0 t1 h x h').init t0' t1'
  ↔
  amms.init t0' t1'
  := by sorry

@[simp] theorem 𝕊ₐ.init_of_sub_r1
  (amms: 𝕊ₐ) (t0 t1 t0' t1': 𝕋₀) (h: amms.init t0 t1) (x: PReal) (h': x < amms.r1 t0 t1 h):
  (amms.sub_r1 t0 t1 h x h').init t0' t1'
  ↔
  amms.init t0' t1'
  := by sorry

@[simp] theorem 𝕊ₐ.r0_of_add_r0
  (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (x: PReal)
  (h: amms.init t0 t1)
  :
  (amms.add_r0 t0 t1 h x).r0 t0 t1 (by simp [h])
  =
  x + amms.r0 t0 t1 h
  := by sorry

@[simp] theorem 𝕊ₐ.r0_of_add_r0_diff
  (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (x: PReal)
  (h: amms.init t0 t1) 
  (t0' t1': 𝕋₀) (h': amms.init t0' t1')
  (hdiff: diffpair t0 t1 t0' t1')
  :
  (amms.add_r0 t0 t1 h x).r0 t0' t1' (by simp [h'])
  =
  amms.r0 t0' t1' h'
  := by sorry

@[simp] theorem 𝕊ₐ.r0_of_add_r1
  (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (h: amms.init t0 t1) (x: PReal):
  (amms.add_r1 t0 t1 h x).r0 t0 t1 (by simp[h])
  =
  amms.r0 t0 t1 h
  := by sorry

@[simp] theorem 𝕊ₐ.r0_of_add_r1_diff
  (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (x: PReal)
  (h: amms.init t0 t1) 
  (t0' t1': 𝕋₀) (h': amms.init t0' t1')
  (hdiff: diffpair t0 t1 t0' t1')
  :
  (amms.add_r1 t0 t1 h x).r0 t0' t1' (by simp [h'])
  =
  amms.r0 t0' t1' h'
  := by sorry

@[simp] theorem 𝕊ₐ.r1_of_add_r1
  (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (h: amms.init t0 t1) (x: ℝ+):
  (amms.add_r1 t0 t1 h x).r1 t0 t1 (by simp[h])
  =
  x + amms.r1 t0 t1 h
  := by sorry

@[simp] theorem 𝕊ₐ.r1_of_add_r1_diff
  (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (x: PReal)
  (h: amms.init t0 t1) 
  (t0' t1': 𝕋₀) (h': amms.init t0' t1')
  (hdiff: diffpair t0 t1 t0' t1')
  :
  (amms.add_r1 t0 t1 h x).r1 t0' t1' (by simp [h'])
  =
  amms.r1 t0' t1' h'
  := by sorry

@[simp] theorem 𝕊ₐ.r1_of_add_r0
  (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (h: amms.init t0 t1) (x: ℝ+):
  (amms.add_r0 t0 t1 h x).r1 t0 t1 (by simp[h])
  =
  amms.r1 t0 t1 h
  := by sorry

@[simp] theorem 𝕊ₐ.r1_of_add_r0_diff
  (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (x: PReal)
  (h: amms.init t0 t1) 
  (t0' t1': 𝕋₀) (h': amms.init t0' t1')
  (hdiff: diffpair t0 t1 t0' t1')
  :
  (amms.add_r0 t0 t1 h x).r1 t0' t1' (by simp [h'])
  =
  amms.r1 t0' t1' h'
  := by sorry

@[simp] theorem 𝕊ₐ.r0_of_sub_r0
  (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r0 t0 t1 h):
  (amms.sub_r0 t0 t1 h x h').r0 t0 t1 (by simp[h])
  =
  (amms.r0 t0 t1 h).sub x h'
  := by sorry

@[simp] theorem 𝕊ₐ.r0_of_sub_r1
  (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r1 t0 t1 h):
  (amms.sub_r1 t0 t1 h x h').r0 t0 t1 (by simp[h])
  =
  amms.r0 t0 t1 h
  := by sorry

@[simp] theorem 𝕊ₐ.r1_of_sub_r1
  (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r1 t0 t1 h):
  (amms.sub_r1 t0 t1 h x h').r1 t0 t1 (by simp[h])
  =
  (amms.r1 t0 t1 h).sub x h'
  := by sorry

@[simp] theorem 𝕊ₐ.r1_of_sub_r0
  (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r0 t0 t1 h):
  (amms.sub_r0 t0 t1 h x h').r1 t0 t1 (by simp[h])
  =
  amms.r1 t0 t1 h
  := by sorry

@[simp] theorem 𝕊ₐ.r0_of_sub_r0_diff
  (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r0 t0 t1 h)
  (t0' t1': 𝕋₀) (h'': amms.init t0' t1')
  (hdiff: diffpair t0 t1 t0' t1'):
  (amms.sub_r0 t0 t1 h x h').r0 t0' t1' (by simp[h''])
  =
  amms.r0 t0' t1' h''
  := by sorry

@[simp] theorem 𝕊ₐ.r0_of_sub_r1_diff
  (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r1 t0 t1 h)
  (t0' t1': 𝕋₀) (h'': amms.init t0' t1')
  (hdiff: diffpair t0 t1 t0' t1'):
  (amms.sub_r1 t0 t1 h x h').r0 t0' t1' (by simp[h''])
  =
  amms.r0 t0' t1' h''
  := by sorry

@[simp] theorem 𝕊ₐ.r1_of_sub_r1_diff
  (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r1 t0 t1 h)
  (t0' t1': 𝕋₀) (h'': amms.init t0' t1')
  (hdiff: diffpair t0 t1 t0' t1'):
  (amms.sub_r1 t0 t1 h x h').r1 t0' t1' (by simp[h''])
  =
  amms.r1 t0' t1' h''
  := by sorry

@[simp] theorem 𝕊ₐ.r1_of_sub_r0_diff
  (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r0 t0 t1 h)
  (t0' t1': 𝕋₀) (h'': amms.init t0' t1')
  (hdiff: diffpair t0 t1 t0' t1'):
  (amms.sub_r0 t0 t1 h x h').r1 t0' t1' (by simp[h''])
  =
  amms.r0 t0' t1' h''
  := by sorry
