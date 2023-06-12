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

theorem 𝕊ₐ.reorder_fst
(a: 𝕊ₐ) (t1 t0: 𝕋₀):
(a.f t1 t0).fst = (a.f t0 t1).snd := by
  simp [a.h1 t1 t0]

theorem 𝕊ₐ.reorder_snd
(a: 𝕊ₐ) (t1 t0: 𝕋₀):
(a.f t1 t0).snd = (a.f t0 t1).fst := by
  simp [a.h1 t1 t0]

def 𝕊ₐ.empty: 𝕊ₐ :=
⟨ 
  0,
  by intro _ _; simp,
  by intro t; simp; exact Prod.zero_eq_mk,
  by intro t0 t1; apply Iff.intro;
     . simp
     . simp
⟩ 

theorem Prod.mk_eq
{α β: Type} [Zero α] [Zero β]
(p: α × β): (p.fst, p.snd) = p := by simp

theorem Prod.fst_snd_zero_imp_zero
{α β: Type} [Zero α] [Zero β]
(p: α × β) (h1: p.fst = 0) (h2: p.snd = 0): p = 0 := by
  rw [← Prod.mk_eq p]
  apply (Prod.mk_eq_zero).mpr
  apply And.intro
  . exact h1
  . exact h2


theorem Prod.neq_zero_imp_or 
{α β: Type} [Zero α] [Zero β]
{p: α × β} (h: p ≠ 0): p.fst ≠ 0 ∨ p.snd ≠ 0 := by
  by_contra contra
  simp at contra
  have h' := and_iff_not_or_not.mpr contra
  rcases h' with ⟨left,right⟩
  have h' := Prod.fst_snd_zero_imp_zero p left right
  contradiction

theorem 𝕊ₐ.exists_imp_fst 
{amms: 𝕊ₐ} {t0 t1: 𝕋₀} (h: amms.f t0 t1 ≠ 0)
: ((amms.f t0 t1).fst ≠ 0) := by
  have h' := Prod.neq_zero_imp_or h
  rcases h' with left|right
  . exact left
  . exact (amms.h3 t0 t1).mpr right

theorem 𝕊ₐ.exists_imp_snd
{amms: 𝕊ₐ} {t0 t1: 𝕋₀} (h: amms.f t0 t1 ≠ 0)
: ((amms.f t0 t1).snd ≠ 0) := by
  have h' := Prod.neq_zero_imp_or h
  rcases h' with left|right
  . exact (amms.h3 t0 t1).mp left
  . exact right

theorem 𝕊ₐ.exists_imp_dif 
{amms: 𝕊ₐ} {t0 t1: 𝕋₀} (h: amms.f t0 t1 ≠ 0)
: t0 ≠ t1 := by
  by_contra contra
  rw [contra] at h
  rw [amms.h2] at h
  contradiction

theorem 𝕊ₐ.exists_swap
{amms: 𝕊ₐ} {t0 t1: 𝕋₀} (h: amms.f t0 t1 ≠ 0):
amms.f t1 t0 ≠ 0 := by
  rw [amms.h1]
  simp [h]

def 𝕊ₐ.fp (amms: 𝕊ₐ) {t0 t1: 𝕋₀}
(exi: amms.f t0 t1 ≠ 0): ℝ+ × ℝ+ :=
(
  ⟨(amms.f t0 t1).fst.val,
   NNReal.neq_zero_imp_gt (𝕊ₐ.exists_imp_fst exi)
  ⟩,
  ⟨(amms.f t0 t1).snd.val,
   NNReal.neq_zero_imp_gt (𝕊ₐ.exists_imp_snd exi)
  ⟩
)

theorem 𝕊ₐ.reorder_fstp
(a: 𝕊ₐ) (t1 t0: 𝕋₀)
(exi: a.f t1 t0 ≠ 0):
(a.fp exi).fst = (a.fp (𝕊ₐ.exists_swap exi)).snd := by
  simp [fp, a.h1 t1 t0]

theorem 𝕊ₐ.reorder_sndp
(a: 𝕊ₐ) (t1 t0: 𝕋₀)
(exi: a.f t1 t0 ≠ 0):
(a.fp exi).snd = (a.fp (𝕊ₐ.exists_swap exi)).fst := by
  simp [fp, a.h1 t1 t0]

theorem 𝕊ₐ.fstp_coe_eq
{a: 𝕊ₐ} {t0 t1: 𝕋₀}
(exi: a.f t0 t1 ≠ 0):
((a.fp exi).fst: NNReal) = (a.f t0 t1).fst := by
  rfl

theorem 𝕊ₐ.sndp_coe_eq
{a: 𝕊ₐ} {t0 t1: 𝕋₀}
(exi: a.f t0 t1 ≠ 0):
((a.fp exi).snd: NNReal) = (a.f t0 t1).snd := by
  rfl

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

noncomputable def 𝕊ₐ.up (amms: 𝕊ₐ) 
(t0 t1: 𝕋₀) (x: NNReal × NNReal) (hdif: t0 ≠ t1)
(h3: x.fst ≠ 0 ↔ x.snd ≠ 0)
: 𝕊ₐ := 
⟨
  (amms.f.up t0 t1 x).up t1 t0 x.swap,
  up_h1' amms t0 t1 x hdif, 
  up_h2' amms t0 t1 x hdif,
  up_h3' amms t0 t1 x hdif h3
⟩

/- When passing only one of the arguments, we need it to be different to both updated tokens. -/
@[simp] theorem 𝕊ₐ.up_diff1 (amms: 𝕊ₐ)
(t0' t1': 𝕋₀) (x: NNReal × NNReal) 
(hdif: t0' ≠ t1') (h3: x.fst ≠ 0 ↔ x.snd ≠ 0)
(t0: 𝕋₀) (h1: t0 ≠ t0') (h2: t0 ≠ t1')
: (amms.up t0' t1' x hdif h3).f t0 = amms.f t0 := by
  simp [up, h2, h1]

/- When passing two arguments, we need to know {t0,t1} ≠ {t0',t1'} -/
@[simp] theorem 𝕊ₐ.up_diff2 (amms: 𝕊ₐ)
(t0' t1': 𝕋₀) (x: NNReal × NNReal) 
(hdif: t0' ≠ t1') (h3: x.fst ≠ 0 ↔ x.snd ≠ 0)
(t0 t1: 𝕋₀) (h1: (t0 ≠ t0' ∨ t1 ≠ t1') ∧ (t0 ≠ t1' ∨ t1 ≠ t0'))
: (amms.up t0' t1' x hdif h3).f t0 t1 = amms.f t0 t1 := by

  rcases h1 with ⟨left|left', right|right'⟩
  . simp [left, right]
  . simp [up, left, right']
  . simp [up, left', right]
  . simp [up, left', right']

@[simp] theorem 𝕊ₐ.up_diff2_pos (amms: 𝕊ₐ)
(t0' t1': 𝕋₀) (x: NNReal × NNReal) 
(hdif: t0' ≠ t1') (h3: x.fst ≠ 0 ↔ x.snd ≠ 0)
(t0 t1: 𝕋₀) 
(hpos: amms.f t0 t1 ≠ 0)
(h1: (t0 ≠ t0' ∨ t1 ≠ t1') ∧ (t0 ≠ t1' ∨ t1 ≠ t0'))
: @𝕊ₐ.fp (amms.up t0' t1' x hdif h3) t0 t1 (by simp [h1, hpos]) = amms.fp hpos := by
  unfold fp
  simp only [Prod.eq_iff_fst_eq_snd_eq]
  apply And.intro
  <;>
  (apply Subtype.eq
   simp [h1])

@[simp] theorem 𝕊ₐ.up_same (amms: 𝕊ₐ)
(t0' t1': 𝕋₀) (x: NNReal × NNReal)
(hdif: t0' ≠ t1') 
(h3: x.fst ≠ 0 ↔ x.snd ≠ 0)
: (amms.up t0' t1' x hdif h3).f t0' t1' = x := by
  simp [up, hdif]

@[simp] theorem 𝕊ₐ.up_same' (amms: 𝕊ₐ)
(t0' t1': 𝕋₀) (x: NNReal × NNReal)
(hdif: t0' ≠ t1') 
(h3: x.fst ≠ 0 ↔ x.snd ≠ 0)
: (amms.up t0' t1' x hdif h3).f t1' t0' = x.swap := by
  simp [up, hdif]

noncomputable def 𝕊ₐ.add_r0 (amms: 𝕊ₐ)
{t0 t1: 𝕋₀} (x: NNReal) 
(exi: amms.f t0 t1 ≠ 0): 𝕊ₐ
:= amms.up t0 t1 ((amms.f t0 t1) + (x,0)) (exists_imp_dif exi) 
   (by apply Iff.intro
       . field_simp
         intro _
         exact 𝕊ₐ.exists_imp_snd exi
       . field_simp
         intro _ fsteq_contra
         have fstneq := 𝕊ₐ.exists_imp_fst exi
         contradiction)

noncomputable def 𝕊ₐ.add_r1 (amms: 𝕊ₐ)
{t0 t1: 𝕋₀} (x: NNReal) 
(exi: amms.f t0 t1 ≠ 0): 𝕊ₐ
:= amms.up t0 t1 ((amms.f t0 t1) + (0,x)) (exists_imp_dif exi) 
   (by apply Iff.intro
       . field_simp
         intro _ sndeq_contra
         have sndneq := 𝕊ₐ.exists_imp_snd exi
         contradiction

       . field_simp
         intro _ fsteq_contra
         have fstneq := 𝕊ₐ.exists_imp_fst exi
         contradiction)

noncomputable def 𝕊ₐ.sub_r0 (amms: 𝕊ₐ)
{t0 t1: 𝕋₀} (x: NNReal) 
(nodrain: x < (amms.f t0 t1).fst): 𝕊ₐ
:= amms.up t0 t1 ((amms.f t0 t1) - (x,0)) 
  (by have fstne: (amms.f t0 t1).fst ≠ 0 := by
        exact ne_bot_of_gt nodrain
      have exi: amms.f t0 t1 ≠ 0 := by
        simp only [Prod.neq_zero_iff]
        left
        exact fstne
      exact 𝕊ₐ.exists_imp_dif exi)

  (by have fstne: (amms.f t0 t1).fst ≠ 0 := by
        exact ne_bot_of_gt nodrain
      have sndne := (amms.h3 t0 t1).mp fstne
      apply Iff.intro
      . intro _
        simp; exact sndne
      . intro _;
        simp; exact nodrain)

noncomputable def 𝕊ₐ.sub_r1 (amms: 𝕊ₐ)
{t0 t1: 𝕋₀} (x: NNReal)
(nodrain: x < (amms.f t0 t1).snd): 𝕊ₐ
:= amms.up t0 t1 ((amms.f t0 t1) - (0,x))
  (by have sndne: (amms.f t0 t1).snd ≠ 0 := by
        exact ne_bot_of_gt nodrain
      have exi: amms.f t0 t1 ≠ 0 := by
        simp only [Prod.neq_zero_iff]
        right
        exact sndne
      exact 𝕊ₐ.exists_imp_dif exi)
      
  (by have sndne: (amms.f t0 t1).snd ≠ 0 := by
        exact ne_bot_of_gt nodrain
      have fstne := (amms.h3 t0 t1).mpr sndne
      apply Iff.intro
      . intro _
        simp; exact nodrain
      . intro _;
        simp; exact fstne)
