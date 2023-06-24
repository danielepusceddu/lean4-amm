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

def 𝕊ₐ.uninit
(amms: 𝕊ₐ) (t0 t1: 𝕋₀): Prop :=
  amms.f t0 t1 = 0

theorem 𝕊ₐ.empty_uninit (t0 t1: 𝕋₀):
  𝕊ₐ.empty.uninit t0 t1 := by
  simp [uninit, empty]

def 𝕊ₐ.init (amms: 𝕊ₐ) (t0 t1: 𝕋₀): Prop :=
  amms.f t0 t1 ≠ 0

def 𝕊ₐ.init.swap {amms: 𝕊ₐ} {t0 t1: 𝕋₀} (h: amms.init t0 t1):
  amms.init t1 t0 := by sorry

def 𝕊ₐ.init.dif {amms: 𝕊ₐ} {t0 t1: 𝕋₀} (h: amms.init t0 t1):
  t0 ≠ t1 := by sorry

def 𝕊ₐ.init.mint {amms: 𝕊ₐ} {t0 t1: 𝕋₀} 
  (h: amms.init t0 t1) := 𝕋₀.toMint h.dif


/-
def AMM
(amms: 𝕊ₐ) (t0 t1: 𝕋₀): Prop :=
  amms.f t0 t1 ≠ 0

def AMM.mint
  (amm: AMM amms t0 t1): 𝕋₁ := by sorry

def AMM.swap
  {amms: 𝕊ₐ} (h: AMM amms t1 t0):
  AMM amms t0 t1 := by
  unfold AMM at h ⊢
  rw [amms.h1]
  simp [h]

def AMM.set {amms: 𝕊ₐ} {t0 t1: 𝕋₀}
  (_: AMM amms t0 t1): 𝕊ₐ := amms

def AMM.r0 {amms: 𝕊ₐ} {t0 t1: 𝕋₀}
  (t0t1: AMM amms t0 t1): ℝ+ :=
  ⟨
    (amms.f t0 t1).fst,
    (by sorry)
  ⟩

def AMM.r1 {amms: 𝕊ₐ} {t0 t1: 𝕋₀}
  (t0t1: AMM amms t0 t1): ℝ+ :=
  ⟨
    (amms.f t0 t1).snd,
    (by sorry)
  ⟩

def AMM.r0_swap (amms: 𝕊ₐ) {t0 t1: 𝕋₀}
  (init: AMM amms t1 t0):
  init.r0 = init.swap.r1 := by
    simp [r1, r0, amms.h1 t1 t0]

def AMM.r1_swap (amms: 𝕊ₐ) {t0 t1: 𝕋₀}
  (init: AMM amms t1 t0):
  init.r1 = init.swap.r0 := by
    simp [r1, r0, amms.h1 t1 t0]

def AMM.r0_add_set {amms: 𝕊ₐ} {t0 t1: 𝕋₀}
  (init: AMM amms t0 t1) (x: ℝ+): 𝕊ₐ := by sorry

def AMM.r0_add {amms: 𝕊ₐ} {t0 t1: 𝕋₀}
  (init: AMM amms t0 t1) (x: ℝ+):
  AMM (init.r0_add_set x) t0 t1 := by sorry

/-
ammset: AMMSet

amm:  AMM ammset
amm': AMM ammset

AMMOf ammset -> AMMOf ammset.swap sw

I would like to do this:
(ammset.add_r0 amm x).add_r0 amm' y

Issue: what should the type of add_r0 be?
Obvious: ammset → (AMMOf ammset) → ammset
But, the above wouldn't work, because amm' is not AMMOf (added)

The workaround would be
(ammset.add_r0 t0 t1 x).add_r0 (ammof_add_r0 amm' x) y

Which is overly tedious

Another idea
((ammset.begin.add_r0 amm x).add_r0 amm' y).end

((ammset.begin.add_r0 amm x).add_r0 amm y).end
=
((ammset.begin.add_r0 amm (x+y)).end

Where begin: (ammset: AMMSet) → (opseq: OPSeq ammset)
      add_r0: (opseq: OPSeq ammset) → (amm: AMMOf ammset) → ℝ+ → (opseq: OPSeq.ammset)
      end: (opseq: OPSeq ammset) → AMMSet


Swap definita come
((ammset.begin.add_r0 amm x).sub_r1 amm y nodrain).end

Se facciamo un'altra swap
(((ammset.begin.add_r0 amm x).sub_r1 amm y nodrain).end.begin.add_r0 amm' x').sub_r1 amm' y' nodrain').end
=
(((ammset.begin.add_r0 amm x).sub_r1 amm y nodrain).add_r0 amm' x').sub_r1 amm' y' nodrain').end


sub_r1: (seq: OPSeq ammset) → (amm: AMM ammset) → (y: ℝ+) → (nodrain: y < seq.end.r1 amm) →  OPSeq ammset

(((ammset.begin.add_r0 amm x).sub_r1 amm y nodrain)
=






((ammset.add_r0 t0 t1 x).add_r0 t0 t1 y).r0
=
((ammset.add_r0 t0 t1 (x+y))).r0

per casi su (t0,t1) ∈ ammset
  se true, allora (t0,t1 ∈ (ammset.add_r0 t0 t1 x))
           e      (t0,t1 ∈ ((ammset.add_r0 t0 t1 x).add_r0 t0 t1 y))


-/

#check Option
/-
Monad (α β) m: α → β
m takes a type and gives you a type. For example, Option.
β may be the same type as well.

bind: m α → (α → m β) → m β. 
example: Option α → (α → Option β) → Option β
bind (pure v) f should be the same as f v.
bind (bind v f) g should be the same as bind v (fun x => bind (f x) g)

The method bind is composing these two actions. We often say bind is an abstract semicolon. 

pure : α → m α
example: α → Option α

Pure could be OPSeq.empty: ammset → OPSeq ammset
bind could be (add_r0 amm x) ?
What would the type of bind be?
OPSeq ammset → (ammset → OPSeq ammset) → OPSeq ammset

Pure could be id: ammset → ammset
What would the type of bind be?
ammset → (ammset → β) → β

state has an OPSeq instead of ammset


Applicative?
Instead of bind, we have seq : m (α → β) → m α → m β
For Options:
Option (α → β) → Option α → Option β

For OPSeq

-/
def AMM.amm_of_r0_add {amms: 𝕊ₐ} {t0 t1: 𝕋₀}
  (init: AMM amms t0 t1) (x: ℝ+):
  AMM (init.r0_add_set x) t0 t1 := by sorry

@[simp] theorem 𝕊ₐ.r0_of_r0_add {amms: 𝕊ₐ} {t0 t1: 𝕋₀}
  (init: AMM amms t0 t1) (x: ℝ+):
  (init.r0_add x).r0 = init.r0 + x := by sorry

@[simp] theorem 𝕊ₐ.r1_of_r0_add {amms: 𝕊ₐ} {t0 t1: 𝕋₀}
  (init: AMM amms t0 t1) (x: ℝ+):
  (init.r0_add x).r1 = init.r1 := by sorry

@[simp] theorem 𝕊ₐ.r0_of_r0_add_diff {amms: 𝕊ₐ} {t0 t1 t0' t1': 𝕋₀}
  (init: AMM amms t0 t1) (x: ℝ+)
  (init': AMM amms t0' t1')
  (hdif: init'.mint ≠ init.mint):
  (init.r0_add x).r0 = init.r0 + x := by sorry

@[simp] theorem 𝕊ₐ.r1_of_r0_add' {amms: 𝕊ₐ} {t0 t1: 𝕋₀}
  (init: AMM amms t0 t1) (x: ℝ+):
  (init.r0_add x).r1 = init.r1 := by sorry

def AMM.r1_add_set {amms: 𝕊ₐ} {t0 t1: 𝕋₀}
  (init: AMM amms t0 t1) (x: ℝ+): 𝕊ₐ := by sorry

def AMM.r1_add {amms: 𝕊ₐ} {t0 t1: 𝕋₀}
  (init: AMM amms t0 t1) (x: ℝ+):
  AMM (init.r1_add_set x) t0 t1 := by sorry

@[simp] theorem 𝕊ₐ.r1_of_r1_add {amms: 𝕊ₐ} {t0 t1: 𝕋₀}
  (init: AMM amms t0 t1) (x: ℝ+):
  (init.r1_add x).r1 = init.r1 + x := by sorry

@[simp] theorem 𝕊ₐ.r0_of_r1_add {amms: 𝕊ₐ} {t0 t1: 𝕋₀}
  (init: AMM amms t0 t1) (x: ℝ+):
  (init.r1_add x).r0 = init.r0 := by sorry

def AMM.r0_sub_set {amms: 𝕊ₐ} {t0 t1: 𝕋₀}
  (init: AMM amms t0 t1) (x: ℝ+) (nodrain: x < init.r0): 𝕊ₐ := by sorry

def AMM.r0_sub {amms: 𝕊ₐ} {t0 t1: 𝕋₀}
  (init: AMM amms t0 t1) (x: ℝ+) (nodrain: x < init.r0):
  AMM (init.r0_sub_set x nodrain) t0 t1 := by sorry

@[simp] theorem 𝕊ₐ.r0_of_r0_sub {amms: 𝕊ₐ} {t0 t1: 𝕋₀}
  (init: AMM amms t0 t1) (x: ℝ+) (nodrain: x < init.r0):
  (init.r0_sub x nodrain).r0 = init.r0.sub x nodrain := by sorry

@[simp] theorem 𝕊ₐ.r1_of_r0_sub {amms: 𝕊ₐ} {t0 t1: 𝕋₀}
  (init: AMM amms t0 t1) (x: ℝ+) (nodrain: x < init.r0):
  (init.r0_sub x nodrain).r1 = init.r1 := by sorry

def AMM.r1_sub_set {amms: 𝕊ₐ} {t0 t1: 𝕋₀}
  (init: AMM amms t0 t1) (x: ℝ+) (nodrain: x < init.r1): 𝕊ₐ := by sorry

def AMM.r1_sub {amms: 𝕊ₐ} {t0 t1: 𝕋₀}
  (init: AMM amms t0 t1) (x: ℝ+) (nodrain: x < init.r1):
  AMM (init.r1_sub_set x nodrain) t0 t1 := by sorry

@[simp] theorem 𝕊ₐ.r1_of_r1_sub {amms: 𝕊ₐ} {t0 t1: 𝕋₀}
  (init: AMM amms t0 t1) (x: ℝ+) (nodrain: x < init.r1):
  (init.r1_sub x nodrain).r1 = init.r1.sub x nodrain := by sorry

@[simp] theorem 𝕊ₐ.r0_of_r1_sub {amms: 𝕊ₐ} {t0 t1: 𝕋₀}
  (init: AMM amms t0 t1) (x: ℝ+) (nodrain: x < init.r1):
  (init.r1_sub x nodrain).r0 = init.r0 := by sorry
-/

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
  (h: amms.uninit t0 t1) (r0 r1: ℝ+): 𝕊ₐ :=
  
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

@[simp] theorem 𝕊ₐ.r0_of_add_r1
  (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (h: amms.init t0 t1) (x: PReal):
  (amms.add_r1 t0 t1 h x).r0 t0 t1 (by simp[h])
  =
  amms.r0 t0 t1 h
  := by sorry

@[simp] theorem 𝕊ₐ.r1_of_add_r1
  (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (h: amms.init t0 t1) (x: ℝ+):
  (amms.add_r1 t0 t1 h x).r1 t0 t1 (by simp[h])
  =
  x + amms.r1 t0 t1 h
  := by sorry

@[simp] theorem 𝕊ₐ.r1_of_add_r0
  (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (h: amms.init t0 t1) (x: ℝ+):
  (amms.add_r0 t0 t1 h x).r1 t0 t1 (by simp[h])
  =
  amms.r1 t0 t1 h
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

theorem 𝕊ₐ.init_imp_diff 
  (amms: 𝕊ₐ) (t0 t1: 𝕋₀) (h: amms.init t0 t1):
  t0 ≠ t1 := by sorry

/-
amms.add_r0 t0 t1 x :=
  if t0 t1 ∈ amms
  then amms.update_r0 t0 t1 (x + amms.r0 t0 t1)
  else amms

simp theorem1
(amms.add_r0 t0 t1 x).r0 t0 t1
= 
if t0 t1 ∈ amms 
then x + amms.r0
else 0

simp theorem2
t0 t1 ∈ (amms.add_r0 t0' t1' x)
↔
t0 t1 ∈ amms


example simplification (done automatically)
h: t0 t1 ∈ amms

⊢ .. ((amms.add_r0 t0 t1 x).add_r0 t0 t1 y).r0 t0 t1 ..

by theorem1
if t0 t1 ∈ (amms.add_r0 t0 t1 x)
then y + (amms.add_r0 t0 t1 x).r0 t0 t1
else 0

by theorem2
if t0 t1 ∈ amms
then y + (amms.add_r0 t0 t1 x).r0 t0 t1
else 0

by h
y + (amms.add_r0 t0 t1 x).r0 t0 t1

by theorem1
y + if t0 t1 ∈ amms then x + amms.r0 t0 t1 else 0

by h
y + x + amms.r0 t0 t1
-/
