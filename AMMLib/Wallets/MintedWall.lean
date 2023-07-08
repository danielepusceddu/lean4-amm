import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Sym.Sym2
import Mathlib.Algebra.BigOperators.Finsupp
import HelpersLib.NNReal
import HelpersLib.Prod
import HelpersLib.PReal.Basic
import HelpersLib.PReal.Subtraction
import HelpersLib.Finsupp2
import AMMLib.Tokens
import AMMLib.Wallets.AtomicWall

structure 𝕎₁ where 
  f: 𝕋 →₀ 𝕎₀
  h1: ∀ (t0 t1: 𝕋), f t0 t1 = f t1 t0
  h2: ∀ (t: 𝕋), f t t = 0

def 𝕎₁.empty: 𝕎₁ :=
⟨ 
  0,
  by simp,
  by simp
⟩

instance: Zero 𝕎₁ := ⟨𝕎₁.empty⟩

def 𝕎₁.get (w: 𝕎₁) (t0 t1: 𝕋): NNReal := w.f t0 t1

@[simp] theorem 𝕎₁.zero_get (t0 t1: 𝕋):
  (0: 𝕎₁).get t0 t1 = 0 := by
  have h: (0: 𝕎₁) = empty := by rfl
  rw [h]
  simp [empty, get]

theorem 𝕎₁.f_eq_get  (w: 𝕎₁) (t0 t1: 𝕋):
  w.f t0 t1 = w.get t0 t1 := by rfl

theorem 𝕎₁.get_reorder (w: 𝕎₁) (t1 t0: 𝕋):
  w.get t1 t0 = w.get t0 t1 := by
  simp [w.h1, 𝕎₁.get]

theorem 𝕎₁.samepair_get (w: 𝕎₁) {t0 t1 t0' t1': 𝕋} (h: samemint t0 t1 t0' t1'):
  w.get t0 t1 = w.get t0' t1' := by
  rcases h with ⟨a,b⟩|⟨a,b⟩
  . simp [a,b]
  . simp [a, b, w.get_reorder]

noncomputable def 𝕎₁.add (w: 𝕎₁) (t0 t1: 𝕋) 
  (hdif: t0 ≠ t1) (x: NNReal): 𝕎₁ :=
⟨
  (w.f.update t0 ((w.f t0).add t1 x)).update t1 ((w.f t1).add t0 x),
  by intro t0' t1'
     rcases (Decidable.em (t0' = t0)), (Decidable.em (t0' = t1)), (Decidable.em (t1' = t0)), (Decidable.em (t1' = t1)) with ⟨left|
     left, right|right, left'|left', right'|right'⟩
     <;> simp [left, right, left', right', hdif, w.h1],

  by intro t
     rcases Decidable.em (t = t0), Decidable.em (t = t1) with ⟨left|left, right|right⟩
     <;> simp [hdif, left, right, w.h2]
⟩ 

theorem 𝕎₁.add_reorder (w: 𝕎₁) (t1 t0: 𝕋) (hdif: t0 ≠ t1) (x: NNReal):
  w.add t1 t0 hdif.symm x = w.add t0 t1 hdif x := by

  simp only [add, mk.injEq]
  ext t0' t1'
  rcases (Decidable.em (t0' = t0)), (Decidable.em (t0' = t1)), (Decidable.em (t1' = t0)), (Decidable.em (t1' = t1)) with ⟨left|
     left, right|right, left'|left', right'|right'⟩
  <;> simp [left, right, left', right', hdif, hdif.symm, w.h1]

@[simp] theorem 𝕎₁.get_add_self (w: 𝕎₁) (t0 t1: 𝕋) (hdif: t0 ≠ t1) (x: NNReal):
  (w.add t0 t1 hdif x).get t0 t1 = w.get t0 t1 + x := by
  simp [add, hdif, hdif.symm, get]

@[simp] theorem 𝕎₁.get_add_diff (w: 𝕎₁) (t0 t1: 𝕋) (hdif: t0 ≠ t1) (x: NNReal) (t0' t1': 𝕋) (diffp: diffmint t0 t1 t0' t1'):
  (w.add t0 t1 hdif x).get t0' t1' = w.get t0' t1' := by

  rcases diffp with ⟨left,right⟩|⟨left,right⟩
  . rw [get_reorder _ t0' t1']
    rw [add_reorder _ t0 t1 hdif.symm _]
    rcases Decidable.em (t1' = t1) with left'|left'
    . simp [get, add, left, right, left.symm, right.symm, left'.symm, w.h1]
    . simp [get, add, left, right, left.symm, right.symm, left', w.h1]

  . rcases Decidable.em (t0' = t0) with left'|left'
    . simp [get, add, left, right, left.symm, right.symm, left'.symm, w.h1]
    . simp [get, add, left, right, left.symm, right.symm, left', w.h1]

noncomputable def 𝕎₁.sub (w: 𝕎₁) (t0 t1: 𝕋) (hdif: t0 ≠ t1) (x: NNReal) (h: x ≤ w.get t0 t1): 𝕎₁ :=
⟨
  (w.f.update t0 ((w.f t0).sub t1 x h)).update t1 ((w.f t1).sub t0 x (by unfold get at h; simp [h, w.h1])),

  by intro t0' t1'
     rcases (Decidable.em (t0' = t0)), (Decidable.em (t0' = t1)), (Decidable.em (t1' = t0)), (Decidable.em (t1' = t1)) with ⟨left|
     left, right|right, left'|left', right'|right'⟩
     <;> simp [left, right, left', right', hdif, w.h1],

  by intro t
     rcases Decidable.em (t = t0), Decidable.em (t = t1) with ⟨left|left, right|right⟩
     <;> simp [hdif, left, right, w.h2]
⟩ 

theorem 𝕎₁.sub_reorder (w: 𝕎₁) (t1 t0: 𝕋) (hdif: t0 ≠ t1) (x: NNReal) (h: x ≤ w.get t0 t1):
  w.sub t1 t0 hdif.symm x (by rw [get_reorder _ t1 t0]; exact h) = w.sub t0 t1 hdif x h := by
  simp only [sub, mk.injEq]
  ext t0' t1'
  rcases (Decidable.em (t0' = t0)), (Decidable.em (t0' = t1)), (Decidable.em (t1' = t0)), (Decidable.em (t1' = t1)) with ⟨left|
     left, right|right, left'|left', right'|right'⟩
  <;> simp [left, right, left', right', hdif, hdif.symm, w.h1]

@[simp] theorem 𝕎₁.get_sub_self (w: 𝕎₁) (t0 t1: 𝕋) (hdif: t0 ≠ t1) (x: NNReal) (h: x ≤ w.get t0 t1):
  (w.sub t0 t1 hdif x h).get t0 t1 = w.get t0 t1 - x := by
  simp [sub, hdif, hdif.symm, get]

@[simp] theorem 𝕎₁.get_sub_diff (w: 𝕎₁) (t0 t1: 𝕋) (hdif: t0 ≠ t1) (x: NNReal) (h: x ≤ w.get t0 t1) (t0' t1': 𝕋) (diffp: diffmint t0 t1 t0' t1'):
  (w.sub t0 t1 hdif x h).get t0' t1' = w.get t0' t1' :=
  by

  rcases diffp with ⟨left,right⟩|⟨left,right⟩
  . rw [get_reorder _ t0' t1']
    rw [sub_reorder _ t0 t1 hdif.symm _ (by simp [get_reorder, h])]
    rcases Decidable.em (t1' = t1) with left'|left'
    . simp [get, sub, left, right, left.symm, right.symm, left'.symm, w.h1]
    . simp [get, sub, left, right, left.symm, right.symm, left', w.h1]

  . rcases Decidable.em (t0' = t0) with left'|left'
    . simp [get, sub, left, right, left.symm, right.symm, left'.symm, w.h1]
    . simp [get, sub, left, right, left.symm, right.symm, left', w.h1]

noncomputable def 𝕎₁.drain (w: 𝕎₁) (t0 t1: 𝕋) (hdif: t0 ≠ t1): 𝕎₁ := 
  w.sub t0 t1 hdif (w.get t0 t1) (by simp)

theorem 𝕎₁.drain_reorder (w: 𝕎₁) (t1 t0: 𝕋) (hdif: t0 ≠ t1):
  w.drain t1 t0 hdif.symm = w.drain t0 t1 hdif := by 
  unfold drain
  simp_rw [get_reorder _ t1 t0]
  rw [sub_reorder _ t1 t0 hdif]

@[simp] theorem 𝕎₁.get_drain_self (w: 𝕎₁) (t0 t1: 𝕋) (hdif: t0 ≠ t1):
  (w.drain t0 t1 hdif).get t0 t1 = 0 := by
  simp [drain]

@[simp] theorem 𝕎₁.get_drain_diff (w: 𝕎₁) (t0 t1: 𝕋) (hdif: t0 ≠ t1) (t0' t1': 𝕋) (diffp: diffmint t0 t1 t0' t1'):
  (w.drain t0 t1 hdif).get t0' t1' = w.get t0' t1' := by
  simp [drain, diffp]


noncomputable def 𝕎₁.u (w: 𝕎₁): (𝕋 × 𝕋) →₀ NNReal := w.f.uncurry

theorem 𝕎₁.u_def (w: 𝕎₁) (t0 t1: 𝕋): w.u (t0,t1) = w.get t0 t1 := by
  unfold get
  unfold u
  rw [Finsupp.uncurry_apply]

noncomputable def 𝕎₁.worth (w: 𝕎₁) (o: 𝕋 → 𝕋 → NNReal): NNReal :=
  (w.u.sum (λ p x => x*(o p.fst p.snd))) / 2

theorem 𝕎₁.worth_destruct (w: 𝕎₁) (o: 𝕋 → 𝕋 → NNReal) (t0 t1: 𝕋) (hdif: t0 ≠ t1) (ho: o t1 t0 = o t0 t1):
  w.worth o = (w.drain t0 t1 hdif).worth o + (w.get t0 t1)*(o t0 t1)
  := by 
  unfold worth
  rw [← Finsupp.add_sum_erase' _ (t0,t1) _ (by simp)]
  rw [← Finsupp.add_sum_erase' _ (t1,t0) _ (by simp)]
  rw [Finsupp.erase_ne (by simp[hdif])]

  have h: ∀ (w: 𝕎₁) (t0 t1: 𝕋) (h: t0 ≠ t1), Finsupp.erase (t1,t0) (Finsupp.erase (t0,t1) w.u) = (w.drain t0 t1 h).u := by 
    intro w' t0' t1' h'
    unfold drain
    unfold sub
    unfold u
    unfold 𝕎₀.sub
    unfold get
    simp [w'.h1 t1' t0', Finsupp.update_zero_eq_erase]
    ext p
    rw [Prod.fst_snd p]
    rw [Finsupp.uncurry_apply]
    rcases Decidable.em (p.fst = t0'), Decidable.em (p.fst = t1'), Decidable.em (p.snd = t0'), Decidable.em (p.snd = t1') with ⟨a|a, b|b, c|c, d|d⟩
    . simp [a, b, c, d, h', h'.symm, Finsupp.uncurry_apply]
    . simp [a, b, c, d, h', h'.symm, Finsupp.uncurry_apply]
    . simp [a, b, c, d, h', h'.symm, Finsupp.uncurry_apply]
    . simp [a, b, c, d, h', h'.symm, Finsupp.uncurry_apply]
    . simp [a, b, c, d, h', h'.symm, Finsupp.uncurry_apply]
    . simp [a, b, c, d, h', h'.symm, Finsupp.uncurry_apply]
    . simp [a, b, c, d, h', h'.symm, Finsupp.uncurry_apply]
    . simp [a, b, c, d, h', h'.symm, Finsupp.uncurry_apply]
    . simp [a, b, c, d, h', h'.symm, Finsupp.uncurry_apply]
    . simp [a, b, c, d, h', h'.symm, Finsupp.uncurry_apply]
    . simp [a, b, c, d, h', h'.symm, Finsupp.uncurry_apply]
    . simp [a, b, c, d, h', h'.symm, Finsupp.uncurry_apply]
    . simp [a, b, c, d, h', h'.symm, Finsupp.uncurry_apply]
    . simp [a, b, c, d, h', h'.symm, Finsupp.uncurry_apply]
    . simp [a, b, c, d, h', h'.symm, Finsupp.uncurry_apply]
    . have hp: p ≠ (t1', t0') := by 
        apply (Prod.neq_iff_fst_neq_or_snd_eq p (t1', t0')).mpr
        left
        simp [b]

      have hp': p ≠ (t0', t1') := by
        apply (Prod.neq_iff_fst_neq_or_snd_eq p (t0', t1')).mpr
        left
        simp [a]
      simp only [Finsupp.mem_support_iff, Finsupp.uncurry_apply, ne_eq, not_not, Finsupp.support_erase,
        Finset.mem_erase, Prod.mk.injEq, h'.symm, h', and_self, not_false_eq_true, true_and, Prod.mk.eta, hp,
        Finsupp.erase_ne, hp', Finsupp.coe_update, b, Function.update_noteq, a, NNReal.coe_eq]
      rw [Finsupp.uncurry_apply]

  rw [h _ _ _ hdif]
  rw [u_def]
  rw [u_def]
  rw [get_reorder w t1 t0]
  rw [ho]
  rw [← add_assoc]
  rw [add_div]
  rw [add_self_div_two]
  rw [add_comm]