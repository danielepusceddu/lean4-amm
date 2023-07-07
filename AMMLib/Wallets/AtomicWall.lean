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
import Mathlib.Tactic.LibrarySearch

abbrev 𝕎₀ := 𝕋 →₀ NNReal

noncomputable def 𝕎₀.add (w: 𝕎₀) (t: 𝕋) (x: NNReal): 𝕎₀ := 
  w.update t ((w t) + x)

@[simp] theorem 𝕎₀.get_add_self (w: 𝕎₀) (t: 𝕋) (x: NNReal):
  (w.add t x) t = w t + x := by simp [𝕎₀.add]

@[simp] theorem 𝕎₀.get_add_diff (w: 𝕎₀) (t: 𝕋) (x: NNReal) (t': 𝕋) (hdif: t ≠ t'):
  (w.add t x) t' = w t' := by simp [𝕎₀.add, hdif.symm]

noncomputable def 𝕎₀.sub (w: 𝕎₀) (t: 𝕋) (x: NNReal) (_: x ≤ w t): 𝕎₀ :=
  w.update t ((w t) - x)

@[simp] theorem 𝕎₀.get_sub_self (w: 𝕎₀) (t: 𝕋) (x: NNReal) (h: x ≤ w t):
  (w.sub t x h) t = w t - x := by simp [𝕎₀.sub]

@[simp] theorem 𝕎₀.get_sub_diff (w: 𝕎₀) (t: 𝕋) (x: NNReal) (h: x ≤ w t) (t': 𝕋) (diff: t ≠ t'):
  (w.sub t x h) t' = w t' := by simp [𝕎₀.sub, diff.symm]

noncomputable def 𝕎₀.drain (w: 𝕎₀) (t: 𝕋): 𝕎₀ := 
  w.sub t (w t) (by simp)

@[simp] theorem 𝕎₀.get_drain_self (w: 𝕎₀) (t: 𝕋):
  (w.drain t) t = 0 := by simp [𝕎₀.drain]

@[simp] theorem 𝕎₀.get_drain_diff (w: 𝕎₀) (t t': 𝕋) (diff: t ≠ t'):
  (w.drain t) t' = w t' := by simp [𝕎₀.drain, diff]

theorem 𝕎₀.drain_comm (w: 𝕎₀) (t0 t1: 𝕋):
  (w.drain t1).drain t0 = (w.drain t0).drain t1 := by 
  ext t0' t1'
  apply @Decidable.byCases (t0' = t0)
  . apply @Decidable.byCases (t0' = t1)
    . intro eq1 eq2
      rw [eq1] at eq2 ⊢
      rw [eq2]
    . intro diff eq
      rw [eq] at diff ⊢
      simp [(Ne.intro diff).symm]
  . apply @Decidable.byCases (t0' = t1)
    . intro eq diff
      rw [eq] at diff ⊢
      simp [(Ne.intro diff).symm]
    . intro diff1 diff2
      simp [(Ne.intro diff1).symm, (Ne.intro diff2).symm]

@[simp] theorem 𝕎₀.drain_add_self (w: 𝕎₀) (t: 𝕋) (x: NNReal):
  (w.add t x).drain t = w.drain t := by 
  ext t'
  apply @Decidable.byCases (t' = t)
  . intro eq
    simp [eq]
  . intro neq
    simp [(Ne.intro neq).symm]

@[simp] theorem 𝕎₀.drain_sub_self (w: 𝕎₀) (t: 𝕋) (x: NNReal) (h: x ≤ w t):
  (w.sub t x h).drain t = w.drain t := by
  ext t'
  apply @Decidable.byCases (t' = t)
  . intro eq
    simp [eq]
  . intro neq
    simp [(Ne.intro neq).symm]

@[simp] theorem 𝕎₀.drain_add_diff (w: 𝕎₀) (t: 𝕋) (x: NNReal) (t': 𝕋) (hdif: t ≠ t'):
  (w.add t x).drain t' = (w.drain t').add t x := by
  ext t''
  rcases Decidable.em (t''=t), (Decidable.em (t''=t')) with ⟨left|left, right|right⟩
  
  . rw [left] at right
    contradiction
  . rw [left]
    simp [hdif.symm]
  . rw [right]
    simp [hdif, hdif.symm]
  . simp [(Ne.intro left).symm, (Ne.intro right).symm]

@[simp] theorem 𝕎₀.drain_sub_diff (w: 𝕎₀) (t: 𝕋) (x: NNReal) (h: x ≤ w t) (t': 𝕋) (hdif: t ≠ t'):
  (w.sub t x h).drain t' = (w.drain t').sub t x (by simp[h,hdif.symm]) := by   
  ext t''
  rcases Decidable.em (t''=t), (Decidable.em (t''=t')) with ⟨left|left, right|right⟩
  
  . rw [left] at right
    contradiction
  . rw [left]
    simp [hdif.symm]
  . rw [right]
    simp [hdif, hdif.symm]
  . simp [(Ne.intro left).symm, (Ne.intro right).symm]

def 𝕎₀.worth (w: 𝕎₀) (o: 𝕋 → PReal): NNReal :=
  w.sum (λ t x => x*(o t))

theorem Finsupp.update_zero_eq_erase {α β: Type} [DecidableEq α] [Zero β] (f: α →₀ β) (a: α):
  Finsupp.update f a 0 = Finsupp.erase a f := by 
  ext a'
  rcases Decidable.em (a=a') with eq|neq
  . rw [eq]; simp
  . simp [(Ne.intro neq).symm]

theorem 𝕎₀.worth_destruct (w: 𝕎₀) (o: 𝕋 → PReal) (t: 𝕋):
  w.worth o = (w.drain t).worth o + (w t)*(o t) := by 
  unfold worth
  unfold drain
  unfold sub
  simp only [le_refl, tsub_eq_zero_of_le]
  rw [Finsupp.update_zero_eq_erase]
  rw [add_comm]
  have bruh: (w t)*(o t) = (λ t (x: NNReal) => x*(o t)) t (w t) := by simp
  rw [bruh]
  rw [Finsupp.add_sum_erase' w t (λ t (x: NNReal) => x*(o t))]
  simp

/- 
  Symmetric versions of the theorems with "hdif",
  to make their use with simp easier
-/
@[simp] theorem 𝕎₀.get_add_diff' (w: 𝕎₀) (t: 𝕋) (x: NNReal) (t': 𝕋) (hdif: t' ≠ t): (w.add t x) t' = w t' 
  := 𝕎₀.get_add_diff w t x t' hdif.symm

@[simp] theorem 𝕎₀.get_sub_diff' (w: 𝕎₀) (t: 𝕋) (x: NNReal) (h: x ≤ w t) (t': 𝕋) (diff: t' ≠ t):
  (w.sub t x h) t' = w t' := 𝕎₀.get_sub_diff w t x h t' diff.symm

@[simp] theorem 𝕎₀.get_drain_diff' (w: 𝕎₀) (t t': 𝕋) (diff: t' ≠ t):
  (w.drain t) t' = w t' := 𝕎₀.get_drain_diff w t t' diff.symm

@[simp] theorem 𝕎₀.drain_add_diff' (w: 𝕎₀) (t: 𝕋) (x: NNReal) (t': 𝕋) (hdif: t' ≠ t):
  (w.add t x).drain t' = (w.drain t').add t x := 𝕎₀.drain_add_diff w t x t' hdif.symm

@[simp] theorem 𝕎₀.drain_sub_diff' (w: 𝕎₀) (t: 𝕋) (x: NNReal) (h: x ≤ w t) (t': 𝕋) (hdif: t' ≠ t):
  (w.sub t x h).drain t' = (w.drain t').sub t x (by simp[h,hdif.symm]) := 𝕎₀.drain_sub_diff w t x h t' hdif.symm