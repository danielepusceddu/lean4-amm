import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Sym.Sym2
import Mathlib.Algebra.BigOperators.Finsupp
import HelpersLib.NNReal
import HelpersLib.Prod
import HelpersLib.PReal.Basic
import HelpersLib.PReal.Subtraction
import HelpersLib.Finsupp2
import AMMLib.State.Tokens
import Mathlib.Tactic.LibrarySearch
open NNReal

-- Atomic token wallet
abbrev W₀ := T →₀ ℝ≥0

noncomputable def W₀.add (w: W₀) (t: T) (x: ℝ≥0): W₀ :=
  w.update t ((w t) + x)

@[simp] theorem W₀.get_add_self (w: W₀) (t: T) (x: ℝ≥0):
  (w.add t x) t = w t + x := by simp [W₀.add]

@[simp] theorem W₀.get_add_diff (w: W₀) (t: T) (x: ℝ≥0) (t': T) (hdif: t ≠ t'):
  (w.add t x) t' = w t' := by simp [W₀.add, hdif.symm]

noncomputable def W₀.sub (w: W₀) (t: T) (x: ℝ≥0) (_: x ≤ w t): W₀ :=
  w.update t ((w t) - x)

@[simp] theorem W₀.get_sub_self (w: W₀) (t: T) (x: ℝ≥0) (h: x ≤ w t):
  (w.sub t x h) t = w t - x := by simp [W₀.sub]

@[simp] theorem W₀.get_sub_diff (w: W₀) (t: T) (x: ℝ≥0) (h: x ≤ w t) (t': T) (diff: t ≠ t'):
  (w.sub t x h) t' = w t' := by simp [W₀.sub, diff.symm]

noncomputable def W₀.drain (w: W₀) (t: T): W₀ :=
  w.sub t (w t) (by simp)

@[simp] theorem W₀.get_drain_self (w: W₀) (t: T):
  (w.drain t) t = 0 := by simp [W₀.drain]

@[simp] theorem W₀.get_drain_diff (w: W₀) (t t': T) (diff: t ≠ t'):
  (w.drain t) t' = w t' := by simp [W₀.drain, diff]

theorem W₀.drain_comm (w: W₀) (t0 t1: T):
  (w.drain t1).drain t0 = (w.drain t0).drain t1 := by
  ext t0'
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

@[simp] theorem W₀.drain_add_self (w: W₀) (t: T) (x: ℝ≥0):
  (w.add t x).drain t = w.drain t := by
  ext t'
  apply @Decidable.byCases (t' = t)
  . intro eq
    simp [eq]
  . intro neq
    simp [(Ne.intro neq).symm]

@[simp] theorem W₀.drain_sub_self (w: W₀) (t: T) (x: ℝ≥0) (h: x ≤ w t):
  (w.sub t x h).drain t = w.drain t := by
  ext t'
  apply @Decidable.byCases (t' = t)
  . intro eq
    simp [eq]
  . intro neq
    simp [(Ne.intro neq).symm]

@[simp] theorem W₀.drain_add_diff (w: W₀) (t: T) (x: ℝ≥0) (t': T) (hdif: t ≠ t'):
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

@[simp] theorem W₀.drain_sub_diff (w: W₀) (t: T) (x: ℝ≥0) (h: x ≤ w t) (t': T) (hdif: t ≠ t'):
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

noncomputable def W₀.worth (w: W₀) (o: T → ℝ>0): ℝ≥0 :=
  w.sum (λ t x => x*(o t))

theorem Finsupp.update_zero_eq_erase {α β: Type} [DecidableEq α] [Zero β] (f: α →₀ β) (a: α):
  Finsupp.update f a 0 = Finsupp.erase a f := by
  ext a'
  rcases Decidable.em (a=a') with eq|neq
  . rw [eq]; simp
  . simp [(Ne.intro neq).symm]

theorem W₀.worth_destruct (w: W₀) (o: T → ℝ>0) (t: T):
  w.worth o = (w.drain t).worth o + (w t)*(o t) := by
  unfold worth
  unfold drain
  unfold sub
  simp only [le_refl, tsub_eq_zero_of_le]
  rw [Finsupp.update_zero_eq_erase]
  rw [add_comm]
  have invert_app:
    (w t)*(o t) = (λ t (x: ℝ≥0) => x*(o t)) t (w t) :=
    by simp
  rw [invert_app]
  rw [Finsupp.add_sum_erase' w t (λ t (x: ℝ≥0) => x*(o t))]
  simp

/-
  Symmetric versions of the theorems with "hdif",
  to make their use with simp easier
-/
@[simp] theorem W₀.get_add_diff' (w: W₀) (t: T) (x: ℝ≥0) (t': T) (hdif: t' ≠ t): (w.add t x) t' = w t'
  := W₀.get_add_diff w t x t' hdif.symm

@[simp] theorem W₀.get_sub_diff' (w: W₀) (t: T) (x: ℝ≥0) (h: x ≤ w t) (t': T) (diff: t' ≠ t):
  (w.sub t x h) t' = w t' := W₀.get_sub_diff w t x h t' diff.symm

@[simp] theorem W₀.get_drain_diff' (w: W₀) (t t': T) (diff: t' ≠ t):
  (w.drain t) t' = w t' := W₀.get_drain_diff w t t' diff.symm

@[simp] theorem W₀.drain_add_diff' (w: W₀) (t: T) (x: ℝ≥0) (t': T) (hdif: t' ≠ t):
  (w.add t x).drain t' = (w.drain t').add t x := W₀.drain_add_diff w t x t' hdif.symm

@[simp] theorem W₀.drain_sub_diff' (w: W₀) (t: T) (x: ℝ≥0) (h: x ≤ w t) (t': T) (hdif: t' ≠ t):
  (w.sub t x h).drain t' = (w.drain t').sub t x (by simp[h,hdif.symm]) := W₀.drain_sub_diff w t x h t' hdif.symm
