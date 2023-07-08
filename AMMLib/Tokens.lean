import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Finsupp.Basic
import HelpersLib.PReal.Basic
import HelpersLib.PReal.Subtraction
import HelpersLib.Finsupp2
open BigOperators

structure 𝔸 where
  n: ℕ

structure 𝕋 where
  n: ℕ

instance: DecidableEq 𝔸 := 
  fun a1 a2 => by 
  cases a1; cases a2; simp; infer_instance

instance: DecidableEq 𝕋 := 
  fun a1 a2 => by 
  cases a1; cases a2; simp; infer_instance

abbrev AtomicOracle  := 𝕋 → PReal

def diffmint (t0 t1 t0' t1': 𝕋): Prop :=
  (t0 ≠ t0' ∧ t0 ≠ t1') ∨ (t1 ≠ t0' ∧ t1 ≠ t1')

def samemint (t0 t1 t0' t1': 𝕋): Prop :=
  (t0 = t0' ∧ t1 = t1') ∨ (t0 = t1' ∧ t1 = t0')

instance (t0 t1 t0' t1': 𝕋): Decidable (samemint t0 t1 t0' t1') := 
  by unfold samemint; infer_instance;

instance (t0 t1 t0' t1': 𝕋): Decidable (diffmint t0 t1 t0' t1') := 
  by unfold diffmint; infer_instance;

@[simp] theorem not_diffmint_iff_samemint 
  (t0 t1 t0' t1': 𝕋) (hdif: t0 ≠ t1):
  ¬ diffmint t0 t1 t0' t1' ↔ samemint t0 t1 t0' t1' := by
  unfold diffmint
  unfold samemint
  simp_rw [not_or, not_and_or, not_ne_iff]
  apply Iff.intro

  . intro notdiff
    rcases notdiff with ⟨a|a, b|b⟩
    . rw [a, b] at hdif; contradiction
    . simp [a, b, hdif]
    . simp [a, b, hdif]
    . rw [a, b] at hdif; contradiction
  
  . intro samemint
    rcases samemint with ⟨a,b⟩|⟨a,b⟩ <;> simp [a,b]

@[simp] theorem not_samemint_iff_diffmint
  (t0 t1 t0' t1': 𝕋) (hdif: t0 ≠ t1):
  ¬ samemint t0 t1 t0' t1' ↔ diffmint t0 t1 t0' t1' := by
  have h := (not_diffmint_iff_samemint t0 t1 t0' t1' hdif).not.symm
  simp at h
  exact h

theorem self_samemint (t0 t1: 𝕋):
  samemint t0 t1 t0 t1 := by simp [samemint]

theorem samemint.iff_swap_inner_left (t0 t1 t0' t1': 𝕋):
  samemint t0 t1 t0' t1' ↔ samemint t1 t0 t0' t1' := by 
  unfold samemint
  apply Iff.intro <;> (
    intro h
    rcases h with ⟨a,b⟩|⟨a,b⟩ <;> simp [a,b]
  )

theorem samemint.iff_swap_inner_right (t0 t1 t0' t1': 𝕋):
  samemint t0 t1 t0' t1' ↔ samemint t0 t1 t1' t0' := by 
  unfold samemint
  apply Iff.intro <;> (
    intro h
    rcases h with ⟨a,b⟩|⟨a,b⟩ <;> simp [a,b]
  )

theorem samemint.iff_swap_inner (t0 t1 t0' t1': 𝕋):
  samemint t0 t1 t0' t1' ↔ samemint t1 t0 t1' t0' := by 
  unfold samemint
  apply Iff.intro <;> (
    intro h
    rcases h with ⟨a,b⟩|⟨a,b⟩ <;> simp [a,b]
  )

theorem samemint.iff_swap_outer (t0 t1 t0' t1': 𝕋):
  samemint t0 t1 t0' t1' ↔ samemint t0' t1' t0 t1 := by 
  unfold samemint
  apply Iff.intro <;> (
    intro h
    rcases h with ⟨a,b⟩|⟨a,b⟩ <;> simp [a,b]
  )

theorem diffmint.iff_swap_inner_left (t0 t1 t0' t1': 𝕋):
  diffmint t0 t1 t0' t1' ↔ diffmint t1 t0 t0' t1' := by 
  unfold diffmint
  apply Iff.intro <;> (
    intro h
    rcases h with ⟨a,b⟩|⟨a,b⟩ <;> simp [a,b]
  )

theorem diffmint.iff_swap_inner_right (t0 t1 t0' t1': 𝕋):
  diffmint t0 t1 t0' t1' ↔ diffmint t0 t1 t1' t0' := by 
  unfold diffmint
  apply Iff.intro <;> (
    intro h
    rcases h with ⟨a,b⟩|⟨a,b⟩ <;> simp [a,b]
  )

theorem diffmint.iff_swap_inner (t0 t1 t0' t1': 𝕋):
  diffmint t0 t1 t0' t1' ↔ diffmint t1 t0 t1' t0' := by 
  unfold diffmint
  apply Iff.intro <;> (
    intro h
    rcases h with ⟨a,b⟩|⟨a,b⟩ <;> simp [a,b]
  )

/-
diffmint says: one of the elements of the first pair is different to both elements of the second pair.
does that imply one of the elements of the second pair is different to both elements of the first pair?

(a,b) (c,d)
we have a ≠ b, a ≠ c, a ≠ d, c ≠ d.
assume c = b.
  then, d ≠ b, so d is the one.
assume d = b.
  then, c ≠ b, so c is the one.
-/
theorem diffmint.iff_swap_outer (t0 t1 t0' t1': 𝕋) (hdif1: t0 ≠ t1) (hdif2: t0' ≠ t1'):
  diffmint t0 t1 t0' t1' ↔ diffmint t0' t1' t0 t1 := by 
  unfold diffmint
  apply Iff.intro
  . intro h
    rcases h with ⟨a,b⟩|⟨a,b⟩
    . rcases Decidable.em (t1=t0') with c|c
      . rw [c] at hdif1 ⊢
        simp [a, b, hdif1, b.symm, hdif2.symm]
      . simp [a.symm, (Ne.intro c).symm]
    . rcases Decidable.em (t0=t0') with c|c
      . rw [c] at hdif1 ⊢
        simp [a, b, hdif1, b.symm, hdif2.symm]
      . simp [a.symm, (Ne.intro c).symm]

  . intro h
    rcases h with ⟨a,b⟩|⟨a,b⟩
    . rcases Decidable.em (t1'=t0) with c|c
      . rw [c] at hdif2 ⊢
        simp [a, b, b.symm, hdif1.symm]
      . simp [a.symm, (Ne.intro c).symm]
    . rcases Decidable.em (t0'=t0) with c|c
      . rw [c] at hdif2 ⊢
        simp [a, b, b.symm, hdif1.symm]
      . simp [a.symm, (Ne.intro c).symm]
