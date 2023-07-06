import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Finsupp.Basic
import HelpersLib.PReal
import HelpersLib.Finsupp2
open BigOperators

structure 𝔸 where
  n: ℕ

structure 𝕋₀ where
  n: ℕ

instance: DecidableEq 𝔸 := 
  fun a1 a2 => by 
  cases a1; cases a2; simp; infer_instance

instance: DecidableEq 𝕋₀ := 
  fun a1 a2 => by 
  cases a1; cases a2; simp; infer_instance

abbrev AtomicOracle  := 𝕋₀ → PReal


def diffpair (t0 t1 t0' t1': 𝕋₀): Prop :=
  (t0 ≠ t0' ∧ t0 ≠ t1') ∨ (t1 ≠ t0' ∧ t1 ≠ t1')

theorem self_not_diffpair (t0 t1: 𝕋₀):
  ¬ diffpair t0 t1 t0 t1 := by simp [diffpair]

theorem diffpair.swap_inner_left {t0 t1 t0' t1': 𝕋₀} (h: diffpair t0 t1 t0' t1'):
  diffpair t1 t0 t0' t1' := by sorry

theorem diffpair.swap_inner_right {t0 t1 t0' t1': 𝕋₀} (h: diffpair t0 t1 t0' t1'):
  diffpair t0 t1 t1' t0' := by sorry

theorem diffpair.swap_inner {t0 t1 t0' t1': 𝕋₀} (h: diffpair t0 t1 t0' t1'):
  diffpair t1 t0 t1' t0' := by sorry

  /-
  ```

¬(t0 ≠ t0' ∧ t0 ≠ t1' ∨ t1 ≠ t0' ∧ t1 ≠ t1')    ↔
¬(t0 ≠ t0' ∧ t0 ≠ t1') ∧ ¬(t1 ≠ t0' ∧ t1 ≠ t1') ↔ 
(t0 = t0' ∨ t0 = t1') ∧ (t1 = t0' ∨ t1 = t1')   ↔

..... ↔

(t0 = t0' ∧ t1 = t1') ∨ (t0 = t1' ∧ t1 = t0')

  ```
  -/
theorem not_diffpair {t0 t1 t0' t1': 𝕋₀} (dif1: t0 ≠ t1) (h: ¬ diffpair t0 t1 t0' t1'):
  (t0 = t0' ∧ t1 = t1') ∨ (t0 = t1' ∧ t1 = t0') := by
  
  unfold diffpair at h
  simp_rw [not_or, not_and_or, not_ne_iff] at h

  rcases h with ⟨a|a, b|b⟩
  . rw [a, b] at dif1; contradiction
  . simp [a, b, dif1]
  . simp [a, b, dif1]
  . rw [a, b] at dif1; contradiction

instance (t0 t1 t0' t1': 𝕋₀): Decidable (diffpair t0 t1 t0' t1') := 
  by sorry