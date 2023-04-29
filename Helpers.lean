import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LibrarySearch

def GT.gt.ne (x y: ℝ) (h: x > y): x ≠ y
  := Ne.symm (LT.lt.ne (GT.gt.lt h))

theorem mul_inv_self_R (x: ℝ) (h: x ≠ 0): x*x⁻¹ = 1 := by
  rewrite [← div_eq_mul_inv]
  rewrite [div_self]
  rfl
  apply h

theorem sub_eq_add_neg' : ∀ (x y: ℝ), x - y = x + -y := by
  intro x y
  change (x + -y = x + -y) 
  rfl

theorem pos_of_nonneg_neq_zero (x: ℝ) (h1: x ≠ 0) (h2: 0 ≤ x): 0 < x :=
  by exact Ne.lt_of_le (id (Ne.symm h1)) h2