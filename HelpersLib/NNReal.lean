import Mathlib.Data.Real.NNReal
import HelpersLib.PReal.Basic
open NNReal

lemma NNReal.neq_zero_imp_gt {x: ℝ≥0} (h: x ≠ 0)
: 0 < x := Ne.lt_of_le' h x.property

theorem NNReal.pos_imp_add_pos
(x y: ℝ≥0) (h: x ≠ 0): x + y ≠ 0 := by
field_simp
intro contra; contradiction

def NNReal.toPReal (x: ℝ≥0) (h: 0 < x): ℝ>0 :=
  ⟨
    x, h
  ⟩

def NNReal.toPReal' (x: ℝ≥0) (h: x ≠ 0): ℝ>0 :=
  ⟨
    x, neq_zero_imp_gt h
  ⟩

@[simp] theorem NNReal_toPReal_toNNReal_eq_self (x: ℝ≥0) (h: 0 < x):
  x.toPReal h = x := by rfl
