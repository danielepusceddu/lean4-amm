import HelpersLib.PReal.Basic
import HelpersLib.PReal.Subtraction

namespace PReal

@[simp] theorem lt_add_right (x y: ℝ+):
  x < x+y := by
  rw [← toReal_lt_toReal_iff]
  simp [y.toReal_pos]

@[simp] theorem lt_add_left (x y: ℝ+):
  x < y+x := by
  rw [add_comm y x]
  exact lt_add_right x y

theorem gt_add_right (x y: ℝ+):
  x+y > x := by
  simp only [gt_iff_lt]
  exact lt_add_right x y

theorem div_lt_add_denum (x y z: ℝ+):
  x/(y+z) < x/y := by
  simp only [div_eq_mul_inv, mul_lt_mul_iff_left]
  apply inv_lt_inv'
  exact lt_add_right y z

theorem lt_iff_exists_add {x y: ℝ+} (h: x < y):
  ∃ (z: ℝ+), y = x+z := by
    exists (y.sub x h)
    rw [← toReal_eq_toReal_iff]
    simp