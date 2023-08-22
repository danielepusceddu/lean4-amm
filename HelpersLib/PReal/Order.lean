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

theorem lt_iff_exists_add' {x y: ℝ+}:
  x < y ↔ ∃ (z: ℝ+), y = x+z := by
    sorry

theorem sub_sub' (x y z: ℝ+) (h: y+z < x):
  x.sub (y+z) h = (x.sub y (by sorry)).sub z (by sorry) := by
  unfold sub
  rw [← toReal_eq_toReal_iff]
  simp [sub_sub]

theorem lt_imp_sub_lt (x y z: ℝ+) (h: z < x) (h': x < y):
  x.sub z h < y := by sorry

theorem x_sub_y_lt_x_sub_z_iff (x y z: ℝ+) (h: z < x) (h': y < x):
  x.sub y h' < x.sub z h ↔ z < y := by 
  simp_rw [← toReal_lt_toReal_iff]
  simp [-toReal_lt_toReal_iff]