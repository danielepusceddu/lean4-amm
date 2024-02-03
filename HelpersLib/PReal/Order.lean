import HelpersLib.PReal.Basic
import HelpersLib.PReal.Subtraction

namespace PReal

@[simp] theorem lt_add_right (x y: ℝ>0):
  x < x+y := by
  rw [← toReal_lt_toReal_iff]
  simp [y.toReal_pos]

@[simp] theorem lt_add_left (x y: ℝ>0):
  x < y+x := by
  rw [add_comm y x]
  exact lt_add_right x y

theorem gt_add_right (x y: ℝ>0):
  x+y > x := by
  simp only [gt_iff_lt]
  exact lt_add_right x y

theorem div_lt_add_denum (x y z: ℝ>0):
  x/(y+z) < x/y := by
  simp only [div_eq_mul_inv, mul_lt_mul_iff_left]
  apply inv_lt_inv'
  exact lt_add_right y z

theorem lt_iff_exists_add {x y: ℝ>0} (h: x < y):
  ∃ (z: ℝ>0), y = x+z := by
    exists (y.sub x h)
    rw [← toReal_eq_toReal_iff]
    simp

theorem lt_iff_exists_add' {x y: ℝ>0}:
  x < y ↔ ∃ (z: ℝ>0), y = x+z := by
    apply Iff.intro
    . intro lt
      exists y.sub x lt
      rw [add_y_sub_y]
    . intro ⟨z, hz⟩
      rw [hz]
      exact lt_add_right _ _

-- x - (y+z) = (x - y) - z
theorem sub_sub' (x y z: ℝ>0) (h: y+z < x):
  x.sub (y+z) h = (x.sub y (by calc y < y + z := by simp
                                    _ < x := h)).sub z (
    by rw [← toReal_lt_toReal_iff] at h ⊢
       simp at h
       simp [h]
       rw [lt_sub_iff_add_lt']
       exact h
  ) := by
  unfold sub
  rw [← toReal_eq_toReal_iff]
  simp [sub_sub]

theorem lt_imp_sub_lt (x y z: ℝ>0) (h: z < x) (h': x < y):
  x.sub z h < y := by
  calc x.sub z h < x.sub z h + z := lt_add_right _ _
       _         = x             := sub_y_add_y _ _ _
       _         < y             := h'

theorem x_sub_y_lt_x_sub_z_iff (x y z: ℝ>0) (h: z < x) (h': y < x):
  x.sub y h' < x.sub z h ↔ z < y := by
  simp_rw [← toReal_lt_toReal_iff]
  simp [-toReal_lt_toReal_iff]

@[simp] theorem add_sub (x y: ℝ>0):
  (x+y).sub y (by simp) = x := by
  rw [← toReal_eq_toReal_iff]
  simp

theorem sub_lt_iff (x y z: ℝ>0) (h: y<x):
  x.sub y h < z ↔ x < z+y := by
  simp_rw [← toReal_lt_toReal_iff]
  simp [sub_lt_iff_lt_add]

theorem sub_sub'' (x y z: ℝ>0) (h1: z < y) (h2: y.sub z h1 < x): -- x - (y - z) = x - y + z = x + z - y
  x.sub (y.sub z h1) h2 = (x+z).sub y ((sub_lt_iff _ _ _ _).mp h2) := by
  rw [← toReal_eq_toReal_iff]
  simp [sub_sub_eq_add_sub]

@[simp]
theorem sub_of_add (x y: ℝ>0):
  (x+y).sub y (by simp) = x := by
  rw [← toReal_eq_toReal_iff]
  simp
