import HelpersLib.PReal.Basic

namespace PReal
open NNReal

def sub (x y: ℝ>0) (h: y < x): ℝ>0 :=
  ⟨(x:ℝ)-(y:ℝ), by aesop⟩

@[simp] lemma sub_toReal (x y: ℝ>0) (gt: y < x):
  (((x.sub y gt): ℝ>0): ℝ) = (x: ℝ) - (y: ℝ) := by rfl

@[simp] lemma sub_toNNReal (x y: ℝ>0) (gt: y < x):
  (((x.sub y gt): ℝ>0): ℝ≥0) = (x: ℝ≥0) - (y: ℝ≥0) := by
  unfold sub
  simp [NNReal.sub_def]

@[simp] theorem sub_y_add_y (x y: ℝ>0) (h: y < x):
  x.sub y h + y = x := by
  unfold sub
  rw [← toReal_eq_toReal_iff]
  simp

@[simp] theorem add_y_sub_y (x y: ℝ>0) (h: y < x):
  y + x.sub y h = x := by
  rw [add_comm]
  exact sub_y_add_y x y h

theorem mul_sub' (x y z: ℝ>0) (h: z < y):
  x*(y.sub z h) = (x*y).sub (x*z) (by simp [h]) := by
    rw [← toReal_eq_toReal_iff]
    simp [mul_sub]

theorem sub_mul' (x y z: ℝ>0) (h: z < y):
  (y.sub z h)*x = (y*x).sub (z*x) (by simp [h]) := by
    simp_rw [mul_comm]
    exact mul_sub' x y z h

theorem div_sub_div_same' (x y z: ℝ>0) (h: y < x):
  (x/z).sub (y/z) (by simp [h]) = (x.sub y h)/z := by
    rw [← toReal_eq_toReal_iff]
    simp [div_sub_div_same (x.toReal) y z]
