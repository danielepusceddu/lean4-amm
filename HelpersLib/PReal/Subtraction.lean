import HelpersLib.PReal.Basic

namespace PReal

def sub (x y: ℝ+) (h: y < x): ℝ+ :=
  ⟨(x:ℝ)-(y:ℝ), by aesop⟩

@[simp] lemma sub_toReal (x y: ℝ+) (gt: y < x):
  (((x.sub y gt): ℝ+): ℝ) = (x: ℝ) - (y: ℝ) := by rfl

@[simp] lemma sub_toNNReal (x y: ℝ+) (gt: y < x):
  (((x.sub y gt): ℝ+): NNReal) = (x: NNReal) - (y: NNReal) := by
  unfold sub
  simp [NNReal.sub_def]

@[simp] theorem sub_y_add_y (x y: ℝ+) (h: y < x):
  x.sub y h + y = x := by
  unfold sub
  rw [← toReal_eq_toReal_iff]
  simp

@[simp] theorem add_y_sub_y (x y: ℝ+) (h: y < x):
  y + x.sub y h = x := by
  rw [add_comm]
  exact sub_y_add_y x y h