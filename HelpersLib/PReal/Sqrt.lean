import HelpersLib.PReal.Basic
import Mathlib.Data.Real.Sqrt

namespace PReal

noncomputable def sqrt (x: ℝ>0): ℝ>0 :=
  ⟨Real.sqrt x, by rw [← Real.sqrt_zero]
                   exact (Real.sqrt_lt_sqrt_iff (le_refl 0)).mpr x.2⟩

@[simp]
theorem sqrt_to_real (x: ℝ>0): (x.sqrt: ℝ) = Real.sqrt (x: ℝ) := by rfl

@[simp]
theorem mul_self_sqrt (x: ℝ>0): x.sqrt * x.sqrt = x := by
  rw [← toReal_eq_toReal_iff]
  exact Real.mul_self_sqrt x.2.le
