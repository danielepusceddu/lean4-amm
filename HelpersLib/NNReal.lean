import Mathlib.Data.Real.NNReal

lemma NNReal.neq_zero_imp_gt {x: NNReal} (h: x ≠ 0)
: 0 < x := Ne.lt_of_le' h x.property

theorem NNReal.pos_imp_add_pos 
(x y: NNReal) (h: x ≠ 0): x + y ≠ 0 := by
field_simp
intro contra; contradiction