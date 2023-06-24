import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.NNReal
import Mathlib.Algebra.Order.Positive.Field
import Mathlib.Algebra.Order.Positive.Ring

/- This code is mostly copied and adapted from NNReal. -/

abbrev PReal := { r : ℝ // 0 < r}

notation "ℝ+" => PReal

namespace PReal

@[coe] def toReal : ℝ+ → ℝ := Subtype.val
instance : Coe ℝ+ ℝ := ⟨toReal⟩

@[coe] def toNNReal : ℝ+ → NNReal := λ x => ⟨Subtype.val x, le_of_lt x.2⟩
instance : Coe ℝ+ NNReal := ⟨toNNReal⟩

-- Simp lemma to put back `n.val` into the normal form given by the coercion.
@[simp]
theorem val_eq_coe (n : ℝ+) : n.val = n :=
  rfl

theorem coe_pos (x: ℝ+): (0:ℝ) < x := x.2

theorem coe_ne_zero (x: ℝ+)
: (x: ℝ) ≠ 0 := (ne_of_lt x.coe_pos).symm

@[simp] theorem coe_eq (x: ℝ+): ((x: NNReal): ℝ) = (x: ℝ) := by rfl

theorem coe_nnreal_pos (x: ℝ+): (x: NNReal) ≠ 0 := by
  have h := x.property
  apply NNReal.ne_iff.mp
  rw [coe_eq]
  exact ne_of_gt h

def sub (x y: ℝ+) (h: y < x): ℝ+ :=
  ⟨(x:ℝ)-(y:ℝ), by aesop⟩

theorem eq_iff (x y: ℝ+): 
  (x.toReal = y.toReal) ↔ (x = y) := Subtype.ext_iff.symm

lemma coe_add (x y: ℝ+):
  (((x+y): ℝ+): ℝ) = (x:ℝ)+(y:ℝ) := by rfl

lemma coe_mul (x y: ℝ+):
  (((x*y): ℝ+): ℝ)= (x:ℝ)*(y:ℝ) := by rfl

lemma coe_mul' (x y: ℝ+):
  (((x*y): ℝ+): NNReal)= (x:NNReal)*(y:NNReal) := by rfl

lemma coe_sub (x y: ℝ+) (gt: y < x):
  (((x.sub y gt): ℝ+): ℝ) = (x: ℝ) - (y: ℝ) := by rfl

lemma coe_sub' (x y: ℝ+) (gt: y < x):
  (((x.sub y gt): ℝ+): NNReal) = (x: NNReal) - (y: NNReal) := by sorry

lemma coe_div (x y: ℝ+):
  (((x/y): ℝ+): ℝ)= (x:ℝ)/(y:ℝ) := by rfl

lemma coe_le (x y: ℝ+):
  x ≤ y ↔ (x: ℝ) ≤ (y: ℝ) := by rfl

lemma coe_lt (x y: ℝ+):
  x < y ↔ (x: ℝ) < (y: ℝ) := by rfl

lemma coe_lt' (x y: ℝ+):
  x < y ↔ (x: NNReal) < (y: NNReal) := by rfl

lemma coe_inv (x: ℝ+):
  ((x⁻¹): ℝ+) = (x: ℝ)⁻¹ := Positive.coe_inv x

lemma coe_eq' (x y: ℝ+):
  x = y ↔ (x: ℝ) = (y: ℝ) := by 
  apply Iff.intro
  . intro heq
    rw [heq]
  . intro heq
    rw [← x.val_eq_coe] at heq
    rw [← y.val_eq_coe] at heq
    rcases x with ⟨xval,xprop⟩ 
    rcases y with ⟨yval,yprop⟩ 
    simp at heq
    simp [heq]

lemma coe_cmp (x y: ℝ+):
  cmp (x: ℝ) (y: ℝ) = cmp x y := by rfl

theorem add_div'' {α: Type} 
  [DivInvMonoid α] [Add α] [RightDistribClass α] 
  (a b c: α):
  (a + b) / c = a/c + b/c := 
    by simp_rw [div_eq_mul_inv, add_mul]


/-
CovariantClass { x // 0 < x } { x // 0 < x } (fun x x_1 => x + x_1) fun x x_1 => x < x_1

if x < x1, then y+x < y+x1
-/
theorem lt_add_right (x y: ℝ+):
  x < x+y := by
  simp only [coe_lt, coe_add]
  conv => lhs; rw [← zero_add (x: ℝ)]; rfl
  rw [add_comm (x: ℝ)]
  exact add_lt_add_right y.coe_pos x

theorem lt_add_left (x y: ℝ+):
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

theorem lt_iff_exists_add
{x y: ℝ+} (h: x < y):
∃ (z: ℝ+), y = x+z := by
  exists (y.sub x h)
  rw [coe_eq', coe_add, coe_sub]
  simp