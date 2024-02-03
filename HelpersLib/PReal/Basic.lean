import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.NNReal
import Mathlib.Algebra.Order.Positive.Field
import Mathlib.Algebra.Order.Positive.Ring
open NNReal

/- This code is mostly copied and adapted from NNReal. -/

abbrev PReal := { r : ℝ // 0 < r}

notation "ℝ>0" => PReal

namespace PReal

-- Definitions of coercions
@[coe] def toReal : ℝ>0 → ℝ := Subtype.val
instance : Coe ℝ>0 ℝ := ⟨toReal⟩

@[coe] def toNNReal : ℝ>0 → NNReal := λ x => ⟨Subtype.val x, le_of_lt x.2⟩
instance : Coe ℝ>0 NNReal := ⟨toNNReal⟩

-- Simp lemma to put back `n.val` into the normal form given by the coercion.
@[simp]
theorem val_eq_toNNReal (n : ℝ>0) : n.val = n :=
  rfl

theorem toReal_pos (x: ℝ>0): (0:ℝ) < x := x.2

theorem toReal_ne_zero (x: ℝ>0)
: (x: ℝ) ≠ 0 := (ne_of_lt x.toReal_pos).symm

@[simp] theorem toNNRealReal_eq_toNNReal (x: ℝ>0): ((x: ℝ≥0): ℝ) = (x: ℝ) := by rfl

@[simp] theorem toRealPReal_eq_toPReal (x: ℝ>0):
  ⟨(x: ℝ), x.property⟩ = (x: ℝ>0) := by rfl

theorem toNNReal_ne_zero (x: ℝ>0): (x: ℝ≥0) ≠ 0 := by
  have h := x.property
  apply NNReal.ne_iff.mp
  rw [toNNRealReal_eq_toNNReal]
  exact ne_of_gt h

theorem zero_lt_toNNReal (x: ℝ>0): 0 < (x: ℝ≥0) :=
  by exact x.property

@[simp] lemma add_toReal (x y: ℝ>0):
  (((x+y): ℝ>0): ℝ) = (x:ℝ)+(y:ℝ) := by rfl

@[simp] lemma add_toNNReal (x y: ℝ>0):
  (((x+y): ℝ>0): ℝ≥0) = (x:NNReal)+(y:NNReal) := by rfl

@[simp] lemma mul_toReal (x y: ℝ>0):
  (((x*y): ℝ>0): ℝ)= (x:ℝ)*(y:ℝ) := by rfl

@[simp] lemma mul_toNNReal (x y: ℝ>0):
  (((x*y): ℝ>0): ℝ≥0)= (x:NNReal)*(y:NNReal) := by rfl

@[simp] lemma div_toReal (x y: ℝ>0):
  (((x/y): ℝ>0): ℝ)= (x:ℝ)/(y:ℝ) := by rfl

@[simp] lemma div_toNNReal (x y: ℝ>0):
  (((x/y): ℝ>0): ℝ≥0)= (x:NNReal)/(y:NNReal) := by rfl

@[simp] lemma inv_toReal (x: ℝ>0):
  ((x⁻¹): ℝ>0) = (x: ℝ)⁻¹ := by rfl

@[simp] lemma inv_toNNReal (x: ℝ>0):
  ((x⁻¹): ℝ>0) = (x: ℝ≥0)⁻¹ := by rfl

theorem toReal_injective : Function.Injective toReal := Subtype.coe_injective

@[simp] lemma toReal_eq_toReal_iff (x y: ℝ>0):
  (x: ℝ) = (y: ℝ) ↔ x = y := toReal_injective.eq_iff

theorem toNNReal_injective : Function.Injective toNNReal :=
  λ (x y) =>
  by intro h; unfold toNNReal at h;
     rw [← NNReal.coe_eq] at h
     simp at h
     exact h

@[simp] lemma toNNReal_eq_toNNReal_iff (x y: ℝ>0):
  (x: ℝ≥0) = (y: ℝ≥0) ↔ x = y := toNNReal_injective.eq_iff

@[simp] lemma toReal_le_toReal_iff (x y: ℝ>0):
  (x: ℝ) ≤ (y: ℝ) ↔ x ≤ y := by rfl

@[simp] lemma toNNReal_le_toNNReal_iff (x y: ℝ>0):
  (x: ℝ≥0) ≤ (y: ℝ≥0) ↔ x ≤ y := by rfl

@[simp] lemma toReal_lt_toReal_iff (x y: ℝ>0):
  (x: ℝ) < (y: ℝ) ↔ x < y := by rfl

@[simp] lemma toNNReal_lt_toNNReal_iff (x y: ℝ>0):
  (x: ℝ≥0) < (y: ℝ≥0) ↔ x < y := by rfl

@[simp] lemma toReal_cmp (x y: ℝ>0):
  cmp (x: ℝ) (y: ℝ) = cmp x y := by rfl

@[simp] lemma toNNReal_cmp (x y: ℝ>0):
  cmp (x: ℝ≥0) (y: ℝ≥0) = cmp x y := by rfl

theorem add_div'' {α: Type}
  [DivInvMonoid α] [Add α] [RightDistribClass α]
  (a b c: α):
  (a + b) / c = a/c + b/c :=
    by simp_rw [div_eq_mul_inv, add_mul]

@[simp] theorem mk_toReal (x: ℝ) (h: 0 < x):
  ((⟨x, h⟩: ℝ>0): ℝ) = x := by rfl

@[simp] theorem mk_toNNReal (x: ℝ) (h: 0 < x):
  ((⟨x, h⟩: ℝ>0): ℝ≥0) = (x.toNNReal) := by
  rw [← NNReal.coe_eq]
  simp [max_eq_left_of_lt h]
