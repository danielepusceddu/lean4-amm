import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.NNReal
import Mathlib.Algebra.Order.Positive.Field
import Mathlib.Algebra.Order.Positive.Ring

/- This code is mostly copied and adapted from NNReal. -/

def PReal := { r : ℝ // 0 < r} deriving One, Add, Mul

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

noncomputable instance: Inv ℝ+ := Positive.Subtype.inv
noncomputable instance: LinearOrderedCancelCommMonoid ℝ+ := Positive.linearOrderedCancelCommMonoid

noncomputable instance: Div ℝ+ := ⟨fun (x y:ℝ+) => 
  ⟨x/y, div_pos x.2 y.2⟩⟩

def sub (x y: ℝ+) (h: y < x): ℝ+ :=
  ⟨(x:ℝ)-(y:ℝ), by aesop⟩

theorem eq_iff (x y: ℝ+): 
  (x.toReal = y.toReal) ↔ (x = y) := Subtype.ext_iff.symm

lemma coe_add (x y: ℝ+):
  (((x+y): ℝ+): ℝ) = (x:ℝ)+(y:ℝ) := by rfl

lemma coe_mul (x y: ℝ+):
  (((x*y): ℝ+): ℝ)= (x:ℝ)*(y:ℝ) := by rfl

lemma coe_sub (x y: ℝ+) (gt: y < x):
  (((x.sub y gt): ℝ+): ℝ) = (x: ℝ) - (y: ℝ) := by rfl

lemma coe_div (x y: ℝ+):
  (((x/y): ℝ+): ℝ)= (x:ℝ)/(y:ℝ) := by rfl

lemma coe_le (x y: ℝ+):
  x ≤ y ↔ (x: ℝ) ≤ (y: ℝ) := by rfl

lemma coe_lt (x y: ℝ+):
  x < y ↔ (x: ℝ) < (y: ℝ) := by rfl

lemma coe_inv (x: ℝ+):
  ((x⁻¹): ℝ+) = (x: ℝ)⁻¹ := by rfl

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

noncomputable instance: Group ℝ+ where
  mul_left_inv := by 
    intro x
    simp [coe_eq', coe_mul, coe_inv, x.coe_ne_zero]
    rfl

noncomputable instance: CommGroup ℝ+ where
  mul_comm := by
    intro x y
    simp [PReal.coe_eq', coe_mul, mul_comm]

instance: RightDistribClass ℝ+ where
  right_distrib := by
    intro x y z
    simp only [coe_eq', coe_mul, coe_add]
    exact right_distrib (x: ℝ) y z

noncomputable instance: OrderedCommGroup ℝ+ where
  mul_le_mul_left := by 
    intro a b
    intro hle
    intro c
    rw [mul_le_mul_iff_left]
    exact hle

theorem add_div'' {α: Type} 
  [DivInvMonoid α] [Add α] [RightDistribClass α] 
  (a b c: α):
  (a + b) / c = a/c + b/c := 
    by simp_rw [div_eq_mul_inv, add_mul]

theorem lt_add_right (x y: ℝ+):
  x < x+y := by
  simp only [coe_lt, coe_add]
  conv => lhs; rw [← zero_add (x: ℝ)]; rfl
  rw [add_comm (x: ℝ)]
  exact add_lt_add_right y.coe_pos x

theorem gt_add_right (x y: ℝ+):
  x+y > x := by
  simp only [gt_iff_lt]
  exact lt_add_right x y

theorem div_lt_add_denum (x y z: ℝ+):
  x/(y+z) < x/y := by
  simp only [div_eq_mul_inv, mul_lt_mul_iff_left]
  apply inv_lt_inv'
  exact lt_add_right y z
