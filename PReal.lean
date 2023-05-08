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